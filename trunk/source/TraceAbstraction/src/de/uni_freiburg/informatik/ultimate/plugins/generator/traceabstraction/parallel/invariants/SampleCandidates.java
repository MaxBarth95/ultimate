/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Reachable states at the loop heads of the program, and the candidate invariants they suggest: the linear equalities
 * of their affine hull, the bounds of each variable and the orderings between two variables. Only integer variables.
 * <p>
 * With relations enabled, also: per pair of variables the facets of the convex hull of the projected states (e.g.
 * {@code x <= 3i} for states where x grows by 1 or 3 with i) and the octagon bounds {@code a + b} and {@code a - b};
 * per variable the congruence {@code v mod m = r} with m the greatest common divisor of the differences of its values.
 * <p>
 * A state may give values to only some variables, e.g. one taken from an interpolant that fixes them. The candidates
 * are computed per set of variables, from every state that gives a value to all of them.
 * <p>
 * The candidates are guesses: most hold on the states seen so far only. The supplier publishes only what it proves to
 * be inductive. Only used by the thread of the {@link InvariantSupplier}.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
final class SampleCandidates {

	/** How many states are kept per location; beyond that new ones are dropped. */
	private static final int MAX_POINTS = 64;
	/** How many candidates one call of {@link #candidates} proposes at most. */
	private static final int MAX_CANDIDATES = 48;
	/** Equalities with more variables are dropped: they are rarely invariants and often only fit the states seen. */
	private static final int MAX_SUPPORT = 3;
	/** Orderings are proposed between the first that many variables that take more than one value. */
	private static final int MAX_ORDERED_VARIABLES = 8;
	/** Sets of variables with more variables than this get no affine hull, which would be costly and overfitted. */
	private static final int MAX_HULL_DIMENSION = 32;
	/** Facets with a larger coefficient are dropped: they rarely are invariants and often only fit the states seen. */
	private static final int MAX_FACET_COEFFICIENT = 16;
	/** Congruences need at least that many states, fewer have common divisors by chance. */
	private static final int MIN_CONGRUENCE_POINTS = 4;
	/** The largest modulus of a congruence. */
	private static final int MAX_MODULUS = 64;

	private final Script mScript;
	private final boolean mRelations;
	private final Map<IcfgLocation, Set<Map<TermVariable, Rational>>> mPoints = new HashMap<>();
	private final Set<IcfgLocation> mChanged = new LinkedHashSet<>();
	private final Map<IcfgLocation, Set<Term>> mProposed = new HashMap<>();

	/**
	 * @param relations
	 *            whether to also propose hull facets, octagon bounds and congruences
	 */
	SampleCandidates(final Script script, final boolean relations) {
		mScript = script;
		mRelations = relations;
	}

	/**
	 * @param point
	 *            values of integer variables, at least one
	 * @return whether the point is new
	 */
	boolean add(final IcfgLocation location, final Map<TermVariable, Rational> point) {
		if (point.isEmpty()) {
			return false;
		}
		final Set<Map<TermVariable, Rational>> points = mPoints.computeIfAbsent(location, x -> new LinkedHashSet<>());
		if (points.size() >= MAX_POINTS || !points.add(Map.copyOf(point))) {
			return false;
		}
		mChanged.add(location);
		return true;
	}

	/** @return the locations that got new points since the last call */
	Set<IcfgLocation> takeChanged() {
		final Set<IcfgLocation> result = new LinkedHashSet<>(mChanged);
		mChanged.clear();
		return result;
	}

	int count(final IcfgLocation location) {
		return mPoints.getOrDefault(location, Set.of()).size();
	}

	int count() {
		return mPoints.values().stream().mapToInt(Set::size).sum();
	}

	int locations() {
		return mPoints.size();
	}

	/**
	 * @return the candidate invariants of {@code location} not proposed before, most promising first: equalities,
	 *         congruences, lower bounds, orderings, hull facets, upper bounds, octagon bounds
	 */
	Set<Term> candidates(final IcfgLocation location) {
		final List<Map<TermVariable, Rational>> points = new ArrayList<>(mPoints.getOrDefault(location, Set.of()));
		final Set<Term> equalities = new LinkedHashSet<>();
		final Set<Term> congruences = new LinkedHashSet<>();
		final Set<Term> lower = new LinkedHashSet<>();
		final Set<Term> orderings = new LinkedHashSet<>();
		final Set<Term> facets = new LinkedHashSet<>();
		final Set<Term> upper = new LinkedHashSet<>();
		final Set<Term> octagons = new LinkedHashSet<>();
		final Set<Set<TermVariable>> variableSets = new LinkedHashSet<>();
		for (final Map<TermVariable, Rational> point : points) {
			variableSets.add(point.keySet());
		}
		for (final Set<TermVariable> variableSet : variableSets) {
			final List<TermVariable> variables = new ArrayList<>(variableSet);
			variables.sort(Comparator.comparing(TermVariable::getName));
			final List<Rational[]> projected = new ArrayList<>();
			for (final Map<TermVariable, Rational> point : points) {
				if (point.keySet().containsAll(variableSet)) {
					projected.add(variables.stream().map(point::get).toArray(Rational[]::new));
				}
			}
			addEqualities(variables, projected, equalities);
			addBoundsAndOrderings(variables, projected, lower, orderings, upper);
			if (mRelations) {
				addCongruences(variables, projected, congruences);
				addFacetsAndOctagons(variables, projected, facets, octagons);
			}
		}
		// What was proposed before is known to the supplier already, so the limit only counts new candidates.
		final Set<Term> proposed = mProposed.computeIfAbsent(location, x -> new HashSet<>());
		final Set<Term> result = new LinkedHashSet<>();
		for (final Set<Term> kind : List.of(equalities, congruences, lower, orderings, facets, upper, octagons)) {
			for (final Term candidate : kind) {
				if (result.size() >= MAX_CANDIDATES) {
					return result;
				}
				if (proposed.add(candidate)) {
					result.add(candidate);
				}
			}
		}
		return result;
	}

	/** Proposes {@code v mod m = r} for every variable whose values differ by multiples of some {@code m > 1}. */
	private void addCongruences(final List<TermVariable> variables, final List<Rational[]> points,
			final Set<Term> congruences) {
		if (points.size() < MIN_CONGRUENCE_POINTS) {
			return;
		}
		for (int i = 0; i < variables.size(); i++) {
			final BigInteger first = points.get(0)[i].numerator();
			BigInteger gcd = BigInteger.ZERO;
			for (final Rational[] point : points) {
				gcd = gcd.gcd(point[i].numerator().subtract(first));
			}
			if (gcd.compareTo(BigInteger.ONE) <= 0 || gcd.compareTo(BigInteger.valueOf(MAX_MODULUS)) > 0) {
				continue;
			}
			final TermVariable variable = variables.get(i);
			final Term modulus = constant(Rational.valueOf(gcd, BigInteger.ONE), variable.getSort());
			final Term remainder = constant(Rational.valueOf(first.mod(gcd), BigInteger.ONE), variable.getSort());
			congruences.add(relation(RelationSymbol.EQ, SmtUtils.mod(mScript, variable, modulus), remainder));
		}
	}

	/**
	 * Proposes, for every pair of variables that take several values, the facets of the convex hull of the states
	 * projected to the pair that are not parallel to an axis, and the bounds of their sum and difference.
	 */
	private void addFacetsAndOctagons(final List<TermVariable> variables, final List<Rational[]> points,
			final Set<Term> facets, final Set<Term> octagons) {
		final List<Integer> varying = new ArrayList<>();
		for (int i = 0; i < variables.size() && varying.size() < MAX_ORDERED_VARIABLES; i++) {
			final int index = i;
			if (points.stream().map(p -> p[index]).distinct().count() > 1) {
				varying.add(i);
			}
		}
		for (int a = 0; a < varying.size(); a++) {
			for (int b = a + 1; b < varying.size(); b++) {
				final int i = varying.get(a);
				final int j = varying.get(b);
				final TermVariable x = variables.get(i);
				final TermVariable y = variables.get(j);
				final Set<List<Rational>> distinct = new LinkedHashSet<>();
				for (final Rational[] point : points) {
					distinct.add(List.of(point[i], point[j]));
				}
				addFacets(x, y, convexHull(new ArrayList<>(distinct)), facets);
				Rational minSum = null;
				Rational maxSum = null;
				Rational minDifference = null;
				Rational maxDifference = null;
				for (final List<Rational> point : distinct) {
					final Rational sum = point.get(0).add(point.get(1));
					final Rational difference = point.get(0).sub(point.get(1));
					minSum = minSum == null || sum.compareTo(minSum) < 0 ? sum : minSum;
					maxSum = maxSum == null || sum.compareTo(maxSum) > 0 ? sum : maxSum;
					minDifference = minDifference == null || difference.compareTo(minDifference) < 0 ? difference
							: minDifference;
					maxDifference = maxDifference == null || difference.compareTo(maxDifference) > 0 ? difference
							: maxDifference;
				}
				final Term sum = SmtUtils.sum(mScript, x.getSort(), x, y);
				final Term difference = SmtUtils.sum(mScript, x.getSort(), x, SmtUtils.mul(mScript, Rational.MONE, y));
				// A constant sum or difference is an equality of the affine hull.
				if (!minSum.equals(maxSum)) {
					octagons.add(relation(RelationSymbol.LEQ, sum, constant(maxSum, x.getSort())));
					octagons.add(relation(RelationSymbol.GEQ, sum, constant(minSum, x.getSort())));
				}
				if (!minDifference.equals(maxDifference)) {
					octagons.add(relation(RelationSymbol.LEQ, difference, constant(maxDifference, x.getSort())));
					octagons.add(relation(RelationSymbol.GEQ, difference, constant(minDifference, x.getSort())));
				}
			}
		}
	}

	/**
	 * For every edge from p to q of a counterclockwise hull, every point r is on its left:
	 * {@code dx * (r_y - p_y) - dy * (r_x - p_x) >= 0} with {@code (dx, dy) = q - p}.
	 */
	private void addFacets(final TermVariable x, final TermVariable y, final List<List<Rational>> hull,
			final Set<Term> facets) {
		if (hull.size() < 3) {
			return;
		}
		for (int k = 0; k < hull.size(); k++) {
			final List<Rational> p = hull.get(k);
			final List<Rational> q = hull.get((k + 1) % hull.size());
			Rational dx = q.get(0).sub(p.get(0));
			Rational dy = q.get(1).sub(p.get(1));
			if (dx.signum() == 0 || dy.signum() == 0) {
				// parallel to an axis: a bound of one variable, proposed already
				continue;
			}
			final Rational gcd = dx.gcd(dy);
			dx = dx.div(gcd);
			dy = dy.div(gcd);
			if (dx.abs().compareTo(Rational.valueOf(MAX_FACET_COEFFICIENT, 1)) > 0
					|| dy.abs().compareTo(Rational.valueOf(MAX_FACET_COEFFICIENT, 1)) > 0) {
				continue;
			}
			final Term lhs = SmtUtils.sum(mScript, x.getSort(), SmtUtils.mul(mScript, dx, y),
					SmtUtils.mul(mScript, dy.negate(), x));
			final Rational rhs = dx.mul(p.get(1)).sub(dy.mul(p.get(0)));
			facets.add(relation(RelationSymbol.GEQ, lhs, constant(rhs, x.getSort())));
		}
	}

	/** @return the vertices of the convex hull of {@code points} in counterclockwise order (monotone chain) */
	private static List<List<Rational>> convexHull(final List<List<Rational>> points) {
		points.sort(Comparator.<List<Rational>, Rational> comparing(p -> p.get(0)).thenComparing(p -> p.get(1)));
		if (points.size() < 3) {
			return points;
		}
		final List<List<Rational>> hull = new ArrayList<>();
		for (int pass = 0; pass < 2; pass++) {
			final int start = hull.size();
			for (int k = 0; k < points.size(); k++) {
				final List<Rational> point = points.get(pass == 0 ? k : points.size() - 1 - k);
				while (hull.size() >= start + 2
						&& cross(hull.get(hull.size() - 2), hull.get(hull.size() - 1), point).signum() <= 0) {
					hull.remove(hull.size() - 1);
				}
				hull.add(point);
			}
			// the last point of each chain is the first of the other
			hull.remove(hull.size() - 1);
		}
		return hull;
	}

	/** @return the cross product of {@code a - o} and {@code b - o}, positive if o, a, b turn counterclockwise */
	private static Rational cross(final List<Rational> o, final List<Rational> a, final List<Rational> b) {
		return a.get(0).sub(o.get(0)).mul(b.get(1).sub(o.get(1)))
				.sub(a.get(1).sub(o.get(1)).mul(b.get(0).sub(o.get(0))));
	}

	private void addEqualities(final List<TermVariable> variables, final List<Rational[]> points,
			final Set<Term> equalities) {
		if (points.size() < 3 || variables.size() > MAX_HULL_DIMENSION) {
			return;
		}
		final AffineHull.Result hull = AffineHull.compute(points);
		// Any rank + 1 points in general position span a hull of that dimension; only more points are evidence.
		if (points.size() <= hull.rank() + 1) {
			return;
		}
		for (final AffineHull.Equality equality : hull.equalities()) {
			if (equality.support() > MAX_SUPPORT) {
				continue;
			}
			final List<Term> summands = new ArrayList<>();
			final BigInteger[] coefficients = equality.coefficients();
			for (int i = 0; i < coefficients.length; i++) {
				if (coefficients[i].signum() != 0) {
					summands.add(SmtUtils.mul(mScript, Rational.valueOf(coefficients[i], BigInteger.ONE),
							variables.get(i)));
				}
			}
			final Sort sort = variables.get(0).getSort();
			equalities.add(relation(RelationSymbol.EQ, SmtUtils.sum(mScript, sort, summands.toArray(Term[]::new)),
					constant(Rational.valueOf(equality.constant(), BigInteger.ONE), sort)));
		}
	}

	private void addBoundsAndOrderings(final List<TermVariable> variables, final List<Rational[]> points,
			final Set<Term> lower, final Set<Term> orderings, final Set<Term> upper) {
		if (points.isEmpty()) {
			return;
		}
		final List<Integer> varying = new ArrayList<>();
		for (int i = 0; i < variables.size(); i++) {
			Rational min = points.get(0)[i];
			Rational max = min;
			for (final Rational[] point : points) {
				min = point[i].compareTo(min) < 0 ? point[i] : min;
				max = point[i].compareTo(max) > 0 ? point[i] : max;
			}
			final TermVariable variable = variables.get(i);
			lower.add(relation(RelationSymbol.GEQ, variable, constant(min, variable.getSort())));
			upper.add(relation(RelationSymbol.LEQ, variable, constant(max, variable.getSort())));
			if (!min.equals(max) && varying.size() < MAX_ORDERED_VARIABLES) {
				varying.add(i);
			}
		}
		for (int a = 0; a < varying.size(); a++) {
			for (int b = a + 1; b < varying.size(); b++) {
				final int i = varying.get(a);
				final int j = varying.get(b);
				boolean leq = true;
				boolean geq = true;
				for (final Rational[] point : points) {
					final int comparison = point[i].compareTo(point[j]);
					leq &= comparison <= 0;
					geq &= comparison >= 0;
				}
				// Both: always equal, which the affine hull proposes.
				if (leq && !geq) {
					orderings.add(relation(RelationSymbol.LEQ, variables.get(i), variables.get(j)));
				} else if (geq && !leq) {
					orderings.add(relation(RelationSymbol.GEQ, variables.get(i), variables.get(j)));
				}
			}
		}
	}

	private Term constant(final Rational value, final Sort sort) {
		return value.toTerm(sort);
	}

	/** {@code lhs relation rhs}, in the normal form the predicate factories expect. */
	private Term relation(final RelationSymbol relation, final Term lhs, final Term rhs) {
		return PolynomialRelation.of(mScript, relation, lhs, rhs).toTerm(mScript);
	}

	/**
	 * @return whether {@code variable} is one that points may give a value to
	 */
	static boolean isSampled(final TermVariable variable) {
		return SmtSortUtils.isIntSort(variable.getSort());
	}

	/**
	 * Reads a point from the conjuncts of an interpolant: every conjunct {@code v = c} with an integer variable
	 * {@code v} and a literal {@code c}.
	 *
	 * @return the point, empty if no conjunct fixes a variable
	 */
	static Map<TermVariable, Rational> pointOf(final Iterable<Term> conjuncts) {
		final Map<TermVariable, Rational> point = new LinkedHashMap<>();
		for (final Term conjunct : conjuncts) {
			final Map.Entry<TermVariable, Rational> fixed = fixedValue(conjunct);
			if (fixed != null) {
				point.put(fixed.getKey(), fixed.getValue());
			}
		}
		return point;
	}

	/** @return {@code v -> c} if {@code term} is {@code v = c} or {@code c = v} for an integer variable */
	private static Map.Entry<TermVariable, Rational> fixedValue(final Term term) {
		if (!(term instanceof final ApplicationTerm application)
				|| !"=".equals(application.getFunction().getName()) || application.getParameters().length != 2) {
			return null;
		}
		final Term first = application.getParameters()[0];
		final Term second = application.getParameters()[1];
		if (first instanceof final TermVariable variable && isSampled(variable)) {
			final Rational value = SmtUtils.tryToConvertToLiteral(second);
			return value == null ? null : Map.entry(variable, value);
		}
		if (second instanceof final TermVariable variable && isSampled(variable)) {
			final Rational value = SmtUtils.tryToConvertToLiteral(first);
			return value == null ? null : Map.entry(variable, value);
		}
		return null;
	}
}
