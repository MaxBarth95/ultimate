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

	private final Script mScript;
	private final Map<IcfgLocation, Set<Map<TermVariable, Rational>>> mPoints = new HashMap<>();
	private final Set<IcfgLocation> mChanged = new LinkedHashSet<>();

	SampleCandidates(final Script script) {
		mScript = script;
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
	 * @return the candidate invariants of {@code location}, most promising first: equalities, lower bounds, orderings,
	 *         upper bounds
	 */
	Set<Term> candidates(final IcfgLocation location) {
		final List<Map<TermVariable, Rational>> points = new ArrayList<>(mPoints.getOrDefault(location, Set.of()));
		final Set<Term> equalities = new LinkedHashSet<>();
		final Set<Term> lower = new LinkedHashSet<>();
		final Set<Term> orderings = new LinkedHashSet<>();
		final Set<Term> upper = new LinkedHashSet<>();
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
		}
		final Set<Term> result = new LinkedHashSet<>();
		for (final Set<Term> kind : List.of(equalities, lower, orderings, upper)) {
			for (final Term candidate : kind) {
				if (result.size() >= MAX_CANDIDATES) {
					return result;
				}
				result.add(candidate);
			}
		}
		return result;
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
