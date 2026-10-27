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
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AbstractGeneralizedAffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Generalizes the interpolants of a loop head across its unwindings. When trace abstraction diverges on a loop, the
 * interpolants at the successive visits of the loop head on one trace differ only in their constants, e.g.
 * {@code x <= 0}, {@code x <= 2}, {@code x <= 4}, and on another trace {@code i <= 0}, {@code i <= 1}, {@code i <= 2}.
 * Each is a bound that only holds for so many iterations; the relation between them, here {@code x <= 2i}, is on no
 * trace, but it is what the two series say together.
 * <p>
 * Every linear integer conjunct {@code sum a_v * v <= c} (or {@code >=}, {@code =}) is split into its <i>shape</i>, the
 * relation and the left-hand side, and its constant {@code c}. On one interpolant sequence, the constants of a shape at
 * the j-th visit of a loop head form a series. If at least {@link #MIN_VISITS} visits lie on a line
 * {@code p * j + q * c = d} with {@code p != 0}, it is a <i>trend</i>. Each sequence starts at the initial location,
 * so j counts the iterations alike on all of them, and two trends of different shapes at the same head can be combined
 * by eliminating j: from {@code p1 * j + q1 * c1 = d1} and {@code p2 * j + q2 * c2 = d2} follows
 * {@code p2 * q1 * c1 - p1 * q2 * c2 = p2 * d1 - p1 * d2}. The supplier proposes the same relation between the
 * left-hand sides, with {@code =}, {@code <=} and {@code >=}: which one is inductive depends on the directions of the
 * bounds.
 * <p>
 * The candidates are guesses; the supplier publishes only what it proves to be inductive. Only used by the thread of
 * the {@link InvariantSupplier}.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
final class InterpolantShapes {

	/** Two visits always lie on a line, so only three or more are evidence for one. */
	private static final int MIN_VISITS = 3;
	/** How many trends are kept per location; beyond that new ones are dropped. */
	private static final int MAX_TRENDS = 32;
	/** How many new candidates one call of {@link #candidates} proposes at most. */
	private static final int MAX_CANDIDATES = 24;

	/**
	 * The shape of a conjunct {@code sum coefficients(v) * v relation constant}: integer coefficients without a common
	 * divisor, the one of the variable first by name positive.
	 */
	record Shape(RelationSymbol relation, Map<TermVariable, Rational> coefficients) {
		Shape {
			coefficients = Map.copyOf(coefficients);
		}

		@Override
		public String toString() {
			return sortedVariables(coefficients).stream().map(v -> coefficients.get(v) + "*" + v)
					.collect(Collectors.joining(" + ")) + " " + relation + " _";
		}
	}

	/** The constant {@code c} of {@code shape} at the j-th visit of a loop head satisfies {@code p * j + q * c = d}. */
	private record Trend(Shape shape, BigInteger p, BigInteger q, BigInteger d) {
		@Override
		public String toString() {
			return shape + " with " + p + "*j + " + q + "*_ = " + d;
		}
	}

	private final Script mScript;
	/** Per location, the trends with the number of sequences that showed them. */
	private final Map<IcfgLocation, Map<Trend, Integer>> mTrends = new HashMap<>();
	private final Set<IcfgLocation> mChanged = new LinkedHashSet<>();
	private final Map<IcfgLocation, Set<Term>> mProposed = new HashMap<>();

	InterpolantShapes(final Script script) {
		mScript = script;
	}

	/**
	 * Takes the series of the loop heads on one interpolant sequence.
	 *
	 * @param locations
	 *            the locations of the sequence, from the initial one on
	 * @param conjuncts
	 *            for each location, the conjuncts of its interpolant, in the supplier's script
	 * @param heads
	 *            the loop heads
	 */
	void add(final List<IcfgLocation> locations, final List<List<Term>> conjuncts, final Set<IcfgLocation> heads) {
		// per head and shape: visit index -> constant
		final Map<IcfgLocation, Map<Shape, Map<Integer, Rational>>> series = new LinkedHashMap<>();
		final Map<IcfgLocation, Integer> visits = new HashMap<>();
		for (int i = 0; i < locations.size(); i++) {
			final IcfgLocation location = locations.get(i);
			if (!heads.contains(location)) {
				continue;
			}
			final int visit = visits.merge(location, 1, Integer::sum) - 1;
			final Map<Shape, Map<Integer, Rational>> byShape =
					series.computeIfAbsent(location, x -> new LinkedHashMap<>());
			for (final Term conjunct : conjuncts.get(i)) {
				final Map.Entry<Shape, Rational> shaped = shapeOf(mScript, conjunct);
				if (shaped != null) {
					byShape.computeIfAbsent(shaped.getKey(), x -> new LinkedHashMap<>()).putIfAbsent(visit,
							shaped.getValue());
				}
			}
		}
		for (final Map.Entry<IcfgLocation, Map<Shape, Map<Integer, Rational>>> head : series.entrySet()) {
			for (final Map.Entry<Shape, Map<Integer, Rational>> shape : head.getValue().entrySet()) {
				final Trend trend = trend(shape.getKey(), shape.getValue());
				if (trend == null) {
					continue;
				}
				final Map<Trend, Integer> trends = mTrends.computeIfAbsent(head.getKey(), x -> new LinkedHashMap<>());
				if (trends.containsKey(trend)) {
					trends.merge(trend, 1, Integer::sum);
				} else if (trends.size() < MAX_TRENDS) {
					trends.put(trend, 1);
					mChanged.add(head.getKey());
				}
			}
		}
	}

	/** @return the locations that got new trends since the last call */
	Set<IcfgLocation> takeChanged() {
		final Set<IcfgLocation> result = new LinkedHashSet<>(mChanged);
		mChanged.clear();
		return result;
	}

	int count(final IcfgLocation location) {
		return mTrends.getOrDefault(location, Map.of()).size();
	}

	/** @return for the log, the trends of {@code location} */
	String describe(final IcfgLocation location) {
		return mTrends.getOrDefault(location, Map.of()).entrySet().stream()
				.map(e -> e.getKey() + " (" + e.getValue() + "x)").collect(Collectors.joining("; "));
	}

	/**
	 * @return the candidates of {@code location} not proposed before, from the pairs of the trends seen most often
	 */
	Set<Term> candidates(final IcfgLocation location) {
		final List<Map.Entry<Trend, Integer>> trends =
				new ArrayList<>(mTrends.getOrDefault(location, Map.of()).entrySet());
		trends.sort(Map.Entry.<Trend, Integer> comparingByValue().reversed());
		final List<Map.Entry<Trend, Integer>[]> pairs = new ArrayList<>();
		for (int a = 0; a < trends.size(); a++) {
			for (int b = a + 1; b < trends.size(); b++) {
				@SuppressWarnings("unchecked")
				final Map.Entry<Trend, Integer>[] pair = new Map.Entry[] { trends.get(a), trends.get(b) };
				pairs.add(pair);
			}
		}
		pairs.sort(Comparator.comparingInt((final Map.Entry<Trend, Integer>[] p) -> p[0].getValue() + p[1].getValue())
				.reversed());
		final Set<Term> proposed = mProposed.computeIfAbsent(location, x -> new LinkedHashSet<>());
		final Set<Term> result = new LinkedHashSet<>();
		for (final Map.Entry<Trend, Integer>[] pair : pairs) {
			final Trend first = pair[0].getKey();
			final Trend second = pair[1].getKey();
			if (first.shape().equals(second.shape())) {
				continue;
			}
			// p2 * q1 * t1 - p1 * q2 * t2 = p2 * d1 - p1 * d2
			final Term lhs = combine(Rational.valueOf(second.p().multiply(first.q()), BigInteger.ONE), first.shape(),
					Rational.valueOf(first.p().multiply(second.q()).negate(), BigInteger.ONE), second.shape());
			if (lhs == null) {
				continue;
			}
			final Term rhs = Rational.valueOf(second.p().multiply(first.d()).subtract(first.p().multiply(second.d())),
					BigInteger.ONE).toTerm(lhs.getSort());
			for (final RelationSymbol relation : List.of(RelationSymbol.EQ, RelationSymbol.LEQ, RelationSymbol.GEQ)) {
				if (result.size() >= MAX_CANDIDATES) {
					return result;
				}
				final Term candidate = PolynomialRelation.of(mScript, relation, lhs, rhs).toTerm(mScript);
				if (proposed.add(candidate)) {
					result.add(candidate);
				}
			}
		}
		return result;
	}

	/**
	 * @return the line through the constants of a shape over the visits, if it has at least {@link #MIN_VISITS} of
	 *         them and the constant changes along it
	 */
	private static Trend trend(final Shape shape, final Map<Integer, Rational> constants) {
		if (constants.size() < MIN_VISITS) {
			return null;
		}
		final List<Rational[]> points = new ArrayList<>();
		for (final Map.Entry<Integer, Rational> entry : constants.entrySet()) {
			points.add(new Rational[] { Rational.valueOf(entry.getKey(), 1), entry.getValue() });
		}
		final AffineHull.Result hull = AffineHull.compute(points);
		// Rank 2: the constants are on no line. Rank 1 with j's coefficient 0: the constant does not change, so the
		// conjunct itself is the candidate, which the supplier has seen already.
		if (hull.rank() != 1) {
			return null;
		}
		final AffineHull.Equality line = hull.equalities().get(0);
		final BigInteger p = line.coefficients()[0];
		final BigInteger q = line.coefficients()[1];
		if (p.signum() == 0 || q.signum() == 0) {
			return null;
		}
		return new Trend(shape, p, q, line.constant());
	}

	/**
	 * @return {@code l1 * t1 + l2 * t2} for the left-hand sides {@code t1}, {@code t2} of the shapes, or {@code null} if
	 *         the variables cancel out
	 */
	private Term combine(final Rational l1, final Shape first, final Rational l2, final Shape second) {
		final Map<TermVariable, Rational> sum = new HashMap<>();
		first.coefficients().forEach((v, c) -> sum.merge(v, c.mul(l1), Rational::add));
		second.coefficients().forEach((v, c) -> sum.merge(v, c.mul(l2), Rational::add));
		final List<Term> summands = new ArrayList<>();
		for (final TermVariable variable : sortedVariables(sum)) {
			final Rational coefficient = sum.get(variable);
			if (coefficient.signum() != 0) {
				summands.add(SmtUtils.mul(mScript, coefficient, variable));
			}
		}
		if (summands.isEmpty()) {
			return null;
		}
		return SmtUtils.sum(mScript, summands.get(0).getSort(), summands.toArray(Term[]::new));
	}

	/**
	 * @return the shape and the constant of {@code conjunct}, or {@code null} if it is no linear (in)equality over
	 *         integer variables
	 */
	static Map.Entry<Shape, Rational> shapeOf(final Script script, final Term conjunct) {
		PolynomialRelation relation = PolynomialRelation.of(script, conjunct);
		if (relation == null || !relation.isAffine()
				|| !SmtSortUtils.isIntSort(relation.getPolynomialTerm().getSort())) {
			return null;
		}
		relation = relation.tryToConvertToEquivalentNonStrictRelation();
		RelationSymbol symbol = relation.getRelationSymbol();
		if (symbol != RelationSymbol.EQ && symbol != RelationSymbol.LEQ && symbol != RelationSymbol.GEQ) {
			return null;
		}
		// polynomial symbol 0, i.e. sum + constant symbol 0, i.e. sum symbol -constant
		final AbstractGeneralizedAffineTerm<?> polynomial = relation.getPolynomialTerm();
		final Map<TermVariable, Rational> coefficients = new HashMap<>();
		BigInteger gcd = BigInteger.ZERO;
		for (final Map.Entry<Term, Rational> entry : polynomial.getAbstractVariableAsTerm2Coefficient(script)
				.entrySet()) {
			if (!(entry.getKey() instanceof final TermVariable variable) || !SampleCandidates.isSampled(variable)
					|| !entry.getValue().isIntegral()) {
				return null;
			}
			coefficients.put(variable, entry.getValue());
			gcd = gcd.gcd(entry.getValue().numerator());
		}
		if (coefficients.isEmpty() || !polynomial.getConstant().isIntegral()) {
			return null;
		}
		final TermVariable first = sortedVariables(coefficients).get(0);
		Rational divisor = Rational.valueOf(gcd, BigInteger.ONE);
		if (coefficients.get(first).signum() < 0) {
			divisor = divisor.negate();
			symbol = symbol.swapParameters();
		}
		final Rational constant = polynomial.getConstant().negate().div(divisor);
		if (symbol == RelationSymbol.EQ && !constant.isIntegral()) {
			return null;
		}
		final Map<TermVariable, Rational> normalized = new HashMap<>();
		for (final Map.Entry<TermVariable, Rational> entry : coefficients.entrySet()) {
			normalized.put(entry.getKey(), entry.getValue().div(divisor));
		}
		return Map.entry(new Shape(symbol, normalized),
				symbol == RelationSymbol.GEQ ? constant.ceil() : constant.floor());
	}

	private static List<TermVariable> sortedVariables(final Map<TermVariable, Rational> coefficients) {
		final List<TermVariable> variables = new ArrayList<>(coefficients.keySet());
		variables.sort(Comparator.comparing(TermVariable::getName));
		return variables;
	}
}
