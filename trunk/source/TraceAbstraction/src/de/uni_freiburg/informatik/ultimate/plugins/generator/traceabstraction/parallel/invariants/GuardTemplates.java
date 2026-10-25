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

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Candidate invariants from the conditions of the loops: every integer comparison {@code a < b} or {@code a <= b} (or
 * {@code >}, {@code >=}) in a transition that leaves a loop head and that mentions only values the variables have at
 * the head, as the non-strict comparison over the program variables. E.g. {@code i < n} of the loop condition gives
 * {@code i <= n}, which holds at the head of a loop that counts up to {@code n}. The comparisons of the exit
 * condition give candidates too, which are rarely invariants; Houdini drops them.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
final class GuardTemplates {

	private GuardTemplates() {
	}

	/**
	 * @param heads
	 *            the locations to propose candidates for
	 * @return per head location, the candidates, over the term variables of the program variables
	 */
	static <L extends IIcfgTransition<?>> Map<IcfgLocation, Set<Term>> compute(final ManagedScript mgdScript,
			final INestedWordAutomaton<L, IPredicate> abstraction, final Set<IcfgLocation> heads) {
		final Map<IcfgLocation, Set<Term>> result = new LinkedHashMap<>();
		for (final L letter : abstraction.getVpAlphabet().getInternalAlphabet()) {
			final IcfgLocation source = letter.getSource();
			if (!heads.contains(source)) {
				continue;
			}
			final Set<Term> candidates = candidates(mgdScript, letter.getTransformula());
			if (!candidates.isEmpty()) {
				result.computeIfAbsent(source, x -> new LinkedHashSet<>()).addAll(candidates);
			}
		}
		return result;
	}

	private static Set<Term> candidates(final ManagedScript mgdScript, final UnmodifiableTransFormula tf) {
		// in-var of the transition -> term variable of its program variable, i.e. the value at the source
		final Map<Term, Term> atSource = new HashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> in : tf.getInVars().entrySet()) {
			if (!in.getKey().isOldvar()) {
				atSource.put(in.getValue(), in.getKey().getTermVariable());
			}
		}
		final Set<Term> result = new LinkedHashSet<>();
		for (final Term conjunct : SmtUtils.getConjuncts(tf.getFormula())) {
			final TermVariable[] freeVars = conjunct.getFreeVars();
			if (freeVars.length == 0 || !List.of(freeVars).stream().allMatch(atSource::containsKey)) {
				continue;
			}
			final BinaryNumericRelation relation = BinaryNumericRelation.convert(conjunct);
			if (relation == null || !SmtSortUtils.isIntSort(relation.getLhs().getSort())) {
				continue;
			}
			final RelationSymbol weakened = weaken(relation.getRelationSymbol());
			if (weakened == null) {
				continue;
			}
			final Term lhs = PureSubstitution.apply(mgdScript, atSource, relation.getLhs());
			final Term rhs = PureSubstitution.apply(mgdScript, atSource, relation.getRhs());
			final PolynomialRelation candidate =
					PolynomialRelation.of(mgdScript.getScript(), weakened, lhs, rhs);
			result.add(candidate.toTerm(mgdScript.getScript()));
		}
		return result;
	}

	/** @return the non-strict version of an ordering, or null for anything else */
	private static RelationSymbol weaken(final RelationSymbol symbol) {
		switch (symbol) {
		case LESS:
		case LEQ:
			return RelationSymbol.LEQ;
		case GREATER:
		case GEQ:
			return RelationSymbol.GEQ;
		default:
			return null;
		}
	}
}
