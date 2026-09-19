/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.LoopTreeFormulaBuilder.Checkpoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.LoopTreeFormulaBuilder.LoopTree;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.LoopTreeFormulaBuilder.Scope;

/**
 * A transition system made from a {@link LoopTree}: the state is the program variables plus a program counter
 * {@code pc}. The values of {@code pc} are
 * <ul>
 * <li>{@link #INIT}: program start, has no incoming transition,
 * <li>{@link #FINAL}: the error/accepting states, has only a self loop (stutter), so "an error is reachable within at
 * most k steps" is the same as "{@code pc = FINAL} after exactly k steps",
 * <li>every loop head (all nesting depths),
 * <li>every "waypoint": a state outside a loop that a {@code break} out of the loop can jump to.
 * </ul>
 * Every edge of every scope of the tree is one transition, from the node of its source checkpoint to the node of its
 * target checkpoint, labelled with the edge's formula. Every program execution is a sequence of such transitions,
 * because it is cut at each visit of a loop head.
 * <p>
 * {@link #step} builds the relation between step {@code idx} and step {@code idx + 1}. Variables a transition does
 * not assign are explicitly kept equal (frame), and auxiliary variables are instantiated separately for every
 * transition and step.
 *
 * @param <STATE>
 *            state type of the automaton
 */
public class PcTransitionSystem<STATE> {

	public static final int INIT = 0;
	public static final int FINAL = 1;

	private final List<Transition> mTransitions = new ArrayList<>();
	private final Map<STATE, Integer> mHeadNodes = new LinkedHashMap<>();
	private final Map<STATE, Integer> mWaypointNodes = new LinkedHashMap<>();
	private final Set<IProgramVar> mVars = new LinkedHashSet<>();
	private int mNumNodes = 2;

	/**
	 * Supplies the terms for one unrolling of the system, either constants (for a solver query) or term variables
	 * (to build a formula with quantifiers).
	 */
	public interface StepVars {
		/** The value of the program variable in step {@code idx}. */
		Term var(IProgramVar pv, int idx);

		/** The program counter in step {@code idx}. */
		Term pc(int idx);

		/** The auxiliary variable of transition {@code transitionId}, as used between step {@code idx} and the next. */
		Term aux(int transitionId, TermVariable auxVar, int idx);
	}

	private static final class Transition {
		final int mId;
		final int mFrom;
		final int mTo;
		// null: identity (stutter)
		final UnmodifiableTransFormula mFormula;

		Transition(final int id, final int from, final int to, final UnmodifiableTransFormula formula) {
			mId = id;
			mFrom = from;
			mTo = to;
			mFormula = formula;
		}
	}

	public PcTransitionSystem(final LoopTree<STATE> tree) {
		final List<Scope<STATE>> scopes = new ArrayList<>();
		scopes.add(tree.getRoot());
		for (final Scope<STATE> loop : tree.getLoops()) {
			mHeadNodes.put(loop.getHead(), mNumNodes++);
			scopes.add(loop);
		}
		for (final Scope<STATE> scope : scopes) {
			for (final Map.Entry<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> from : scope
					.getEdges().entrySet()) {
				for (final Map.Entry<Checkpoint<STATE>, UnmodifiableTransFormula> to : from.getValue().entrySet()) {
					addTransition(nodeOf(scope, from.getKey()), nodeOf(scope, to.getKey()), to.getValue());
				}
			}
		}
		addTransition(FINAL, FINAL, null);
	}

	private void addTransition(final int from, final int to, final UnmodifiableTransFormula formula) {
		mTransitions.add(new Transition(mTransitions.size(), from, to, formula));
		if (formula != null) {
			collectVars(formula.getInVars().keySet());
			collectVars(formula.getOutVars().keySet());
		}
	}

	private void collectVars(final Set<IProgramVar> vars) {
		for (final IProgramVar pv : vars) {
			if (!pv.isOldvar()) {
				mVars.add(pv);
			}
		}
	}

	private int nodeOf(final Scope<STATE> scope, final Checkpoint<STATE> checkpoint) {
		if (checkpoint.isInit()) {
			return scope.isRoot() ? INIT : mHeadNodes.get(scope.getHead());
		}
		if (checkpoint.isEnd()) {
			return mHeadNodes.get(scope.getHead());
		}
		if (checkpoint.isFinal()) {
			return FINAL;
		}
		if (checkpoint.isLoopHead()) {
			return mHeadNodes.get(checkpoint.getLoopHead());
		}
		final STATE state = checkpoint.getEscapeState();
		final Integer head = mHeadNodes.get(state);
		if (head != null) {
			return head;
		}
		return mWaypointNodes.computeIfAbsent(state, k -> mNumNodes++);
	}

	/** The pc value of each loop head. */
	public Map<STATE, Integer> getHeadNodes() {
		return Collections.unmodifiableMap(mHeadNodes);
	}

	/** The non-old program variables that occur in some transition. */
	public Set<IProgramVar> getVars() {
		return Collections.unmodifiableSet(mVars);
	}

	public int getNumTransitions() {
		return mTransitions.size();
	}

	public int getNumNodes() {
		return mNumNodes;
	}

	/** The term for the pc value {@code node}. */
	public static Term pcValue(final Script script, final int node) {
		return SmtUtils.constructIntValue(script, BigInteger.valueOf(node));
	}

	/**
	 * The relation between step {@code idx} and step {@code idx + 1}: some transition is taken, i.e. pc and variables
	 * of the two steps fit to one of the transitions.
	 */
	public Term step(final int idx, final StepVars sv, final ManagedScript mgdScript) {
		final Script script = mgdScript.getScript();
		final List<Term> disjuncts = new ArrayList<>();
		for (final Transition t : mTransitions) {
			final List<Term> conjuncts = new ArrayList<>();
			conjuncts.add(SmtUtils.binaryEquality(script, sv.pc(idx), pcValue(script, t.mFrom)));
			conjuncts.add(SmtUtils.binaryEquality(script, sv.pc(idx + 1), pcValue(script, t.mTo)));
			final Set<IProgramVar> assigned = new LinkedHashSet<>();
			if (t.mFormula != null) {
				conjuncts.add(instantiate(t, idx, sv, mgdScript, assigned));
			}
			for (final IProgramVar pv : mVars) {
				if (!assigned.contains(pv)) {
					conjuncts.add(SmtUtils.binaryEquality(script, sv.var(pv, idx + 1), sv.var(pv, idx)));
				}
			}
			disjuncts.add(SmtUtils.and(script, conjuncts));
		}
		return SmtUtils.or(script, disjuncts);
	}

	private Term instantiate(final Transition t, final int idx, final StepVars sv, final ManagedScript mgdScript,
			final Set<IProgramVar> assigned) {
		final UnmodifiableTransFormula tf = t.mFormula;
		final Map<Term, Term> substitution = new HashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> in : tf.getInVars().entrySet()) {
			final IProgramVar pv = in.getKey();
			substitution.put(in.getValue(), pv.isOldvar() ? pv.getDefaultConstant() : sv.var(pv, idx));
		}
		for (final Map.Entry<IProgramVar, TermVariable> out : tf.getOutVars().entrySet()) {
			final IProgramVar pv = out.getKey();
			if (tf.getInVars().get(pv) == out.getValue()) {
				continue;
			}
			assigned.add(pv);
			substitution.put(out.getValue(),
					pv.isOldvar() && !tf.getAssignedVars().contains(pv) ? pv.getDefaultConstant()
							: sv.var(pv, idx + 1));
		}
		for (final TermVariable aux : tf.getAuxVars()) {
			substitution.put(aux, sv.aux(t.mId, aux, idx));
		}
		return PureSubstitution.apply(mgdScript, substitution, tf.getFormula());
	}
}
