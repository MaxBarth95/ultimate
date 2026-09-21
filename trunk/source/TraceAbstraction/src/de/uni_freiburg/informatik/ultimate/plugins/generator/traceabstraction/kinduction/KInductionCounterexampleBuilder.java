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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.PcTransitionSystem.Transition;

/**
 * Turns a {@link KInductionWitness} - what the solver's model of a satisfiable base case said - into a concrete
 * {@link NestedRun} of the abstraction that reaches an accepting state.
 *
 * <h2>Why a search is needed at all</h2>
 *
 * A step of the {@link PcTransitionSystem} is not a single letter. Each of its transitions is one edge of one
 * scope's checkpoint graph, and {@link LoopTreeFormulaBuilder} built that edge by composing whole <em>paths</em> of
 * letters: {@code sequentialComposition} for concatenation, {@code parallelComposition} for the union of
 * alternatives. The union is built without branch indicators, so the composed formula does not record which
 * alternative a model took, and the letters themselves are gone. The model therefore pins down the program state at
 * every checkpoint, but not the way between two of them; that has to be searched for.
 *
 * <h2>What the search may and may not assume</h2>
 *
 * The model is used for the <b>shape</b> of the violation only: which pc node each unrolled state has, and which
 * transition was taken between two of them. That fixes, for every step, the automaton states the letter path has to
 * run between, which is what makes the search tractable.
 * <p>
 * The model's <b>variable values</b> are deliberately not used. A composed edge relation need not agree with any
 * single concrete path about the value a variable ends up with - where the composition leaves an out-variable
 * unconstrained, the model may pick a value no concrete path produces - so constraining the search with those
 * values makes it fail on perfectly good counterexamples. Feasibility is therefore established by the search
 * itself, which is what actually matters.
 * <p>
 * Every path the search considers is checked against the solver as it is extended, over one continuous SSA that
 * spans all steps, so the run that comes back is feasible as a whole and ends in an accepting state. It is
 * therefore a genuine counterexample no matter what the pc encoding did, and
 * {@code KInductionWorkerThread.reportCounterexample} independently confirms it with the ordinary trace check. If
 * the encoding were ever to over-approximate and report a violation that does not exist, no feasible path would be
 * found and this class would throw rather than invent one.
 *
 * <h2>How far the search may wander</h2>
 *
 * Per step the letter path is <b>simple, except that its last state may equal its first</b>. A cut graph is
 * acyclic, and all of a scope's own heads and the heads of its inner loops are sealed in it - they are nodes but
 * have no outgoing edges - so such a state can only ever be a path's last. The exception is what a loop body needs:
 * {@code INIT(h) -> END(h)} in a loop scope runs from the head back to the head. Restricting the search to simple
 * paths alone would drop exactly those, and restricting it no further keeps the search finite.
 * <p>
 * A loop that is entered at several heads also has the steps {@code INIT(h1) -> END(h2)}, whose path runs between
 * two <em>different</em> sealed states and is therefore plainly simple. On such a program the search may leave the
 * transition the model named and come back through a third head, so the run it returns need not be the model's.
 * That is harmless: the path was checked against the solver as it was extended, {@link #assemble} re-checks it with
 * {@code Accepts}, and {@code KInductionWorkerThread.reportCounterexample} re-runs the ordinary trace check - so
 * what comes back is a genuine counterexample either way.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class KInductionCounterexampleBuilder<LETTER extends IAction, STATE> {

	/**
	 * Cuts off a search that is not going to finish, so that a pathological abstraction produces a legible failure
	 * instead of hanging. Reaching this is a bug or a program far outside what k-induction is used on.
	 */
	private static final int MAX_EXPANSIONS = 100_000;

	private static final String CALL_RETURN_RESTRICTION =
			"k-induction counterexamples are restricted to internal transitions, because the nesting relation of a "
					+ "run cannot be recovered from the pc transition system, whose formulas treat a call and a "
					+ "return like any other edge. That treatment is only sound for inlined procedures "
					+ "(see LoopTreeFormulaBuilder), so on a program whose procedures were not inlined the "
					+ "k-induction verdict itself rests on an assumption that does not hold here - not just the "
					+ "counterexample. Inline the procedures, or teach the pc transition system about calls.";

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final Object mLockOwner;
	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final PcTransitionSystem<STATE> mSystem;
	private final KInductionWitness mWitness;

	/** The number of pc steps to reconstruct: everything after it is the FINAL stutter self loop. */
	private final int mSteps;

	// The run being built. Both are undone on backtracking.
	private final List<LETTER> mLetters = new ArrayList<>();
	private final List<STATE> mStates = new ArrayList<>();

	// SSA state: the constant that currently holds each variable's value, and the counters behind those constants.
	private final Map<IProgramVar, Term> mCurrent = new HashMap<>();
	private final Map<String, Term> mCexConstants = new HashMap<>();
	private int mSsaCounter;
	private int mAuxCounter;

	private int mExpansions;

	/** How many scopes we have pushed. A successful search returns with its whole stack standing; see build(). */
	private int mPushDepth;

	// state -> states reachable from it over internal transitions, computed lazily per transition id
	private final Map<Integer, Set<STATE>> mCanReachTarget = new HashMap<>();
	private Map<STATE, List<STATE>> mInternalPredecessors;

	public KInductionCounterexampleBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final Object lockOwner,
			final INestedWordAutomaton<LETTER, STATE> abstraction, final PcTransitionSystem<STATE> system,
			final KInductionWitness witness) {
		mServices = services;
		mLogger = logger;
		mMgdScript = mgdScript;
		mLockOwner = lockOwner;
		mAbstraction = abstraction;
		mSystem = system;
		mWitness = witness;
		mSteps = witness.getFirstFinalStep();
	}

	/**
	 * @return a feasible run of the abstraction into an accepting state.
	 * @throws KInductionCounterexampleException
	 *             if the violation cannot be expressed as a run of the abstraction.
	 */
	public NestedRun<LETTER, STATE> build() {
		// Checked before anything else, because on a call-bearing abstraction the verdict we are asked to witness
		// is itself unsound: LoopTreeFormulaBuilder gives a call and a return edge the transition formula of the
		// call resp. the return and then treats them like ordinary edges, so the transition system admits paths
		// that leave through one call site and come back at another. Such a spliced path skips whatever lies
		// between the two sites, which is how a satisfiable base case can appear for a program that never reaches
		// an error. Searching for a run that realises it would fail anyway, but with a message about the search
		// rather than about the reason.
		final STATE withCall = findCallOrReturn();
		if (withCall != null) {
			throw new KInductionCounterexampleException("k-induction reported a violation at k=" + mWitness.getK()
					+ " (" + mWitness + "), but the abstraction has call and return transitions (for example at "
					+ withCall + "), so that verdict cannot be trusted and no counterexample is reported. "
					+ CALL_RETURN_RESTRICTION);
		}
		checkWitnessShape();
		mLogger.info("KInduction: reconstructing a counterexample for %d pc step(s) of %s", mSteps, mWitness);

		push();
		try {
			final Transition<STATE> first = mSystem.getTransition(mWitness.getTransitionId(0));
			for (final STATE start : first.getSourceStates()) {
				if (!mAbstraction.isInitial(start)) {
					continue;
				}
				mStates.add(start);
				if (solveFrom(0, start)) {
					return assemble();
				}
				mLetters.clear();
				mStates.clear();
				mCurrent.clear();
			}
			throw noRunFound("no counterexample run starts in any of the initial states " + first.getSourceStates()
					+ " of " + first + ", although k-induction reported a violation at k=" + mWitness.getK()
					+ " (" + mWitness + ")");
		} finally {
			// A search that succeeded returns with every scope it pushed still on the stack, so unwind by depth
			// rather than by a fixed count.
			while (mPushDepth > 0) {
				pop();
			}
		}
	}

	private void push() {
		mMgdScript.push(mLockOwner, 1);
		mPushDepth++;
	}

	private void pop() {
		mMgdScript.pop(mLockOwner, 1);
		mPushDepth--;
	}

	/** The parts of the witness this class relies on, checked once so a later failure is not misattributed. */
	private void checkWitnessShape() {
		if (mWitness.getPc(0) != PcTransitionSystem.INIT) {
			throw new AssertionError("the base case asserts pc_0 = INIT, but the model says pc_0 = "
					+ mWitness.getPc(0));
		}
		if (mSteps == 0) {
			throw new AssertionError("the model has pc_0 = FINAL although pc_0 = INIT was asserted");
		}
		for (int j = mSteps; j < mWitness.getK(); j++) {
			if (mWitness.getTransitionId(j) != mSystem.getStutterTransitionId()) {
				throw new AssertionError("FINAL has no outgoing transition but the stutter self loop, yet the "
						+ "model leaves it at step " + j + " via t" + mWitness.getTransitionId(j));
			}
		}
		if (mSteps < mWitness.getK()) {
			mLogger.info("KInduction: the model reaches FINAL after %d of %d step(s); the rest is the stutter self "
					+ "loop and is dropped", mSteps, mWitness.getK());
		}
	}

	/**
	 * Continues the search at the start of pc step {@code step}, with the SSA sitting at that step's boundary.
	 *
	 * @return true if the whole remaining counterexample was found; the solver stack is then left as it is.
	 */
	private boolean solveFrom(final int step, final STATE state) {
		if (step == mSteps) {
			return mAbstraction.isFinal(state);
		}
		final Transition<STATE> transition = mSystem.getTransition(mWitness.getTransitionId(step));
		if (!transition.getSourceStates().contains(state)) {
			return false;
		}
		return extend(step, transition, state, state, new LinkedHashSet<>(Set.of(state)), 0);
	}

	/**
	 * Depth-first search for the letter path of one pc step.
	 *
	 * @param first
	 *            the state the step started in; the only state the path may return to, and only as its last.
	 * @param visited
	 *            the states already on this step's path.
	 * @param length
	 *            how many letters of this step have been taken.
	 */
	private boolean extend(final int step, final Transition<STATE> transition, final STATE current,
			final STATE first, final Set<STATE> visited, final int length) {
		checkBudget();

		// Can this step end here? A zero-length step is legitimate: an edge whose path expression is Epsilon
		// composes to the trivial transition formula.
		if (transition.getTargetStates().contains(current) && solveFrom(step + 1, current)) {
			return true;
		}

		// A path that has come back to its own start is complete by construction and must not run on.
		if (current.equals(first) && length > 0) {
			return false;
		}

		final Set<STATE> useful = canReachATargetOf(transition);
		for (final OutgoingInternalTransition<LETTER, STATE> out : internalSuccessors(current)) {
			final STATE succ = out.getSucc();
			if (visited.contains(succ) && !succ.equals(first)) {
				continue;
			}
			if (!useful.contains(succ)) {
				continue;
			}
			final Map<IProgramVar, Term> restore = new LinkedHashMap<>();
			// Built before the push on purpose: it declares constants, and a declaration made inside a scope is
			// forgotten when that scope is popped while the cache would happily hand the stale term out again.
			final Term ssa = ssaOfLetter(out.getLetter(), restore);
			push();
			mMgdScript.assertTerm(mLockOwner, ssa);
			if (mMgdScript.checkSat(mLockOwner) != LBool.UNSAT) {
				mLetters.add(out.getLetter());
				mStates.add(succ);
				// succ may be `first`, which is already in visited; do not drop it again on backtracking.
				final boolean newlyVisited = visited.add(succ);
				if (extend(step, transition, succ, first, visited, length + 1)) {
					return true;
				}
				if (newlyVisited) {
					visited.remove(succ);
				}
				mStates.remove(mStates.size() - 1);
				mLetters.remove(mLetters.size() - 1);
			}
			pop();
			restoreCurrent(restore);
		}
		return false;
	}

	/** Undoes what one {@link #ssaOfLetter} call changed; a null value means the variable had no constant yet. */
	private void restoreCurrent(final Map<IProgramVar, Term> restore) {
		for (final Map.Entry<IProgramVar, Term> entry : restore.entrySet()) {
			if (entry.getValue() == null) {
				mCurrent.remove(entry.getKey());
			} else {
				mCurrent.put(entry.getKey(), entry.getValue());
			}
		}
	}

	/**
	 * The letter's transition formula over the SSA constants, following {@code PcTransitionSystem.instantiate}
	 * exactly - in particular old variables go to their default constant, which is what the k-induction encoding
	 * assumes and what {@link #build()} pinned once at the top.
	 *
	 * @param restore
	 *            filled with the entries of {@link #mCurrent} this call overwrites, so it can be undone.
	 */
	private Term ssaOfLetter(final LETTER letter, final Map<IProgramVar, Term> restore) {
		final UnmodifiableTransFormula tf = letter.getTransformula();
		final Map<Term, Term> substitution = new HashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> in : tf.getInVars().entrySet()) {
			final IProgramVar pv = in.getKey();
			substitution.put(in.getValue(), pv.isOldvar() ? pv.getDefaultConstant() : current(pv));
		}
		final Map<IProgramVar, Term> updates = new LinkedHashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> out : tf.getOutVars().entrySet()) {
			final IProgramVar pv = out.getKey();
			if (tf.getInVars().get(pv) == out.getValue()) {
				continue;
			}
			if (pv.isOldvar()) {
				throw new KInductionCounterexampleException("letter " + letter + " assigns the old variable " + pv
						+ ". Only a procedure call's modifies clause does that, and k-induction counterexamples "
						+ "are restricted to internal transitions.");
			}
			final Term next = nextConstant(pv);
			substitution.put(out.getValue(), next);
			updates.put(pv, next);
		}
		for (final TermVariable aux : tf.getAuxVars()) {
			// Fresh per occurrence, not per letter: the same letter can appear twice in one run.
			substitution.put(aux, PredicateUtils.getIndexedConstant("kicexaux_" + aux.getName(), aux.getSort(),
					mAuxCounter++, mCexConstants, script()));
		}
		final Term result = PureSubstitution.apply(mMgdScript, substitution, tf.getFormula());
		for (final IProgramVar pv : updates.keySet()) {
			restore.put(pv, mCurrent.get(pv));
		}
		mCurrent.putAll(updates);
		return result;
	}

	private Term current(final IProgramVar pv) {
		return mCurrent.computeIfAbsent(pv, this::nextConstant);
	}

	/**
	 * A fresh constant for {@code pv}. The prefix and the cache are deliberately separate from the ones
	 * {@link KInduction} uses for its own unrolling, so the two can never alias.
	 */
	private Term nextConstant(final IProgramVar pv) {
		return PredicateUtils.getIndexedConstant("kicex_" + pv.getGloballyUniqueId(),
				pv.getTermVariable().getSort(), mSsaCounter++, mCexConstants, script());
	}

	/**
	 * The internal successors of {@code state}. A call or a return here is refused rather than skipped: the
	 * checkpoint formulas were built from those edges too, so ignoring one could make the search miss the very
	 * path the model took and report a violation as unreconstructible for the wrong reason.
	 */
	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		if (hasCallOrReturn(state)) {
			throw new KInductionCounterexampleException(
					"state " + state + " has a call or return transition. " + CALL_RETURN_RESTRICTION);
		}
		return mAbstraction.internalSuccessors(state);
	}

	private boolean hasCallOrReturn(final STATE state) {
		return mAbstraction.callSuccessors(state).iterator().hasNext()
				|| mAbstraction.returnSuccessors(state).iterator().hasNext();
	}

	/**
	 * The first state with a call or a return transition, or {@code null} if the abstraction has none.
	 * <p>
	 * Only used to explain a failed search. The search itself walks internal transitions and prunes with an
	 * internal-only reachability check, so a counterexample that needs a call is not merely missed at the state
	 * that has the call - the pruning can rule out every successor long before that state is reached, and the
	 * search then ends with nothing to point at. Without this, such a run is reported as "no path found", which
	 * sends the reader looking for a bug in the search instead of at the real cause.
	 */
	private STATE findCallOrReturn() {
		for (final STATE state : mAbstraction.getStates()) {
			if (hasCallOrReturn(state)) {
				return state;
			}
		}
		return null;
	}

	/**
	 * Turns a failed search into the most specific explanation available.
	 */
	private KInductionCounterexampleException noRunFound(final String what) {
		final STATE withCall = findCallOrReturn();
		if (withCall != null) {
			return new KInductionCounterexampleException(what + ". The abstraction has call and return transitions "
					+ "(for example at " + withCall + "), so this is expected: " + CALL_RETURN_RESTRICTION);
		}
		return new KInductionCounterexampleException(what + ". The abstraction has only internal transitions, so "
				+ "this is not a restriction of the reconstruction: the pc transition system claims a path that "
				+ "the letters of the abstraction do not admit, which means the two disagree.");
	}

	/**
	 * The states from which some target of {@code transition} is still reachable. Prunes the search away from
	 * parts of the automaton that cannot end this step at all.
	 */
	private Set<STATE> canReachATargetOf(final Transition<STATE> transition) {
		return mCanReachTarget.computeIfAbsent(transition.getId(), id -> {
			final Map<STATE, List<STATE>> predecessors = internalPredecessors();
			final Set<STATE> result = new HashSet<>(transition.getTargetStates());
			final Deque<STATE> worklist = new ArrayDeque<>(result);
			while (!worklist.isEmpty()) {
				for (final STATE pred : predecessors.getOrDefault(worklist.pop(), List.of())) {
					if (result.add(pred)) {
						worklist.push(pred);
					}
				}
			}
			return result;
		});
	}

	private Map<STATE, List<STATE>> internalPredecessors() {
		if (mInternalPredecessors == null) {
			mInternalPredecessors = new HashMap<>();
			for (final STATE state : mAbstraction.getStates()) {
				for (final OutgoingInternalTransition<LETTER, STATE> out : mAbstraction.internalSuccessors(state)) {
					mInternalPredecessors.computeIfAbsent(out.getSucc(), k -> new ArrayList<>()).add(state);
				}
			}
		}
		return mInternalPredecessors;
	}

	private void checkBudget() {
		mExpansions++;
		if (mExpansions > MAX_EXPANSIONS) {
			throw new KInductionCounterexampleException("gave up reconstructing a counterexample after "
					+ MAX_EXPANSIONS + " expansions for " + mWitness);
		}
		if (mExpansions % 512 == 0 && !mServices.getProgressMonitorService().continueProcessing()) {
			throw new KInductionCounterexampleException(
					"cancelled while reconstructing a counterexample for " + mWitness);
		}
	}

	private NestedRun<LETTER, STATE> assemble() {
		if (mLetters.isEmpty()) {
			throw new KInductionCounterexampleException("the reconstructed counterexample is empty; an initial "
					+ "state of the abstraction is also accepting, which no consumer of a counterexample supports");
		}
		// Only internal letters get here, see internalSuccessors, so every position is an internal one.
		NestedWord<LETTER> word = new NestedWord<>();
		for (final LETTER letter : mLetters) {
			word = word.concatenate(new NestedWord<>(letter, NestedWord.INTERNAL_POSITION));
		}
		final NestedRun<LETTER, STATE> run = new NestedRun<>(word, new ArrayList<>(mStates));

		final STATE last = mStates.get(mStates.size() - 1);
		if (!mAbstraction.isFinal(last)) {
			throw new AssertionError("the reconstructed run ends in " + last + ", which is not accepting");
		}
		try {
			if (!new Accepts<>(new AutomataLibraryServices(mServices), mAbstraction, word).getResult()) {
				throw new AssertionError("the abstraction does not accept the reconstructed run " + word);
			}
		} catch (final Exception e) {
			throw new AssertionError("could not check the reconstructed run against the abstraction: " + e, e);
		}
		mLogger.info("KInduction: reconstructed a counterexample of %d letter(s) after %d expansion(s)",
				mLetters.size(), mExpansions);
		return run;
	}

	private Script script() {
		return mMgdScript.getScript();
	}
}
