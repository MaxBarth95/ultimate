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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.LoopTreeFormulaBuilder.LoopTree;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.PcTransitionSystem.StepVars;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

/**
 * k-induction on a nested word automaton (path program or abstraction) that represents a program with any number of
 * loops, sequential or nested.
 * <p>
 * {@link LoopTreeFormulaBuilder} summarizes the program as a tree of loops whose edges are transition formulas
 * between checkpoints (program start, loop heads, error states, ...). {@link PcTransitionSystem} turns this into one
 * transition system whose state is the program variables plus a program counter {@code pc}. An error is reachable
 * iff the system reaches {@code pc = FINAL}. This class runs plain k-induction on it, for {@code k = 1, 2, ...}:
 * <ul>
 * <li><b>Base case</b>: {@code pc_0 = INIT}, k transitions, {@code pc_k = FINAL}. SAT is a real violation
 * (<i>unsafe</i>), since FINAL has a self loop this covers every error within k steps.
 * <li><b>Step case</b>: k transitions starting in an arbitrary state that is not {@code INIT}, no error in the first
 * k states, but an error in the last one. UNSAT together with the base case for k proves that no error is reachable
 * at all (<i>safe</i>). INIT can be excluded in the first state because it has no incoming transition, so every
 * error at a step {@code > k} is preceded by k non-INIT states, and errors at steps {@code <= k} are found by the
 * base case.
 * </ul>
 * Since the whole program, including all loop heads, is one system, a SAFE result is a genuine proof also for
 * several and for nested loops; there is no per-loop or per-path approximation. The only incompleteness is
 * {@link #MAX_K} and the solver returning unknown.
 * <p>
 * <b>Procedures.</b> The transition system is flat and has no call stack, so it never contains a call or a
 * return. If the abstraction has any, {@link ProcedureSummaries} resolves every call site first: a callee whose
 * graph is loop-free becomes one edge for the whole call-to-return span (and one edge per error state inside it,
 * for a call that never returns), while a callee that contains a loop is unfolded into one copy of its states per
 * call site, so that its loop becomes an ordinary nested loop of the tree and gets {@code pc} values of its own.
 * The nodes of the tree are therefore {@link CallNode}s - a state plus the call sites it was reached through - and
 * a loop head of an unfolded callee is a different head at each of its call sites. Recursion is refused there.
 * <p>
 * <b>Invariant injection.</b> The {@link IInvariantSupplier} may return a trusted invariant for any loop head, also
 * a nested one. It is assumed in every unrolled state where {@code pc} is that loop head, in the base and the step
 * case. This only prunes the search and can make a loop inductive that is not k-inductive on its own, but a wrong
 * invariant makes the result wrong. An invariant that mentions a variable that occurs in no transition is dropped,
 * which is always sound.
 * <p>
 * <b>Learned invariants.</b> If the program is proven safe with some k, {@link #getLearnedInvariants()} returns for
 * every loop head the formula "no error can be reached from here within k steps". It holds in every reachable state
 * of the head, because the program is safe, and can be given to other components as an invariant.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class KInduction<LETTER extends IAction, STATE> {

	/**
	 * Upper bound on how many transitions are unrolled while searching for an inductive step. Placeholder constant,
	 * matching {@code InterpolationBasedModelChecking}; not yet wired through a preference.
	 */
	private static final int MAX_K = 200000;

	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final ManagedScript mWorkerMgdScript;
	private final KILock mKILock = new KILock();

	// Set by run() when the base case is satisfiable, reconstructed from mWitness by
	// KInductionCounterexampleBuilder.
	NestedRun<LETTER, STATE> mCounterexample;
	// What the model of the satisfiable base case said. Read in checkBase before its pop, null unless UNSAFE.
	private KInductionWitness mWitness;

	private final CfgSmtToolkit mCsToolkit;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private boolean mSolverReturnedUnknown;
	private boolean mSafe;
	private int mProvedK = -1;
	private Inconclusive mInconclusive;
	private final Map<CallNode<STATE>, Term> mLearnedInvariants = new LinkedHashMap<>();

	// Mirrors IMC's own worker-thread integration parameters, kept for structural consistency between the two
	// algorithms (and as a hook for future preference-driven configuration, e.g. bounding MAX_K); not otherwise
	// used, since k-induction needs no dedicated solver-mode selection.
	TaCheckAndRefinementPreferences<?> mPrefs;
	TaskIdentifier mTaskIdentifier;
	private final KInductionWorkerThread<?, ?> mKInductionWorkerThread;
	private final TAPreferences mPref;

	private final IInvariantSupplier<CallNode<STATE>> mInvariantSupplier;

	// Shared indexed-constant cache, reused across every push/pop-bracketed SAT query this instance ever issues -
	// safe because scopes are always cleanly popped between queries.
	private final Map<String, Term> mIndexedConstantsWorkerScript = new HashMap<>();

	private PcTransitionSystem<CallNode<STATE>> mSystem;
	// null unless the abstraction has calls, in which case it holds the resolved call sites
	private ProcedureSummaries<LETTER, STATE> mSummaries;
	private final List<Term> mStepTerms = new ArrayList<>();
	private StepVars mConstants;
	// pc node of a loop head -> its invariant, over the program variables' term variables
	private final Map<Integer, Term> mInjectedInvariants = new LinkedHashMap<>();
	private final Map<Integer, Map<IProgramVar, TermVariable>> mInjectedInvariantVars = new LinkedHashMap<>();

	public KInduction(final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences<?> prefs, final CfgSmtToolkit csToolkit,
			final INestedWordAutomaton<LETTER, STATE> abstraction, final TaskIdentifier taskIdentifier,
			final KInductionWorkerThread<?, ?> kInductionWorkerThread, final TAPreferences preferences,
			final IInvariantSupplier<CallNode<STATE>> invariantSupplier)
			throws AutomataLibraryException, InterruptedException {
		mAbstraction = abstraction;
		mCsToolkit = csToolkit;
		mWorkerMgdScript = csToolkit.getManagedScript();
		mLogger = logger;
		mServices = services;
		mTaskIdentifier = taskIdentifier;
		mPrefs = prefs;
		mKInductionWorkerThread = kInductionWorkerThread;
		mPref = preferences;
		mInvariantSupplier = invariantSupplier;
		run();
	}

	private enum Verdict {
		SAFE, UNSAFE, UNKNOWN
	}

	private void run() throws AutomataLibraryException {
		mLogger.info("KInduction: starting k-induction (MAX_K=%d)", MAX_K);
		// Building the loop tree composes transition formulas, which declares constants for their aux vars and thus
		// locks the script itself. So the tree has to be complete before we take the lock for the solver queries.
		final LoopTree<CallNode<STATE>> tree = buildLoopTree();
		mSystem = new PcTransitionSystem<>(tree);
		mLogger.info(
				"KInduction: transition system with %d pc value(s), %d transition(s), %d variable(s), %d loop head(s)",
				mSystem.getNumNodes(), mSystem.getNumTransitions(), mSystem.getVars().size(),
				mSystem.getHeadNodes().size());

		mWorkerMgdScript.lock(mKILock);
		try {
			mConstants = new ConstantVars();
			collectInvariants();

			final Verdict verdict = kInduction();
			mSafe = verdict == Verdict.SAFE;
			mSolverReturnedUnknown = verdict == Verdict.UNKNOWN;
			if (mSafe) {
				learnInvariants();
			} else if (verdict == Verdict.UNSAFE) {
				// Still under the lock, but after the base case's pop: reconstruction asserts terms, which would
				// invalidate the model we are working from. mWitness already holds everything we need from it.
				mCounterexample = new KInductionCounterexampleBuilder<LETTER, STATE>(mServices, mLogger,
						mWorkerMgdScript, mKILock, mCsToolkit, mAbstraction, mSystem, mWitness,
						mSummaries == null ? Collections.emptySet() : mSummaries.getSealedStates(),
						mSummaries == null ? Collections.emptySet() : mSummaries.getStackedProcedures()).build();
			}
		} finally {
			mWorkerMgdScript.unlock(mKILock);
		}
		mLogger.info("is safe " + mSafe);
		mLogger.info("solver returned unknown: " + mSolverReturnedUnknown);
	}

	/**
	 * The loop tree of the program. Its nodes are {@link CallNode}s: a state together with the call sites it was
	 * reached through. If the abstraction has no call transition every node is at depth zero and the tree is the
	 * whole automaton, as it always was. Otherwise every call site is first resolved by {@link ProcedureSummaries}
	 * - into a virtual call edge if the callee can be summarized, into an unfolded copy of the callee if it
	 * contains a loop - and the tree is built for the resulting graph, which has no call and no return transition
	 * left. A call that stayed in it would be unsound, see {@link LoopTreeFormulaBuilder}.
	 */
	private LoopTree<CallNode<STATE>> buildLoopTree() {
		final UnfoldedGraph<LETTER, STATE> graph = new UnfoldedGraph<>(mAbstraction);
		if (!hasCallTransitions()) {
			return new LoopTreeFormulaBuilder<>(mServices, mLogger, mWorkerMgdScript, graph,
					roots(mAbstraction.getStates()), roots(mAbstraction.getInitialStates()),
					roots(mAbstraction.getFinalStates()), Collections.emptyMap(), Collections.emptySet()).build();
		}
		mSummaries = new ProcedureSummaries<>(mServices, mLogger, mCsToolkit, mWorkerMgdScript, mAbstraction);
		return new LoopTreeFormulaBuilder<>(mServices, mLogger, mWorkerMgdScript, mSummaries.getGraph(),
				mSummaries.getScopeStates(), mSummaries.getInitStates(), mSummaries.getFinalStates(),
				mSummaries.getVirtualCallEdges(), mSummaries.getSealedStates()).build();
	}

	/** The given states as nodes with no pending call, for a program in which nothing is ever called. */
	private Set<CallNode<STATE>> roots(final Iterable<STATE> states) {
		final Set<CallNode<STATE>> result = new LinkedHashSet<>();
		for (final STATE state : states) {
			result.add(CallNode.root(state));
		}
		return result;
	}

	private boolean hasCallTransitions() {
		for (final STATE state : mAbstraction.getStates()) {
			if (mAbstraction.callSuccessors(state).iterator().hasNext()) {
				return true;
			}
		}
		return false;
	}

	private Verdict kInduction() {
		for (int k = 1; k <= MAX_K; k++) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass(), "k-induction at k=" + k);
			}
			final LBool base = checkBase(k);
			mLogger.info("KInduction: k=%d - base case: %s", k, base);
			if (base == LBool.SAT) {
				return Verdict.UNSAFE;
			}
			if (base == LBool.UNKNOWN) {
				mInconclusive = Inconclusive.solverUnknown(k, "base");
				return Verdict.UNKNOWN;
			}
			final LBool step = checkStep(k);
			mLogger.info("KInduction: k=%d - step case: %s", k, step);
			if (step == LBool.UNSAT) {
				mProvedK = k;
				return Verdict.SAFE;
			}
			if (step == LBool.UNKNOWN) {
				mInconclusive = Inconclusive.solverUnknown(k, "step");
				return Verdict.UNKNOWN;
			}
			// step case SAT: not yet inductive, unroll once more
		}
		mInconclusive = Inconclusive.boundExhausted(MAX_K);
		mLogger.info("KInduction: " + mInconclusive);
		return Verdict.UNKNOWN;
	}

	/**
	 * Is {@code pc = FINAL} reachable from {@code pc = INIT} in {@code k} transitions?
	 */
	private LBool checkBase(final int k) {
		final Script script = mWorkerMgdScript.getScript();
		final List<Term> invariants = prepare(k);
		mWorkerMgdScript.push(mKILock, 1);
		mWorkerMgdScript.assertTerm(mKILock,
				SmtUtils.binaryEquality(script, mConstants.pc(0), PcTransitionSystem.pcValue(script, PcTransitionSystem.INIT)));
		assertSteps(k);
		mWorkerMgdScript.assertTerm(mKILock, SmtUtils.binaryEquality(script, mConstants.pc(k),
				PcTransitionSystem.pcValue(script, PcTransitionSystem.FINAL)));
		for (final Term invariant : invariants) {
			mWorkerMgdScript.assertTerm(mKILock, invariant);
		}
		final LBool result = checkSat();
		if (result == LBool.SAT) {
			// The model dies with this scope, so it has to be read now. The constants themselves were declared by
			// prepare(k), i.e. outside the push, and survive the pop.
			mWitness = extractWitness(k);
			mLogger.info("KInduction: violation found, model says %s", mWitness);
		}
		mWorkerMgdScript.pop(mKILock, 1);
		return result;
	}

	/**
	 * Reads the model of a satisfiable base case. Must be called after {@code checkSat} returned {@code sat} and
	 * before the {@code pop} of that query.
	 */
	private KInductionWitness extractWitness(final int k) {
		final IProgramVar stackPointer = mSummaries == null ? null : mSummaries.getStackPointer();
		final List<Term> queried = new ArrayList<>();
		for (int j = 0; j <= k; j++) {
			queried.add(mConstants.pc(j));
		}
		for (int j = 0; j < k; j++) {
			queried.add(mConstants.sel(j));
		}
		if (stackPointer != null) {
			for (int j = 0; j <= k; j++) {
				queried.add(mConstants.var(stackPointer, j));
			}
		}

		final Map<Term, Term> model;
		try {
			// Not ManagedScript.getValue: SmtUtils normalizes what the solver returns, e.g. z3's (- 1) to -1.
			model = SmtUtils.getValues(mWorkerMgdScript.getScript(), queried);
		} catch (final UnsupportedOperationException e) {
			throw new UnsupportedOperationException("k-induction found a violation but the solver cannot produce a "
					+ "model, so no counterexample can be extracted. The worker's solver needs a mode that sets "
					+ ":produce-models (e.g. External_ModelsAndUnsatCoreMode, the default).", e);
		}

		final int[] pcValues = new int[k + 1];
		for (int j = 0; j <= k; j++) {
			pcValues[j] = intValue(model, mConstants.pc(j), "pc_" + j);
		}
		final int[] transitionIds = new int[k];
		for (int j = 0; j < k; j++) {
			transitionIds[j] = intValue(model, mConstants.sel(j), "selector_" + j);
		}
		int[] stackPointers = null;
		if (stackPointer != null) {
			stackPointers = new int[k + 1];
			for (int j = 0; j <= k; j++) {
				stackPointers[j] = intValue(model, mConstants.var(stackPointer, j), stackPointer + "_" + j);
			}
		}
		return new KInductionWitness(k, pcValues, transitionIds, stackPointers);
	}

	/**
	 * The pc and the transition selector are integers by construction, so anything else here means the model does
	 * not fit the encoding, which is a bug rather than an unsupported case.
	 */
	private static int intValue(final Map<Term, Term> model, final Term term, final String description) {
		final Term value = model.get(term);
		final Rational rational = value == null ? null : SmtUtils.tryToConvertToLiteral(value);
		if (rational == null || !rational.isIntegral()) {
			throw new AssertionError("the k-induction model gives " + value + " for " + description
					+ ", which is not an integer literal");
		}
		return rational.numerator().intValueExact();
	}

	/**
	 * Can {@code k} transitions from an arbitrary non-INIT state, with no error in the first {@code k} states,
	 * reach an error? UNSAT means the step is inductive.
	 */
	private LBool checkStep(final int k) {
		final Script script = mWorkerMgdScript.getScript();
		final List<Term> invariants = prepare(k);
		mWorkerMgdScript.push(mKILock, 1);
		mWorkerMgdScript.assertTerm(mKILock, SmtUtils.distinct(script, mConstants.pc(0),
				PcTransitionSystem.pcValue(script, PcTransitionSystem.INIT)));
		assertSteps(k);
		for (int j = 0; j < k; j++) {
			mWorkerMgdScript.assertTerm(mKILock, SmtUtils.distinct(script, mConstants.pc(j),
					PcTransitionSystem.pcValue(script, PcTransitionSystem.FINAL)));
		}
		mWorkerMgdScript.assertTerm(mKILock, SmtUtils.binaryEquality(script, mConstants.pc(k),
				PcTransitionSystem.pcValue(script, PcTransitionSystem.FINAL)));
		for (final Term invariant : invariants) {
			mWorkerMgdScript.assertTerm(mKILock, invariant);
		}
		final LBool result = checkSat();
		mWorkerMgdScript.pop(mKILock, 1);
		return result;
	}

	private LBool checkSat() {
		return mWorkerMgdScript.checkSat(mKILock);
	}

	/**
	 * Builds everything that declares constants (the steps up to {@code k}, the pc constants and the invariants).
	 * This has to happen before the {@code push} of a query: constants declared inside are forgotten by the solver
	 * on {@code pop}, but stay in {@link #mIndexedConstantsWorkerScript}.
	 *
	 * @return the invariant assertions for the states {@code 0..k}
	 */
	private List<Term> prepare(final int k) {
		while (mStepTerms.size() < k) {
			mStepTerms.add(mSystem.step(mStepTerms.size(), mConstants, mWorkerMgdScript));
		}
		for (int j = 0; j <= k; j++) {
			mConstants.pc(j);
		}
		return invariantAssertions(k);
	}

	private void assertSteps(final int k) {
		for (int j = 0; j < k; j++) {
			mWorkerMgdScript.assertTerm(mKILock, mStepTerms.get(j));
		}
	}

	// ------------------------------------------------------------------------------------------------------------
	// Invariant injection
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * Asks the supplier for an invariant of every loop head and keeps those that only mention variables of the
	 * transition system.
	 */
	private void collectInvariants() {
		final Map<TermVariable, IProgramVar> varOfTermVariable = new HashMap<>();
		for (final IProgramVar pv : mSystem.getVars()) {
			varOfTermVariable.put(pv.getTermVariable(), pv);
		}
		for (final Map.Entry<CallNode<STATE>, Integer> head : mSystem.getHeadNodes().entrySet()) {
			final Optional<Term> invariant = mInvariantSupplier.getInvariant(head.getKey(), mWorkerMgdScript);
			if (invariant.isEmpty()) {
				continue;
			}
			final Map<IProgramVar, TermVariable> used = new LinkedHashMap<>();
			boolean usable = true;
			for (final TermVariable tv : invariant.get().getFreeVars()) {
				final IProgramVar pv = varOfTermVariable.get(tv);
				if (pv == null) {
					usable = false;
					mLogger.info("KInduction: ignoring invariant of loop head %s, it mentions %s which occurs in "
							+ "no transition", head.getKey(), tv);
					break;
				}
				used.put(pv, tv);
			}
			if (usable) {
				mInjectedInvariants.put(head.getValue(), invariant.get());
				mInjectedInvariantVars.put(head.getValue(), used);
				mLogger.info("KInduction: using invariant of loop head %s: %s", head.getKey(), invariant.get());
			}
		}
	}

	/**
	 * For every step {@code 0..k}: if the pc is a loop head with an invariant, the invariant holds. Returns the assertions.
	 */
	private List<Term> invariantAssertions(final int k) {
		final List<Term> result = new ArrayList<>();
		final Script script = mWorkerMgdScript.getScript();
		for (final Map.Entry<Integer, Term> entry : mInjectedInvariants.entrySet()) {
			for (int j = 0; j <= k; j++) {
				final Map<Term, Term> substitution = new HashMap<>();
				for (final Map.Entry<IProgramVar, TermVariable> var : mInjectedInvariantVars.get(entry.getKey())
						.entrySet()) {
					substitution.put(var.getValue(), mConstants.var(var.getKey(), j));
				}
				final Term instantiated = PureSubstitution.apply(mWorkerMgdScript, substitution, entry.getValue());
				final Term atHead = SmtUtils.binaryEquality(script, mConstants.pc(j),
						PcTransitionSystem.pcValue(script, entry.getKey()));
				result.add(SmtUtils.implies(script, atHead, instantiated));
			}
		}
		return result;
	}

	// ------------------------------------------------------------------------------------------------------------
	// Learned invariants
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * For every loop head {@code h}: not (exists a run of {@link #mProvedK} transitions from {@code h} that ends in
	 * FINAL), over the term variables of the program variables.
	 */
	private void learnInvariants() {
		final Script script = mWorkerMgdScript.getScript();
		for (final Map.Entry<CallNode<STATE>, Integer> head : mSystem.getHeadNodes().entrySet()) {
			final FreshVars vars = new FreshVars(head.getValue());
			final List<Term> conjuncts = new ArrayList<>();
			for (int j = 0; j < mProvedK; j++) {
				conjuncts.add(mSystem.step(j, vars, mWorkerMgdScript));
			}
			conjuncts.add(SmtUtils.binaryEquality(script, vars.pc(mProvedK),
					PcTransitionSystem.pcValue(script, PcTransitionSystem.FINAL)));
			final Term reachError = SmtUtils.quantifier(script, QuantifiedFormula.EXISTS, vars.getFreshVariables(),
					SmtUtils.and(script, conjuncts));
			mLearnedInvariants.put(head.getKey(), SmtUtils.not(script, reachError));
		}
		mLogger.info("KInduction: learned an invariant for %d loop head(s) from k=%d", mLearnedInvariants.size(),
				mProvedK);
	}

	/**
	 * Unrolling with constants, for solver queries. Auxiliary variables are separate constants per transition and
	 * step, so different steps do not share their values.
	 */
	private final class ConstantVars implements StepVars {
		private final Sort mPcSort = PcTransitionSystem.pcValue(mWorkerMgdScript.getScript(), 0).getSort();

		@Override
		public Term var(final IProgramVar pv, final int idx) {
			return PredicateUtils.getIndexedConstant(pv, idx, mIndexedConstantsWorkerScript,
					mWorkerMgdScript.getScript());
		}

		@Override
		public Term pc(final int idx) {
			return PredicateUtils.getIndexedConstant("kipc", mPcSort, idx, mIndexedConstantsWorkerScript,
					mWorkerMgdScript.getScript());
		}

		@Override
		public Term aux(final int transitionId, final TermVariable auxVar, final int idx) {
			return PredicateUtils.getIndexedConstant("kiaux_" + transitionId + "_" + auxVar.getName(),
					auxVar.getSort(), idx, mIndexedConstantsWorkerScript, mWorkerMgdScript.getScript());
		}

		@Override
		public Term sel(final int idx) {
			return PredicateUtils.getIndexedConstant("kisel", mPcSort, idx, mIndexedConstantsWorkerScript,
					mWorkerMgdScript.getScript());
		}
	}

	/**
	 * Unrolling with fresh term variables, for a formula with quantifiers. Step 0 is the loop head {@code node} with
	 * the program variables' own term variables (the convention of {@link IInvariantSupplier}); all later steps and
	 * auxiliary variables are fresh and are to be quantified, see {@link #getFreshVariables()}.
	 */
	private final class FreshVars implements StepVars {
		private final int mNode;
		private final Map<String, TermVariable> mFresh = new LinkedHashMap<>();
		private final Set<TermVariable> mFreshVariables = new LinkedHashSet<>();

		FreshVars(final int node) {
			mNode = node;
		}

		Set<TermVariable> getFreshVariables() {
			return mFreshVariables;
		}

		private TermVariable fresh(final String key, final Sort sort) {
			return mFresh.computeIfAbsent(key, k -> {
				final TermVariable tv = mWorkerMgdScript.constructFreshTermVariable("ki", sort);
				mFreshVariables.add(tv);
				return tv;
			});
		}

		@Override
		public Term var(final IProgramVar pv, final int idx) {
			if (idx == 0) {
				return pv.getTermVariable();
			}
			return fresh("v_" + pv.getGloballyUniqueId() + "_" + idx, pv.getTermVariable().getSort());
		}

		@Override
		public Term pc(final int idx) {
			final Script script = mWorkerMgdScript.getScript();
			if (idx == 0) {
				return PcTransitionSystem.pcValue(script, mNode);
			}
			return fresh("pc_" + idx, PcTransitionSystem.pcValue(script, 0).getSort());
		}

		@Override
		public Term aux(final int transitionId, final TermVariable auxVar, final int idx) {
			return fresh("aux_" + transitionId + "_" + auxVar.getName() + "_" + idx, auxVar.getSort());
		}
	}

	public boolean isSafe() {
		return mSafe;
	}

	public boolean wasUnkown() {
		return mSolverReturnedUnknown;
	}

	/**
	 * @return why k-induction ended without a verdict. Only defined if {@link #wasUnkown()}.
	 */
	public Inconclusive getInconclusive() {
		if (mInconclusive == null) {
			throw new UnsupportedOperationException(
					"k-induction was not inconclusive, so there is no reason to report");
		}
		return mInconclusive;
	}

	/**
	 * Why k-induction stopped without proving or refuting the program. The two possibilities are kept apart because
	 * they call for opposite remedies: an exhausted unrolling bound means the search was cut short and a larger
	 * bound might still decide it, whereas a solver that answers {@code unknown} will keep doing so until the query
	 * itself changes (fewer variables, a different encoding, an injected invariant, or a higher resource limit).
	 */
	public static final class Inconclusive {
		private final int mK;
		private final String mCase;

		private Inconclusive(final int k, final String theCase) {
			mK = k;
			mCase = theCase;
		}

		static Inconclusive solverUnknown(final int k, final String theCase) {
			return new Inconclusive(k, theCase);
		}

		static Inconclusive boundExhausted(final int maxK) {
			return new Inconclusive(maxK, null);
		}

		/**
		 * @return true if the unrolling bound was reached, false if the solver gave up first.
		 */
		public boolean isBoundExhausted() {
			return mCase == null;
		}

		public int getK() {
			return mK;
		}

		/**
		 * @return "base" or "step". Only defined unless {@link #isBoundExhausted()}.
		 */
		public String getCase() {
			return mCase;
		}

		@Override
		public String toString() {
			if (isBoundExhausted()) {
				return "k-induction reached the unrolling bound MAX_K=" + mK
						+ " without an inductive step; neither a proof nor a violation was found";
			}
			return "k-induction is inconclusive: the solver returned unknown for the " + mCase + " case at k=" + mK
					+ ", so the program is neither proved safe nor refuted";
		}
	}

	/**
	 * @return for every loop head, an invariant learned from the k-induction proof (empty unless the program was
	 *         proven safe). The terms are native to the worker's {@link ManagedScript}.
	 */
	public Map<CallNode<STATE>, Term> getLearnedInvariants() {
		return Collections.unmodifiableMap(mLearnedInvariants);
	}

	/**
	 * @return {@link #getLearnedInvariants()} as a supplier, for use as the invariants of another run.
	 */
	public IInvariantSupplier<CallNode<STATE>> getLearnedInvariantSupplier() {
		return IInvariantSupplier.fromMap(mLearnedInvariants, mWorkerMgdScript);
	}

	/**
	 * @return a run of the abstraction that reaches an accepting state and is feasible, i.e. a genuine
	 *         counterexample. Only defined if k-induction refuted the program.
	 */
	public NestedRun<LETTER, STATE> getCounterexample() {
		if (mSafe || mSolverReturnedUnknown) {
			throw new UnsupportedOperationException("k-induction did not refute the program, so there is no "
					+ "counterexample");
		}
		if (mCounterexample == null) {
			throw new IllegalStateException("k-induction refuted the program but no counterexample was built; "
					+ "KInductionCounterexampleBuilder must either return a run or throw");
		}
		return mCounterexample;
	}

	/**
	 * Package private class used by KInduction to lock the {@link ManagedScript}.
	 */
	static class KILock {
	}
}
