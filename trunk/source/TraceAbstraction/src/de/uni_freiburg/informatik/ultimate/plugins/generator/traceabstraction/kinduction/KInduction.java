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

	// TODO: on SAT, a concrete witness path is not yet extracted; left unset. See run(). Same gap as IMC's own
	// mCounterexample.
	NestedRun<LETTER, STATE> mCounterexample;

	private final CfgSmtToolkit mCsToolkit;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private boolean mSolverReturnedUnknown;
	private boolean mSafe;
	private int mProvedK = -1;
	private final Map<STATE, Term> mLearnedInvariants = new LinkedHashMap<>();

	// Mirrors IMC's own worker-thread integration parameters, kept for structural consistency between the two
	// algorithms (and as a hook for future preference-driven configuration, e.g. bounding MAX_K); not otherwise
	// used, since k-induction needs no dedicated solver-mode selection.
	TaCheckAndRefinementPreferences<?> mPrefs;
	TaskIdentifier mTaskIdentifier;
	private final KInductionWorkerThread<?, ?> mKInductionWorkerThread;
	private final TAPreferences mPref;

	private final IInvariantSupplier<STATE> mInvariantSupplier;

	// Shared indexed-constant cache, reused across every push/pop-bracketed SAT query this instance ever issues -
	// safe because scopes are always cleanly popped between queries.
	private final Map<String, Term> mIndexedConstantsWorkerScript = new HashMap<>();

	private PcTransitionSystem<STATE> mSystem;
	private final List<Term> mStepTerms = new ArrayList<>();
	private StepVars mConstants;
	// pc node of a loop head -> its invariant, over the program variables' term variables
	private final Map<Integer, Term> mInjectedInvariants = new LinkedHashMap<>();
	private final Map<Integer, Map<IProgramVar, TermVariable>> mInjectedInvariantVars = new LinkedHashMap<>();

	public KInduction(final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences<?> prefs, final CfgSmtToolkit csToolkit,
			final INestedWordAutomaton<LETTER, STATE> abstraction, final TaskIdentifier taskIdentifier,
			final KInductionWorkerThread<?, ?> kInductionWorkerThread, final TAPreferences preferences,
			final IInvariantSupplier<STATE> invariantSupplier) throws AutomataLibraryException, InterruptedException {
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
		final LoopTree<STATE> tree =
				new LoopTreeFormulaBuilder<>(mServices, mLogger, mWorkerMgdScript, mAbstraction).build();
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
			}
		} finally {
			mWorkerMgdScript.unlock(mKILock);
		}
		mLogger.info("is safe " + (mSafe && !mSolverReturnedUnknown));
		mLogger.info("solver returned unknown: " + mSolverReturnedUnknown);
	}

	private Verdict kInduction() {
		for (int k = 1; k <= MAX_K; k++) {
			final LBool base = checkBase(k);
			mLogger.info("KInduction: k=%d - base case: %s", k, base);
			if (base == LBool.SAT) {
				return Verdict.UNSAFE;
			}
			if (base == LBool.UNKNOWN) {
				return Verdict.UNKNOWN;
			}
			final LBool step = checkStep(k);
			mLogger.info("KInduction: k=%d - step case: %s", k, step);
			if (step == LBool.UNSAT) {
				mProvedK = k;
				return Verdict.SAFE;
			}
			if (step == LBool.UNKNOWN) {
				return Verdict.UNKNOWN;
			}
			// step case SAT: not yet inductive, unroll once more
		}
		mLogger.info("KInduction: reached MAX_K=%d without an inductive step", MAX_K);
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
		final LBool result = mWorkerMgdScript.checkSat(mKILock);
		mWorkerMgdScript.pop(mKILock, 1);
		return result;
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
		final LBool result = mWorkerMgdScript.checkSat(mKILock);
		mWorkerMgdScript.pop(mKILock, 1);
		return result;
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
		for (final Map.Entry<STATE, Integer> head : mSystem.getHeadNodes().entrySet()) {
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
		for (final Map.Entry<STATE, Integer> head : mSystem.getHeadNodes().entrySet()) {
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

	public boolean wasOverapproximated() {
		return mSolverReturnedUnknown;
	}

	public boolean wasUnkown() {
		return mSolverReturnedUnknown;
	}

	/**
	 * @return for every loop head, an invariant learned from the k-induction proof (empty unless the program was
	 *         proven safe). The terms are native to the worker's {@link ManagedScript}.
	 */
	public Map<STATE, Term> getLearnedInvariants() {
		return Collections.unmodifiableMap(mLearnedInvariants);
	}

	/**
	 * @return {@link #getLearnedInvariants()} as a supplier, for use as the invariants of another run.
	 */
	public IInvariantSupplier<STATE> getLearnedInvariantSupplier() {
		return IInvariantSupplier.fromMap(mLearnedInvariants, mWorkerMgdScript);
	}

	public NestedRun<LETTER, STATE> getCounterexample() {
		assert !mSafe;
		if (mCounterexample == null) {
			throw new UnsupportedOperationException("KInduction found a violation, but extracting a counterexample "
					+ "run is not implemented yet");
		}
		return mCounterexample;
	}

	/**
	 * Package private class used by KInduction to lock the {@link ManagedScript}.
	 */
	static class KILock {
	}
}
