package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.LoopSegmentFormulaBuilder.LoopSegments;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

public class InterpolationBasedModelChecking<LETTER extends IAction, STATE> {

	/**
	 * Upper bound on how many times the loop body is unwound while searching for an inductive interpolant. Placeholder
	 * constant; not yet wired through a preference.
	 */
	private static final int MAX_K = 20;

	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final ManagedScript mMgdImcScript;
	protected final IMCLock mIMCLock = new IMCLock();
	protected final STATE mDummyEmptyStackState;

	// TODO: on SAT, a concrete witness path is not yet extracted; left unset. See run().
	NestedRun<LETTER, STATE> mCounterexample;

	// this stuff is needed only for asserting / ssa
	private final CfgSmtToolkit mCsToolkit;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private boolean mSolverReturnedUnknown;
	private boolean mSafe;

	// TC Solver setup
	TaCheckAndRefinementPreferences<?> mPrefs;
	TaskIdentifier mTaskIdentifier = null;
	private final InterpolModelCheckingWorkerThread mImcWorkerThread;
	private final ManagedScript mWorkerMgdScript;
	private final TAPreferences mPref;

	// naming for interpolation
	private int mNameCounter;
	private Map<Term, IProgramVar> mConstants2BoogieVar;
	// Transfers terms from IMC's own interpolation-capable script (mMgdScript) back to the worker's script
	// (mWorkerMgdScript), whose symbol table holds the real IProgramVars the rest of the worker recognizes.
	private final TermTransferrer mImc2Worker;
	private final TermTransferrer mWorker2Imc;

	/**
	 *
	 * @param csToolkit
	 * @param logger
	 * @param services
	 * @param preferences
	 * @throws InterruptedException
	 * @throws AutomataLibraryException
	 *
	 */
	public InterpolationBasedModelChecking(final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences prefs, final CfgSmtToolkit csToolkit,
			final INestedWordAutomaton<LETTER, STATE> abstraction, final TaskIdentifier taskIdentifier,
			final InterpolModelCheckingWorkerThread imcWorkerThread, final TAPreferences preferences)
			throws AutomataLibraryException, InterruptedException {
		mAbstraction = abstraction;
		mDummyEmptyStackState = mAbstraction.getEmptyStackState();
		mCsToolkit = csToolkit;
		mWorkerMgdScript = csToolkit.getManagedScript();
		mLogger = logger;
		mServices = services;
		mTaskIdentifier = taskIdentifier;
		mPrefs = prefs;
		mImcWorkerThread = imcWorkerThread;
		mMgdImcScript = csToolkit.createFreshManagedScript(mServices, getSolverSetting(), "IMC");
		mImc2Worker = new TermTransferrer(mMgdImcScript.getScript(), mWorkerMgdScript.getScript());
		mWorker2Imc = new TermTransferrer(mWorkerMgdScript.getScript(), mMgdImcScript.getScript());
		mPref = preferences;
		run();
	}

	/**
	 * Runs bounded-unwinding Interpolation-Based Model Checking on a nested word automaton (path program or
	 * abstraction) that represents a program with exactly one loop.
	 *
	 * The three region summaries (prefix / one loop-body pass / suffix), each covering <b>all</b> paths through their
	 * region, come from {@link LoopSegmentFormulaBuilder}. For k = 1, 2, ..., MAX_K: assert prefix &and; loop^k &and;
	 * suffix as SSA, named per region. If SAT, a real bug was found. If UNSAT, obtain the k+1 cut-point interpolants;
	 * if the newest one is already subsumed by the disjunction of the earlier ones, the loop-head reachable set has
	 * stabilized (a valid, sound stopping criterion since iterations 1..k were each individually confirmed infeasible
	 * already) and the program is safe.
	 */
	private void run() throws AutomataLibraryException {
		mMgdImcScript.lock(mIMCLock);
		mLogger.info("IMC: starting bounded-unwinding interpolation-based model checking (MAX_K=%d)", MAX_K);

		final LoopSegments segments =
				new LoopSegmentFormulaBuilder<>(mServices, mLogger, mWorkerMgdScript, mAbstraction).build();
		mLogger.info("IMC: loop segment formulas ready, starting unwinding loop");

		for (int k = 1; k <= MAX_K; k++) {
			mLogger.info("IMC: k=%d - asserting prefix, %d copies of loop body, suffix", k, k);
			mMgdImcScript.push(mIMCLock, 1);

			final List<UnmodifiableTransFormula> regions = new ArrayList<>();
			regions.add(segments.getPrefix());
			regions.addAll(Collections.nCopies(k, segments.getLoopBody()));
			regions.add(segments.getSuffix());

			final Term[] partition = assertRegionSequenceNamed(regions);
			final LBool sat = mMgdImcScript.checkSat(mIMCLock);
			mLogger.info("IMC: k=%d - solver result: %s", k, sat);

			if (sat == LBool.SAT) {
				mSafe = false;
				mLogger.info("IMC: k=%d - feasible counterexample found, program is unsafe", k);
				mMgdImcScript.pop(mIMCLock, 1);
				break;
			}
			if (sat == LBool.UNKNOWN) {
				mSolverReturnedUnknown = true;
				mSafe = false;
				mLogger.info("IMC: k=%d - solver returned unknown, aborting", k);
				mMgdImcScript.pop(mIMCLock, 1);
				break;
			}

			// UNSAT: extract the k+1 cut-point interpolants before popping the scope
			final Term[] interpolants = mMgdImcScript.getInterpolants(mIMCLock, partition);
			mLogger.info("IMC: k=%d - obtained %d cut-point interpolants", k, interpolants.length);
			final Term[] cutpointPreds = unSsaToRepresentativeFrame(interpolants);
			mMgdImcScript.pop(mIMCLock, 1);

			if (hasStabilized(cutpointPreds, k)) {
				mSafe = true;
				mLogger.info("IMC: k=%d - interpolant sequence stabilized, program is safe", k);
				break;
			}
			mLogger.info("IMC: k=%d - interpolant sequence has not stabilized yet", k);
			if (k == MAX_K) {
				mSolverReturnedUnknown = true;
				mSafe = false;
				mLogger.info("IMC: reached MAX_K=%d without stabilizing or finding a bug", MAX_K);
			}
		}

		mMgdImcScript.unlock(mIMCLock);
		mLogger.info("is safe " + (mSafe && !mSolverReturnedUnknown));
		mLogger.info("solver returned unknown: " + mSolverReturnedUnknown);
	}

	private SolverSettings getSolverSetting() {
		final SolverSettings setting;
		switch (mPrefs.getRefinementStrategy()) {
		case RefinementStrategy.CAMEL: {
			setting = mPrefs.constructSolverSettings(mTaskIdentifier).setSolverMode(SolverMode.Internal_SMTInterpol)
					.setSmtInterpolTimeout(900000);
			break;
		}
//		case RefinementStrategy.FOX: {
//			setting = mPrefs.constructSolverSettings(new SubtaskIterationIdentifier(mTaskIdentifier, 1))
//					.setUseExternalSolver(ExternalSolver.MATHSAT)
//					.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode);
//			break;
//		}
		default: {
//			setting = mPrefs.constructSolverSettings(new SubtaskIterationIdentifier(mTaskIdentifier, 1))
//					.setUseExternalSolver(ExternalSolver.CVC5)
//					.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode);
			throw new AssertionError("Only Native SMT Interpol im integer mode (CAMEL) supported");
		}
		}
		return setting;
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

	public NestedRun<LETTER, STATE> getCounterexample() {
		assert !mSafe;
		return mCounterexample;
	}

	/**
	 * SSA-chains {@code regions} (already {@code mMgdScript}-native {@link UnmodifiableTransFormula}s, one per
	 * interpolation partition) into a sequence of named ({@code :named}) SMT assertions via
	 * {@link PredicateUtils#formulaWithIndexedVars} — region {@code s}'s inVars are renamed to index {@code s} and its
	 * genuinely-updated outVars to index {@code s + 1}, via a shared indexed-constant cache, so consecutive regions'
	 * matching in/out vars land on the same constant automatically. The {@code :named} constant for region {@code s}
	 * becomes {@code partition[s]} directly. Also refreshes {@link #mConstants2BoogieVar} so
	 * {@link #unSsaToRepresentativeFrame} can un-SSA the resulting interpolants.
	 *
	 * Assumes procedures are inlined (no oldvars / calling contexts to special-case).
	 */
	private Term[] assertRegionSequenceNamed(final List<UnmodifiableTransFormula> regions) {
		final Map<String, Term> indexedConstants = new HashMap<>();
		mConstants2BoogieVar = new HashMap<>();
		final Term[] partition = new Term[regions.size()];
		for (int s = 0; s < regions.size(); s++) {
			final UnmodifiableTransFormula region = regions.get(s);
			final int idxInVar = s;
			final int idxOutVar = s + 1;
			final Set<IProgramVar> assignedVars = new HashSet<>();
			Term ssaFormula = PredicateUtils.formulaWithIndexedVars(region, idxInVar, idxOutVar, assignedVars,
					indexedConstants, mWorkerMgdScript.getScript());
			ssaFormula = mWorker2Imc.transform(ssaFormula);

			// Mirrors formulaWithIndexedVars' own constant choice per var exactly (oldvars use their stable default
			// constant instead of an indexed one) so mConstants2BoogieVar always maps the constant that actually
			// occurs in ssaFormula, not a freshly-minted one nobody references. Not expected to trigger while
			// procedures are assumed inlined, but cheap to keep correct in case an oldvar slips through.
			for (final IProgramVar pv : region.getInVars().keySet()) {
				final Term constant = pv.isOldvar() ? pv.getDefaultConstant()
						: PredicateUtils.getIndexedConstant(pv, idxInVar, indexedConstants,
								mWorkerMgdScript.getScript());
				mConstants2BoogieVar.put(mWorker2Imc.transform(constant), pv);
			}
			for (final IProgramVar pv : assignedVars) {
				final Term constant = pv.isOldvar() && !region.getAssignedVars().contains(pv) ? pv.getDefaultConstant()
						: PredicateUtils.getIndexedConstant(pv, idxOutVar, indexedConstants,
								mWorkerMgdScript.getScript());
				mConstants2BoogieVar.put(mWorker2Imc.transform(constant), pv);
			}
			partition[s] = SmtUtils.annotateAndAssert(mMgdImcScript.getScript(), ssaFormula, "imc" + s);
		}
		// SmtUtils.interpolateBinary(, partition[0], partition[1]);
		return partition;
	}

	/**
	 * Maps every SSA constant back to its program variable's own canonical, non-indexed
	 * {@link IProgramVar#getTermVariable()}, so that cut-point interpolants obtained at different loop-copy positions
	 * become directly comparable formulas over the same variable frame. Interpolants come back from
	 * {@code mMgdScript.getInterpolants} native to IMC's own script; {@code pv.getTermVariable()} is native to the
	 * worker's script ({@link #mWorkerMgdScript}), since {@code pv} is one of {@link LoopSegmentFormulaBuilder}'s
	 * unmodified, worker-native {@code IProgramVar}s. Substituting one script's term into a formula native to the other
	 * would silently build a mismatched term tree, so the interpolant (and the SSA constants it's keyed on) is
	 * transferred into the worker's script via {@link #mImc2Worker} first; only then does the substitution and the
	 * resulting predicate live consistently in {@link #mWorkerMgdScript}, matching what {@code mCsToolkit}'s symbol
	 * table actually has registered.
	 */
	private Term[] unSsaToRepresentativeFrame(final Term[] interpolants) {
		final Map<Term, Term> const2RepTv = new HashMap<>();
		for (final Map.Entry<Term, IProgramVar> entry : mConstants2BoogieVar.entrySet()) {
			// entry comes from imc script
			final Term transferredConstant = mImc2Worker.transform(entry.getKey());
			const2RepTv.put(transferredConstant, mImc2Worker.transform(entry.getValue().getDefaultConstant()));
		}
		final Term[] result = new Term[interpolants.length];
		for (int i = 0; i < interpolants.length; i++) {
			final Term unlet = new FormulaUnLet().transform(interpolants[i]);
			final Term transferred = mImc2Worker.transform(unlet);
			final Term representative = PureSubstitution.apply(mWorkerMgdScript, const2RepTv, transferred);
			result[i] = representative;
		}
		return result;
	}

	/**
	 * {@code cutpointPreds[j]} over-approximates the loop-head state after {@code j} loop iterations
	 * ({@code j = 0..k}). If the newest layer is already subsumed by the union (disjunction) of all earlier layers, no
	 * further unwinding can discover new abstract states at the loop head: the union is an inductive invariant, and
	 * since iterations {@code 1..k} were each individually confirmed infeasible by the caller already, the program is
	 * safe.
	 */
	private boolean hasStabilized(final Term[] unSSAdInterpolants, final int k) {
		final List<Term> earlierLayers = new ArrayList<>(k);
		for (int j = 0; j < k; j++) {
			earlierLayers.add(unSSAdInterpolants[j]);
		}
		final Term union = SmtUtils.or(mWorkerMgdScript.getScript(), earlierLayers);
		return isUnsat(unSSAdInterpolants[k], SmtUtils.not(mWorkerMgdScript.getScript(), union));
	}

	/**
	 * {@code cutpointPreds} are native to {@link #mWorkerMgdScript} (see {@link #unSsaToRepresentativeFrame}), not
	 * {@link #mMgdImcScript}, so the check runs there instead. Unlike {@code mMgdScript} (locked once for the whole
	 * {@link #run()} duration), {@link #mWorkerMgdScript} isn't held by an outer lock here, so this brackets its own
	 * lock/unlock — {@link #mIMCLock} is reused purely as an owner token, independently of which script it's used to
	 * lock.
	 */
	private boolean isUnsat(final Term... conjuncts) {
		mWorkerMgdScript.lock(mIMCLock);
		mWorkerMgdScript.push(mIMCLock, 1);
		for (final Term t : conjuncts) {
			mWorkerMgdScript.assertTerm(mIMCLock, t);
		}
		final LBool result = mWorkerMgdScript.checkSat(mIMCLock);
		mWorkerMgdScript.pop(mIMCLock, 1);
		mWorkerMgdScript.unlock(mIMCLock);
		return result == LBool.UNSAT;
	}

	/**
	 * Package private class used by IMC to lock the {@link ManagedScript}.
	 */
	static class IMCLock {
	}
}
