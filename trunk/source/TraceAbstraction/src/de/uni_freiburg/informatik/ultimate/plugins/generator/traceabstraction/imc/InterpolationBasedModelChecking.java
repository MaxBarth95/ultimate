package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc;

import java.util.ArrayList;
import java.util.Arrays;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.CheckpointGraphFormulaBuilder.Checkpoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.CheckpointGraphFormulaBuilder.CheckpointGraph;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

public class InterpolationBasedModelChecking<LETTER extends IAction, STATE> {

	/**
	 * Upper bound on how many times the loop body is unwound while searching for an inductive interpolant. Placeholder
	 * constant; not yet wired through a preference.
	 */
	private static final int MAX_K = 200000;

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
	final Map<String, Term> mIndexedConstantsWorkerScript = new HashMap<>();

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
	 * Result of checking one INIT-to-FINAL path through the checkpoint graph (see {@link #runPath}). Package-visible
	 * (not {@code private}) so {@link InterproceduralImcOrchestrator} can aggregate verdicts across procedures.
	 */
	enum PathVerdict {
		SAFE, UNSAFE, UNKNOWN
	}

	/**
	 * {@link #runPath}'s result: the verdict, plus - only when {@code verdict == SAFE} - the concrete region chain
	 * that proved it (the same chain already asserted/checked, exposed rather than discarded). This is what lets
	 * {@link InterproceduralImcOrchestrator} reuse the exact formulas already proven for one path (including any
	 * {@link #buildLoopInvariantSummary} regions) when composing a procedure summary, instead of recomputing a
	 * second, separate approximation.
	 */
	static final class PathResult {
		final PathVerdict verdict;
		final List<UnmodifiableTransFormula> provenRegionChain;

		private PathResult(final PathVerdict verdict, final List<UnmodifiableTransFormula> provenRegionChain) {
			this.verdict = verdict;
			this.provenRegionChain = provenRegionChain;
		}

		static PathResult safe(final List<UnmodifiableTransFormula> regionChain) {
			return new PathResult(PathVerdict.SAFE, regionChain);
		}

		static PathResult unsafe() {
			return new PathResult(PathVerdict.UNSAFE, null);
		}

		static PathResult unknown() {
			return new PathResult(PathVerdict.UNKNOWN, null);
		}
	}

	/**
	 * Runs bounded-unwinding Interpolation-Based Model Checking across the whole (non-recursive) call graph of a
	 * nested word automaton (path program or abstraction) that represents a program with any number of non-nested
	 * loops and any number of non-recursive function calls.
	 * <p>
	 * The actual per-procedure orchestration - building each procedure's checkpoint graph
	 * ({@link CheckpointGraphFormulaBuilder}), checking every INIT-to-FINAL path on it via {@link #runPath}, and
	 * composing proven-safe paths into a callee's summary for its callers - is
	 * {@link InterproceduralImcOrchestrator}'s job; recursion is rejected up front by
	 * {@link ProcedureCallGraph} (a virtual call edge needs its callee's summary to already exist, which is
	 * undefined for a cycle). This method just drives that orchestrator once and translates its aggregated
	 * {@link PathVerdict} into {@link #mSafe}/{@link #mSolverReturnedUnknown}.
	 */
	private void run() throws AutomataLibraryException {
		mMgdImcScript.lock(mIMCLock);
		mLogger.info("IMC: starting bounded-unwinding interpolation-based model checking (MAX_K=%d)", MAX_K);

		final InterproceduralImcOrchestrator<LETTER, STATE> orchestrator = new InterproceduralImcOrchestrator<>(
				mServices, mLogger, mCsToolkit, mWorkerMgdScript, mAbstraction, this::runPath);
		final PathVerdict overall = orchestrator.run();

		mSafe = overall == PathVerdict.SAFE;
		mSolverReturnedUnknown = overall == PathVerdict.UNKNOWN;

		mMgdImcScript.unlock(mIMCLock);
		mLogger.info("is safe " + (mSafe && !mSolverReturnedUnknown));
		mLogger.info("solver returned unknown: " + mSolverReturnedUnknown);
	}

	/**
	 * Checks one INIT-to-FINAL path through the checkpoint graph. If the path has no loop head at all, this is a single
	 * plain SAT check on its one edge formula. Otherwise the loop heads on the path are processed in order, one "phase"
	 * per loop head: phase {@code p} sweeps {@code k_p = 1..MAX_K} for loop head {@code p}, with every later loop head
	 * on the path taken exactly one mandatory pass for the purpose of {@link #hasStabilized}'s search (it hasn't been
	 * reached yet). Each sweep step reuses exactly the same push/{@link #assertRegionSequenceNamed}/checkSat/
	 * {@link #hasStabilized} machinery the single-loop case already used, just with a longer, phase-appropriate region
	 * chain.
	 * <p>
	 * Once phase {@code p} stabilizes, every earlier loop head is <em>not</em> frozen at the concrete iteration count
	 * that happened to make its own phase stabilize - that would only prove safety for that one arbitrary count,
	 * silently missing a bug that needs a different one. Instead {@link #buildLoopInvariantSummary} turns the just-proven
	 * inductive invariant into a "havoc, then assume" region, carrying forward the fact that it holds after <em>any</em>
	 * number of iterations {@code n >= 0} (not just {@code k_p}) - see that method's javadoc for why over- rather than
	 * under-approximating variables the invariant doesn't mention is the sound choice. This is what makes later phases
	 * sound for "this loop ran any number of times", not just one lucky value.
	 * <p>
	 * <b>Soundness</b>: an {@link PathVerdict#UNSAFE} verdict is always backed by one concrete, directly re-checkable SAT
	 * region chain for the loop head currently being swept - so it is sound with respect to <em>this program</em>
	 * whenever no earlier loop head's invariant summary over-approximates by havocking a variable the bug actually
	 * depends on (see {@link #buildLoopInvariantSummary}); such a spurious witness is directly checkable by hand against
	 * the original program, unlike a silent false {@link PathVerdict#SAFE}. A {@link PathVerdict#SAFE} verdict proves
	 * safety for <em>any</em> combination of iteration counts across every loop head on this path, up to the
	 * per-phase interpolant-stabilization bound {@code MAX_K} - the same kind of bounded/heuristic limitation
	 * {@code MAX_K} itself already carries for a single loop, now generalized to every loop head instead of exactly one.
	 */
	private PathResult runPath(final CheckpointGraph<STATE> graph, final List<Checkpoint<STATE>> path) {
		final List<STATE> loopHeadsOnPath = new ArrayList<>();
		for (final Checkpoint<STATE> checkpoint : path) {
			if (checkpoint.isLoopHead()) {
				loopHeadsOnPath.add(checkpoint.getLoopHead());
			}
		}

		if (loopHeadsOnPath.isEmpty()) {
			final List<UnmodifiableTransFormula> regions = List.of(graph.getEdge(Checkpoint.init(), Checkpoint.fin()));
			mMgdImcScript.push(mIMCLock, 1);
			assertRegionSequenceNamed(regions);
			final LBool sat = mMgdImcScript.checkSat(mIMCLock);
			mMgdImcScript.pop(mIMCLock, 1);
			if (sat == LBool.SAT) {
				return PathResult.unsafe();
			}
			return sat == LBool.UNKNOWN ? PathResult.unknown() : PathResult.safe(regions);
		}

		final List<UnmodifiableTransFormula> frozenPrefix = new ArrayList<>();
		frozenPrefix.add(graph.getEdge(Checkpoint.init(), Checkpoint.loopHead(loopHeadsOnPath.get(0))));

		for (int p = 0; p < loopHeadsOnPath.size(); p++) {
			final STATE loopHead = loopHeadsOnPath.get(p);
			final List<UnmodifiableTransFormula> tail = buildTail(graph, loopHeadsOnPath, p);
			final int offset = frozenPrefix.size();

			boolean stabilized = false;
			for (int k = 1; k <= MAX_K; k++) {
				mLogger.info("IMC: path %s, loop head %s, k=%d - asserting %d regions", path, loopHead, k,
						offset + k + tail.size());
				mMgdImcScript.push(mIMCLock, 1);

				final List<UnmodifiableTransFormula> regions = new ArrayList<>(frozenPrefix);
				regions.addAll(Collections.nCopies(k, graph.getLoopBody(loopHead)));
				regions.addAll(tail);

				final Term[] partition = assertRegionSequenceNamed(regions);
				final LBool sat = mMgdImcScript.checkSat(mIMCLock);
				mLogger.info("IMC: path %s, loop head %s, k=%d - solver result: %s", path, loopHead, k, sat);

				if (sat == LBool.SAT) {
					mMgdImcScript.pop(mIMCLock, 1);
					return PathResult.unsafe();
				}
				if (sat == LBool.UNKNOWN) {
					mMgdImcScript.pop(mIMCLock, 1);
					return PathResult.unknown();
				}

				// UNSAT: extract this phase's k+1 cut-point interpolants before popping the scope. Cutpoint j of
				// this phase sits at global interpolant index (offset - 1 + j), since `offset` regions (the frozen
				// prefix) precede this phase's own loop-body copies.
				final Term[] interpolants = mMgdImcScript.getInterpolants(mIMCLock, partition);
				final Term[] cutpointPreds = unSsaToRepresentativeFrame(interpolants);
				mMgdImcScript.pop(mIMCLock, 1);
				final Term[] phaseSlice = Arrays.copyOfRange(cutpointPreds, offset - 1, offset + k);

				if (hasStabilized(phaseSlice, k)) {
					mLogger.info("IMC: path %s, loop head %s, k=%d - interpolant sequence stabilized", path, loopHead,
							k);
					// hasStabilized proved phaseSlice[0..k-1]'s disjunction ("invariant") is inductive w.r.t.
					// loopBody and holds after ANY number n >= 0 of iterations (not just k) - see runPath's
					// javadoc. Carrying it forward as an assumed fact (instead of freezing exactly k concrete
					// copies of loopBody) is what lets later phases verify "this loop ran any number of times",
					// closing the gap where a bug needing some other iteration count of this loop was never
					// explored once it got frozen at one arbitrary, lucky k.
					final Term invariant =
							SmtUtils.or(mWorkerMgdScript.getScript(), Arrays.asList(phaseSlice).subList(0, k));
					frozenPrefix.add(buildLoopInvariantSummary(invariant));
					final Checkpoint<STATE> next =
							p + 1 < loopHeadsOnPath.size() ? Checkpoint.loopHead(loopHeadsOnPath.get(p + 1))
									: Checkpoint.fin();
					frozenPrefix.add(graph.getEdge(Checkpoint.loopHead(loopHead), next));
					stabilized = true;
					break;
				}
				mLogger.info("IMC: path %s, loop head %s, k=%d - interpolant sequence has not stabilized yet", path,
						loopHead, k);
			}
			if (!stabilized) {
				mLogger.info("IMC: path %s, loop head %s - reached MAX_K=%d without stabilizing or finding a bug", path,
						loopHead, MAX_K);
				return PathResult.unknown();
			}
		}
		return PathResult.safe(frozenPrefix);
	}

	/**
	 * The fixed continuation of {@code path} after phase {@code phaseIndex}'s loop head: one mandatory pass through
	 * every later loop head on the path (it hasn't been reached yet, so it isn't swept - only the current phase's loop
	 * head is), followed by the edge into FINAL. Constant across a phase's whole {@code k} sweep, exactly like the
	 * single-loop case's {@code suffix} was constant across {@code k}.
	 */
	private List<UnmodifiableTransFormula> buildTail(final CheckpointGraph<STATE> graph,
			final List<STATE> loopHeadsOnPath, final int phaseIndex) {
		final List<UnmodifiableTransFormula> tail = new ArrayList<>();
		STATE current = loopHeadsOnPath.get(phaseIndex);
		for (int q = phaseIndex + 1; q < loopHeadsOnPath.size(); q++) {
			final STATE next = loopHeadsOnPath.get(q);
			tail.add(graph.getEdge(Checkpoint.loopHead(current), Checkpoint.loopHead(next)));
			tail.add(graph.getLoopBody(next));
			current = next;
		}
		tail.add(graph.getEdge(Checkpoint.loopHead(current), Checkpoint.fin()));
		return tail;
	}

	/**
	 * Turns a proven-inductive loop invariant (a {@link Term}, native to {@link #mWorkerMgdScript}, over program
	 * vars' {@link IProgramVar#getDefaultConstant() default constants} - see {@link #unSsaToRepresentativeFrame})
	 * into a "havoc, then assume" {@link UnmodifiableTransFormula}: every program var that {@code invariant}
	 * actually constrains gets a fresh outVar tied to that constraint; every other var gets no outVar at all, so
	 * the next region's own SSA indexing will declare a fresh, wholly unconstrained constant for it (a genuine
	 * havoc). No inVars are added - {@code invariant} is self-contained and does not depend on how the loop head
	 * was reached.
	 * <p>
	 * This is deliberately an over-approximation for any variable the invariant doesn't mention (rather than
	 * assuming it stayed unchanged): an interpolant is only guaranteed sufficient for its own infeasibility proof,
	 * not a complete description of the loop's effect on every variable, so treating an unmentioned-but-modified
	 * variable as unchanged could silently rule out real post-loop values - the same class of false-{@code SAFE}
	 * mistake this method exists to fix (see the call site in {@link #runPath}). Over-approximating instead can in
	 * principle make a later {@link PathVerdict#UNSAFE} verdict a spurious artifact of the havoc rather than the
	 * original program - a materially better failure mode than a silent false {@code SAFE}, since a concrete
	 * witness is directly re-checkable against the original program by hand.
	 */
	private UnmodifiableTransFormula buildLoopInvariantSummary(final Term invariant) {
		final Map<Term, IProgramVar> defaultConstant2ProgVar = new HashMap<>();
		for (final IProgramVar pv : mConstants2BoogieVar.values()) {
			defaultConstant2ProgVar.put(pv.getDefaultConstant(), pv);
		}
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);
		final Map<Term, Term> substitution = new HashMap<>();
		for (final ApplicationTerm constant : SmtUtils.extractConstants(invariant, false)) {
			final IProgramVar pv = defaultConstant2ProgVar.get(constant);
			if (pv == null) {
				// Not one of the program vars in play for this run (e.g. a solver-internal symbol); nothing to do.
				continue;
			}
			final TermVariable fresh =
					mWorkerMgdScript.constructFreshTermVariable(pv.getGloballyUniqueId(), pv.getTermVariable().getSort());
			tfb.addOutVar(pv, fresh);
			substitution.put(constant, fresh);
		}
		tfb.setFormula(PureSubstitution.apply(mWorkerMgdScript, substitution, invariant));
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(mWorkerMgdScript);
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

		mConstants2BoogieVar = new HashMap<>();
		final Term[] partition = new Term[regions.size()];
		for (int s = 0; s < regions.size(); s++) {
			final UnmodifiableTransFormula region = regions.get(s);
			final int idxInVar = s;
			final int idxOutVar = s + 1;
			final Set<IProgramVar> assignedVars = new HashSet<>();
			Term ssaFormula = PredicateUtils.formulaWithIndexedVars(region, idxInVar, idxOutVar, assignedVars,
					mIndexedConstantsWorkerScript, mWorkerMgdScript.getScript());
			ssaFormula = mWorker2Imc.transform(ssaFormula);

			// Mirrors formulaWithIndexedVars' own constant choice per var exactly (oldvars use their stable default
			// constant instead of an indexed one) so mConstants2BoogieVar always maps the constant that actually
			// occurs in ssaFormula, not a freshly-minted one nobody references. Not expected to trigger while
			// procedures are assumed inlined, but cheap to keep correct in case an oldvar slips through.
			for (final IProgramVar pv : region.getInVars().keySet()) {
				final Term constant = pv.isOldvar() ? pv.getDefaultConstant()
						: PredicateUtils.getIndexedConstant(pv, idxInVar, mIndexedConstantsWorkerScript,
								mWorkerMgdScript.getScript());
				mConstants2BoogieVar.put(mWorker2Imc.transform(constant), pv);
			}
			for (final IProgramVar pv : assignedVars) {
				final Term constant = pv.isOldvar() && !region.getAssignedVars().contains(pv) ? pv.getDefaultConstant()
						: PredicateUtils.getIndexedConstant(pv, idxOutVar, mIndexedConstantsWorkerScript,
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
	 * worker's script ({@link #mWorkerMgdScript}), since {@code pv} is one of {@link CheckpointGraphFormulaBuilder}'s
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
