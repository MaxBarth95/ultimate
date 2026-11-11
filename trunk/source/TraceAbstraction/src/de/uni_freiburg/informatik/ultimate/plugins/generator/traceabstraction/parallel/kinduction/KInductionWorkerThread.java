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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.kinduction;

import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ICegarNwaWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ParallelNwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker.TransferMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadTask;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInduction;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInduction.WitnessInvariants;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInductionCounterexampleException;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.IInvariantSupplier;

/**
 * Worker thread running {@link KInduction} inside {@link ParallelNwaCegarLoop}'s thread pool. It runs once (see
 * {@link #run()}) on the whole program and reports a {@link WorkerThreadResult} sentinel when the program is safe.
 * <p>
 * When k-induction refutes the program, {@link KInduction} reconstructs a feasible run from the solver's model and
 * this class reports it: it makes an {@code IcfgProgramExecution} from the run, without a trace check and without
 * values (see {@link #reportCounterexample}), registers
 * {@code Result.UNSAFE} on the shared result builder, and hands the main thread a result marked
 * {@link AutomatonType#ERROR} so that it terminates instead of refining. It carries no error-automaton scaffolding:
 * the whole program is refuted at once, so there is nothing left to refine.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class KInductionWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {
	private final ILogger mLogger;
	private final TAPreferences mPref;
	private final CegarLoopResultBuilder mResultBuilder;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	private int mIteration;
	private final boolean mComputeHoareAnnotation;
	public final ParallelNwaCegarLoop<L, A> mMainThread;
	private final INestedWordAutomaton<L, IPredicate> mAbstraction;
	// communication with controller
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	private final BlockingQueue<WorkerThreadTask<L>> mWorkerTaskQueue;
	private final TransferBetweenMainAndWorker<L, IPredicate> mNwaCexTransferrer;
	private final IInvariantSupplier<CallNode<IPredicate>> mInvariantSupplier;
	// k-induction has no memory limit: when the heap fills up, the other workers retire (see HeapWatchdog).
	private final IUltimateServiceProvider mKInductionServices;
	// The invariants of a proof for the main thread's correctness witness, see computeWitnessInvariants
	private WitnessInvariants<IPredicate> mWitnessInvariants;
	// How much longer than its timer (TAPreferences.getKInductionWitnessTimeout) the verdict waits for a computation
	// that has not noticed the timer yet
	private static final long WITNESS_GRACE_MILLIS = 500;
	// Set when the verdict went without the computation, which may still be running
	private volatile boolean mWitnessAbandoned;

	public KInductionWorkerThread(final ILogger logger, final TAPreferences pref, final int id,
			final CegarLoopResultBuilder resultBuilder, final IUltimateServiceProvider services,
			final CfgSmtToolkit cfgSmtToolkit,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final BlockingQueue<WorkerThreadTask<L>> workerTaskQueue,
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils,
			final IInvariantSupplier<CallNode<IPredicate>> invariantSupplier) throws InterruptedException {
		mLogger = logger;
		mPref = pref;
		mIteration = id;
		mResultBuilder = resultBuilder;
		mCfgSmtToolkit = cfgSmtToolkit;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mComputeHoareAnnotation = computeHoareAnnotation;
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;
		mWorkerTaskQueue = workerTaskQueue;
		mNwaCexTransferrer = transferWorkerUtils;
		mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAndTransferAbstraction();
		mInvariantSupplier = invariantSupplier;
		mKInductionServices = services;
	}

	@Override
	public void run() {
		Thread.currentThread().setName("KInduction Thread");
		try {
			mLogger.info("WorkerThread for KInduction Starts");
			mIteration = 1;
			switch (runKInduction()) {
			case SAFE:
				mBlockingQueueForResults.put(WorkerThreadResult.kInductionSafe(
						mWitnessInvariants == null ? null : mWitnessInvariants.invariants(),
						mWitnessInvariants != null && mWitnessInvariants.proving(), mCfgSmtToolkit.getManagedScript()));
				break;
			case UNSAFE:
				// The violation is already registered on the shared result builder. AutomatonType.ERROR is what
				// tells the main thread that this is a refutation and not the "safe" sentinel, which carries a
				// null automaton type; no subtrahend, because there is nothing left to refine.
				mBlockingQueueForResults.put(new WorkerThreadResult<>(WorkerType.KINDUCTION, null,
						AutomatonType.ERROR, null, null, null, false));
				break;
			case NO_VERDICT:
				mBlockingQueueForResults.put(WorkerThreadResult.noVerdict(WorkerType.KINDUCTION));
				break;
			default:
				throw new AssertionError("unknown k-induction verdict");
			}
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
		} catch (final Throwable t) {
			if (mMainThread.isShuttingDown()) {
				// Another worker decided and the main thread destroyed our solver under a running query.
				mLogger.info("KInduction worker: stopping, shut down during a query (" + t + ")");
				return;
			}
			if (isLimit(t)) {
				// Not a bug in k-induction: its solver gave up or it could not build a run. The other workers go on.
				mLogger.warn("KInduction: stopped by %s; the k-induction worker retires without a verdict", t);
				if (mLogger.isDebugEnabled()) {
					for (final StackTraceElement element : t.getStackTrace()) {
						mLogger.debug("\tat " + element);
					}
				}
				try {
					mBlockingQueueForResults.put(WorkerThreadResult.noVerdict(WorkerType.KINDUCTION));
				} catch (final InterruptedException e) {
					Thread.currentThread().interrupt();
				}
				return;
			}
			mLogger.error("KInduction worker crashed: " + t);
			for (final StackTraceElement element : t.getStackTrace()) {
				mLogger.error("\tat " + element);
			}
			try {
				mBlockingQueueForResults.put(WorkerThreadResult.crashed(WorkerType.KINDUCTION, t));
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
		}
	}

	/**
	 * @return whether k-induction stopped at a limit rather than at a bug: its solver failed (out of memory,
	 *         crashed, or rejected the query), it could not express a violation as a run, or the program uses something
	 *         k-induction does not support. A crash still only retires the worker; this decides how it is logged.
	 */
	private static boolean isLimit(final Throwable t) {
		if (t instanceof UnsupportedOperationException) {
			return true;
		}
		for (Throwable cause = t; cause != null; cause = cause.getCause()) {
			if (cause instanceof SMTLIBException || cause instanceof KInductionCounterexampleException) {
				return true;
			}
		}
		return false;
	}

	private enum Verdict {
		SAFE, UNSAFE, NO_VERDICT
	}

	private Verdict runKInduction() throws AutomataLibraryException, InterruptedException {
		final KInduction<L, IPredicate> kInduction = new KInduction<>(mKInductionServices, mLogger, mCfgSmtToolkit,
				mAbstraction, mInvariantSupplier, mPref.restartKInductionSolverAfterInterrupt());
		if (kInduction.wasUnkown()) {
			// Not a crash: the encoding is fine, the query was just not decided. Retiring this worker leaves the
			// other workers - and, if there are none, the main thread's UNKNOWN result - to speak for the program.
			mLogger.warn("KInduction: " + kInduction.getInconclusive());
			return Verdict.NO_VERDICT;
		}
		if (kInduction.isSafe()) {
			if (mComputeHoareAnnotation) {
				mWitnessInvariants = computeWitnessInvariants(kInduction);
			}
			return Verdict.SAFE;
		}
		// No transfer: the run is built over the worker's own abstraction with worker-script letters, and the
		// refinement engine below runs on the worker toolkit, exactly as in CegarNwaWorkerThread.
		reportCounterexample(kInduction.getCounterexample());
		return Verdict.UNSAFE;
	}

	/**
	 * The invariants of the proof for a correctness witness, by loop head. A loop head is a state of
	 * {@link #mAbstraction}, which shares its states with the main thread's initial abstraction, see
	 * {@link TransferBetweenMainAndWorker#transferAutomaton}.
	 *
	 * @return the invariants, worker-script terms, or null if there are none; throws only when interrupted, since the
	 *         proof stands without a witness
	 */
	private WitnessInvariants<IPredicate> computeWitnessInvariants(final KInduction<L, IPredicate> kInduction)
			throws InterruptedException {
		final long timeout = mPref.getKInductionWitnessTimeout();
		// The timer of computeWitnessInvariantsWithin only ends the computation where it looks at it, and the ite
		// removal of the quantifier elimination does not: it ran for minutes and the verdict never came. So the verdict
		// waits for the computation only until the timer has run out, and an unfinished one is left behind with the
		// best invariants it has proven so far. It only uses this worker's own script, which nobody needs once there
		// is a verdict.
		final FutureTask<WitnessInvariants<IPredicate>> task =
				new FutureTask<>(() -> computeWitnessInvariantsWithin(kInduction, timeout));
		final Thread thread = new Thread(task, "KInduction witness");
		thread.setDaemon(true);
		thread.start();
		WitnessInvariants<IPredicate> invariants;
		try {
			invariants = task.get(timeout + WITNESS_GRACE_MILLIS, TimeUnit.MILLISECONDS);
		} catch (final TimeoutException e) {
			mWitnessAbandoned = true;
			thread.interrupt();
			invariants = kInduction.getBestWitnessInvariants();
			mLogger.warn("KInduction: computing the correctness witness invariants did not end within %d ms, %s",
					timeout + WITNESS_GRACE_MILLIS,
					invariants == null ? "there are none" : "using the best ones found so far");
		} catch (final ExecutionException e) {
			// computeWitnessInvariantsWithin catches everything but errors such as running out of memory
			mLogger.error("KInduction: computing the correctness witness invariants failed: " + e.getCause());
			invariants = kInduction.getBestWitnessInvariants();
		}
		if (invariants == null) {
			mLogger.warn("KInduction: no correctness witness invariants for the proof at k=%d", kInduction.getProvedK());
			return null;
		}
		return invariants;
	}

	/**
	 * @return the invariants of {@link KInduction#computeWitnessInvariants}, or the best ones it found before it failed,
	 *         or null if there are none
	 */
	private WitnessInvariants<IPredicate> computeWitnessInvariantsWithin(final KInduction<L, IPredicate> kInduction,
			final long timeout) {
		final IProgressMonitorService progressMonitor = mKInductionServices.getProgressMonitorService();
		final IUltimateServiceProvider witnessServices = progressMonitor.registerChildTimer(mKInductionServices,
				progressMonitor.getChildTimer(timeout));
		try {
			return kInduction.computeWitnessInvariants(witnessServices, mPref.getSimplificationTechnique(),
					(state, tv) -> isInScope(tv, ((ISLPredicate) state).getProgramPoint().getProcedure())).orElse(null);
		} catch (final ToolchainCanceledException | SMTLIBException e) {
			if (!mWitnessAbandoned) {
				mLogger.warn("KInduction: computing the correctness witness invariants stopped: " + e);
			}
			return kInduction.getBestWitnessInvariants();
		} catch (final RuntimeException | AssertionError e) {
			if (mWitnessAbandoned || mMainThread.isShuttingDown()) {
				// Left behind, the main thread may have destroyed the solver under it.
				return null;
			}
			// A bug in the witness computation must not cost the verdict, but it should be visible. What was proven
			// before it is still proven.
			mLogger.error("KInduction: computing the correctness witness invariants crashed: " + e);
			for (final StackTraceElement element : e.getStackTrace()) {
				mLogger.error("\tat " + element);
			}
			return kInduction.getBestWitnessInvariants();
		}
	}

	/**
	 * @return whether {@code tv} is a global variable or a local of {@code procedure}. The transition system is flat, so
	 *         the invariant of a loop head in a callee may speak about its callers. A variable the symbol table does not
	 *         know, such as the stack pointer of {@code CallStack}, does not exist in the program at all, so it is out
	 *         of scope too.
	 */
	private boolean isInScope(final TermVariable tv, final String procedure) {
		final IProgramVar pv = mCfgSmtToolkit.getSymbolTable().getProgramVar(tv);
		return pv != null && (pv.isGlobal() || procedure.equals(pv.getProcedure()));
	}

	/**
	 * Registers a k-induction counterexample as {@code Result.UNSAFE}, with a program execution made directly from the
	 * run's nested word. The witness and the backtranslation to the input program come from that execution, as for
	 * any other counterexample.
	 * <p>
	 * There is no trace check: the counterexample builder already found the run feasible letter by letter, by executing
	 * the letters on concrete values and confirming the symbolic ones with the solver. Checking the whole run again
	 * cost minutes on hardware tasks (bitwuzla) and floats, and the run often timed out before it reported the
	 * verdict. As a consequence, the execution carries no variable values. Its branch encoders are all set to true,
	 * which only matters for parallel compositions of letters; the SV-COMP settings create none. An overapproximated
	 * letter still turns the result into UNKNOWN, since the result builder reads that from the letters of the
	 * execution.
	 */
	private void reportCounterexample(final NestedRun<L, IPredicate> counterexample) {
		final IcfgProgramExecution<L> programExecution =
				TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(counterexample.getWord());
		programExecution.setOriginCfgScript(mCfgSmtToolkit.getManagedScript());

		mResultBuilder.addResultForProgramExecution(Result.UNSAFE, programExecution, null, null);
		if (mPref.stopAfterFirstViolation()) {
			mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
		}
		mLogger.info("KInduction: reported a counterexample of %d letter(s) as UNSAFE",
				counterexample.getWord().length());
	}

	/**
	 * Worker takes the current abstraction from the main thread (read only), then transfers it to the worker script.
	 */
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getAndTransferAbstraction() {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mainAbstraction = mMainThread.getAbstraction();
		return mNwaCexTransferrer.transferAutomaton(mainAbstraction, mPredicateFactoryInterpolantAutomata,
				TransferMode.MAIN2WORKER);
	}
}
