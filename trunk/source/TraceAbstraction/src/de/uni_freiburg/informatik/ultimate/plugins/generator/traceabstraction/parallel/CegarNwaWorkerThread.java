/*
 * Copyright (C) 2025 University of Freiburg
 * Copyright (C) 2025 LMU Munich
 * Copyright (C) 2025 Max Barth (Max.Barth@lmu.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel;

import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TaJobProcessor.Feasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TaJobProcessor.RefinementAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker.TransferMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.IInvariantSink;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantMessage.InterpolantSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

public class CegarNwaWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {
	private final ILogger mLogger;
	private final TAPreferences mPref;
	private final CegarLoopResultBuilder mResultBuilder;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final PredicateFactory mPredicateFactory;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	private int mIteration;
	private IRun<L, ?> mCounterexample = null;
	// the trace check and the automaton of a counterexample, shared with the TA worker processes
	private final TaJobProcessor<L> mJobProcessor;
	// How often a worker waiting for a task looks whether it was retired
	private static final long RETIREMENT_POLL_MILLIS = 200;
	private final ParallelNwaCegarLoop<L, A> mMainThread;
	private INestedWordAutomaton<L, IPredicate> mAbstraction;
	// communication with controller
	private WorkerThreadResult<L, A> mThreadResult = null;
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	private final BlockingQueue<WorkerThreadTask<L>> mWorkerTaskQueue;
	private final TransferBetweenMainAndWorker<L, IPredicate> mNwaCexTransferrer;

	private final PathProgramCache<L> mProgramCache;
	// the services of the counterexample check that is running, see run()
	private TaskScopedServices mTaskServices;
	// where the interpolants of every infeasible counterexample go, to be checked for invariants
	private final IInvariantSink mInvariantSink;
	// Expires when the HeapWatchdog retires this worker; mServices asks it, so it stops the running check.
	private final RetirementTimer mRetirementTimer;
	// The task whose counterexample is being checked, null while the worker waits for one
	private WorkerThreadTask<L> mTask;

	/**
	 * CegarNwaWorkerThread is a runnable that will be executed by an executor service. It takes counterexamples from
	 * the workerTaskQueue and puts the resulting automata into the blockingQueueForResults. It takes the current
	 * abstraction from the controller, every time it does a difference calculation.
	 *
	 * TransferBetweenMainAndWorker is used to transfer between worker and controller/main cfgScript
	 *
	 * Thread-safety: everything that is given via constructor needs to be thread-save, Most things are freshly created
	 * in when the this object is created. Exceptions are: services, Preferences, the Logger and the PathProgramCache
	 * PathProgramCacheis thread save, the others shouldnt be an issue.
	 *
	 * TODO provide CEGAR loop statistics
	 *
	 * @author Max Barth (max.barth@lmu.de)
	 */
	public CegarNwaWorkerThread(final ILogger logger, final TAPreferences pref, final int id,
			final CegarLoopResultBuilder resultBuilder, final IUltimateServiceProvider services,
			final CfgSmtToolkit cfgSmtToolkit, final PredicateFactory predicateFactory,
			final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final BlockingQueue<WorkerThreadTask<L>> workerTaskQueue,
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils, final IInvariantSink invariantSink,
			final RetirementTimer retirementTimer) {

		mLogger = logger;
		mPref = pref;
		mIteration = id;
		mResultBuilder = resultBuilder;
		mRetirementTimer = retirementTimer;
		mServices = services.getProgressMonitorService().registerChildTimer(services, retirementTimer);
		mCfgSmtToolkit = cfgSmtToolkit;
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;
		mWorkerTaskQueue = workerTaskQueue;
		mNwaCexTransferrer = transferWorkerUtils;
		mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAbstraction();
		mProgramCache = new PathProgramCache<>(mLogger);
		mInvariantSink = invariantSink;
		mJobProcessor = new TaJobProcessor<>(mLogger, pref, mServices, cfgSmtToolkit, predicateFactory,
				taCheckAndRefinementPrefs, predicateFactoryInterpolantAutomata, stateFactoryForRefinement,
				computeHoareAnnotation, mainThread.mTransitionClazz, mProgramCache, mainThread.getTaskIdentifier());

		final Thread.UncaughtExceptionHandler exhandler = (th, ex) -> {
			mThreadResult = new WorkerThreadResult<>(WorkerType.TA, null, null, null, mCounterexample, null, true);
			try {
				mBlockingQueueForResults.put(mThreadResult);
				throw new AssertionError("Worker Thread failed due to " + ex);
			} catch (final InterruptedException e) {
				throw new AssertionError("Worker Thread failed due to " + e);
			}
		};
		Thread.currentThread().setUncaughtExceptionHandler(exhandler);

	}

	/*
	 * Gets a counterexamples from the blocking queue, sets up a strategy (checks how often the pathprogram has been
	 * seen). Checks feasibility, interpolates, creates an Error or Interpolant automaton. Calculates the difference to
	 * generalize the interpolant automaton and then puts a @WorkerThreadResult into the blocking queue for results.
	 *
	 * Terminates if the Thread is interrupted (not used atm) or the Executioner service triggers a shutdown. If the
	 * check of a counterexample throws, the worker tells the main thread with a crashed result and takes no more tasks.
	 * If the {@link HeapWatchdog} retires the worker, the check it runs is stopped and the worker tells the main thread
	 * with a retired result, which hands back the counterexample.
	 */
	@Override
	public void run() {
		try {
			while (!Thread.currentThread().isInterrupted()) {
				if (!checkNextCounterexample()) {
					return;
				}
			}
		} finally {
			mRetirementTimer.stopped();
		}
	}

	/**
	 * @return whether the worker takes another task
	 */
	private boolean checkNextCounterexample() {
		// What the task constructs, above all the solvers of its trace checks, is destroyed when it is done.
		mTaskServices = new TaskScopedServices(mServices);
		try {
			mLogger.info("WorkerThread: " + Thread.currentThread() + " is Waiting for a Task");
			mIteration += 1;
			mTask = takeTask();
			if (mTask == null) {
				return retire();
			}
			checkCounterexample(mTask);
			mTask = null;
			return true;
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
			return false;
		} catch (final Throwable t) {
			if (mMainThread.isShuttingDown()) {
				// Another worker decided and the main thread destroyed our solver under a running query.
				mLogger.info("WorkerThread: stopping, shut down during a trace check (" + t + ")");
				return false;
			}
			if (mRetirementTimer.isRetired()) {
				// Whatever was thrown, a cancellation or an exception that wraps one, the retirement stopped it.
				return retire();
			}
			mLogger.error("WorkerThread failed: " + t);
			for (final StackTraceElement element : t.getStackTrace()) {
				mLogger.error("\tat " + element);
			}
			try {
				mBlockingQueueForResults.put(WorkerThreadResult.crashed(WorkerType.TA, t));
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
			return false;
		} finally {
			mTaskServices.destroyAll(mLogger);
			mTaskServices = null;
		}
	}

	/**
	 * Waits for the next task, but no longer than until the worker is retired.
	 *
	 * @return the task, or null if the worker was retired
	 */
	private WorkerThreadTask<L> takeTask() throws InterruptedException {
		while (!mRetirementTimer.isRetired()) {
			final WorkerThreadTask<L> task = mWorkerTaskQueue.poll(RETIREMENT_POLL_MILLIS, TimeUnit.MILLISECONDS);
			if (task != null) {
				return task;
			}
		}
		return null;
	}

	/**
	 * Tells the main thread that this worker retired, with the counterexample it was checking, if any.
	 *
	 * @return false, the worker takes no more tasks
	 */
	private boolean retire() {
		mLogger.info("WorkerThread: retired, %s", mRetirementTimer.getReason());
		try {
			mBlockingQueueForResults
					.put(WorkerThreadResult.retired(WorkerType.TA, mTask == null ? null : mTask.getCounterexample()));
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
		}
		return false;
	}

	/**
	 * Checks the counterexample of one task and puts the result into the queue for the main thread.
	 */
	private void checkCounterexample(final WorkerThreadTask<L> task)
			throws AutomataLibraryException, InterruptedException {
		final IRun<L, ?> mainThreadCounterexample = task.getCounterexample();
		mProgramCache.copyProgramCache(mMainThread.getCurrentProgramCache());
		mCounterexample =
				mNwaCexTransferrer.transferRun((NestedRun<L, ?>) mainThreadCounterexample, TransferMode.MAIN2WORKER);
		updateAbstractionIfSmaller();

		// set the programCount to x-1, because we will report it again later
		mProgramCache.setPathProgramCount(mCounterexample.getWord(), task.getPathProgramCount() - 1);
		final List<L> trace = mCounterexample.getWord().asList();
		final IcfgLocation currentErrorLoc = mCounterexample.getSymbol(mCounterexample.getLength() - 2).getTarget();
		final int traceHash = trace.hashCode();
		mLogger.info("Starting Thread: " + Thread.currentThread().threadId() + "# for Trace Check: " + traceHash);
		Thread.currentThread().setName("Worker for " + traceHash);
		final Feasibility<L> feasibility = mJobProcessor.checkFeasibility(getServices(), mCounterexample,
				mAbstraction, mIteration, mRetirementTimer::isRetired);
		if (feasibility.status() == LBool.UNSAT) {
			submitInterpolants(feasibility.refinementResult());
		}
		recordFeasibility(feasibility, currentErrorLoc);

		final RefinementAutomaton<L> automaton = mJobProcessor.constructAutomaton(getServices(), feasibility);
		mThreadResult = new WorkerThreadResult<>(WorkerType.TA,
				mNwaCexTransferrer.transferAutomaton(automaton.automaton(), mPredicateFactoryInterpolantAutomata,
						TransferMode.WORKER2MAIN),
				automaton.type(), mCfgSmtToolkit.getManagedScript(),
				mNwaCexTransferrer.transferRun((NestedRun<L, ?>) mCounterexample, TransferMode.WORKER2MAIN),
				mPredicateFactory, false);
		mLogger.info("Done with Thread: " + Thread.currentThread().threadId() + "#");
		mBlockingQueueForResults.put(mThreadResult);
	}

	/**
	 * Hands every interpolant sequence of the infeasibility proof to the invariant supplier, which keeps what is
	 * inductive. The interpolants are terms of this worker's script; the supplier copies them on its own thread.
	 */
	private void submitInterpolants(
			final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementResult) {
		final List<QualifiedTracePredicates> sequences = refinementResult.getUsedTracePredicates();
		if (sequences == null) {
			return;
		}
		final List<IcfgLocation> locations = TaJobProcessor.getIcfgLocationsFromRun(mCounterexample);
		// The interpolants are those between two letters, i.e. at the states 1..n-1 of the run.
		final List<IcfgLocation> inner = locations.subList(1, locations.size() - 1);
		for (final QualifiedTracePredicates sequence : sequences) {
			final List<Term> interpolants =
					sequence.getPredicates().stream().map(IPredicate::getFormula).collect(Collectors.toList());
			mInvariantSink.submit(new InterpolantSequence(mCfgSmtToolkit.getManagedScript(), inner, interpolants,
					"TA " + sequence.getOrigin().getSimpleName()));
		}
	}

	/**
	 * Worker takes the current abstraction from the main thread (read only). Then transfers it to worker script.
	 */
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getAbstraction() {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mainAbstraction = mMainThread.getAbstraction();
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> workerAbstraction = mNwaCexTransferrer
				.transferAutomaton(mainAbstraction, mPredicateFactoryInterpolantAutomata, TransferMode.MAIN2WORKER);
		return workerAbstraction;
	}

	private void updateAbstractionIfSmaller() {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mainAbstraction = mMainThread.getAbstraction();
		if (mainAbstraction instanceof NestedWordAutomaton && mainAbstraction.size() < mAbstraction.size()) {
			mLogger.info("Updating worker A, since main A " + mainAbstraction.size() + " is smaller than worker A "
					+ mAbstraction.size());
			mAbstraction = (INestedWordAutomaton<L, IPredicate>) mNwaCexTransferrer.transferAutomaton(mainAbstraction,
					mPredicateFactoryInterpolantAutomata, TransferMode.MAIN2WORKER);
		}

	}

	/**
	 * Records the verdict of a trace check in the shared result builder, before the automaton is built.
	 */
	private void recordFeasibility(final Feasibility<L> feasibility, final IcfgLocation currentErrorLoc) {
		final IProgramExecution<L, Term> programExecution = feasibility.programExecution();
		switch (feasibility.status()) {
		case SAT:
			mResultBuilder.addResultForProgramExecution(Result.UNSAFE, programExecution, null, null);
			if (mPref.stopAfterFirstViolation()) {
				mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
			}
			return;
		case UNSAT:
			return;
		case UNKNOWN:
			if (programExecution != null) {
				final UnprovabilityReason reasonUnknown =
						new UnprovabilityReason("unable to decide satisfiability of path constraint");
				mResultBuilder.addResultForProgramExecution(Result.UNKNOWN, programExecution, null, reasonUnknown);
			}
			mResultBuilder.addResult(currentErrorLoc, Result.TIMEOUT, null, null, null);
			if (mPref.stopAfterFirstViolation()) {
				mResultBuilder.addResultForAllRemaining(Result.TIMEOUT);
			}
			return;
		default:
			throw new AssertionError("Unknown feasibility " + feasibility.status());
		}
	}

	protected IUltimateServiceProvider getServices() {
		return mTaskServices != null ? mTaskServices : mServices;
	}
}
