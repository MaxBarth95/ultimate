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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.preferences.IcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

public class ParallelNwaCegarLoop<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		extends NwaCegarLoop<L> {

	boolean mComputeHoareAnnotation;
	final String mDestroyEverything = "destroyEverything";

	// Parallel Setup
	private final ExecutorService mExec;
	private int mThreadLimit;

	/** Workers still alive (i.e. not crashed). Main thread only. */
	private int mLiveWorkers = 0;
	/** Ids of workers currently parked because their search found nothing. Main thread only. */
	private final Set<Integer> mParkedWorkers = new HashSet<>();
	/** How often we let every worker resync and retry before giving up with UNKNOWN. */
	private static final int MAX_RESYNC_ROUNDS = 2;

	private final Object mParkLock = new Object();
	private int mResyncGeneration = 0;

	BlockingQueue<WorkerThreadResult<L, A>> mWorkerResultQueue = new LinkedBlockingQueue<>();

	// Strategies
	/**
	 * Counterexamples claimed by some worker. Entries are added via an atomic claim and are *never*
	 * removed: that is what guarantees no two workers ever analyse the same trace.
	 *
	 * Keys are trace.hashCode(). That key is script-independent because CodeBlock.hashCode() is the
	 * serial number and TransferBetweenMainAndWorker preserves serial numbers when it rebuilds
	 * letters for a worker script — which is what lets workers with different SMT scripts share one
	 * set. Preserve that property when touching transferEdge.
	 */
	private final ConcurrentMap<Integer, NestedRun<L, ?>> mActiveCounterexamples = new ConcurrentHashMap<>();
	protected InterpolationTechnique mInterpolationTechnique;

	protected Class<L> mTransitionClazz;

	// Addtional Statistiks for Evaluation
	private Integer mCounterexamplesChecked = 0;
	private Integer mRefinementsDone = 0;
	private final Integer mCountTimeoutsInSearch = 0;
	private final Integer mCountFailedRunConstructions = 0;
	private Integer mCountFailedToFindCex = 0;
	private Integer mCountBfsFoundCex = 1;
	private final Integer mCountIsEmptyParallel = 0;
	private Integer maxActiveThreads = 0;
	private final Integer mActiveExecutors = 0;
	private long mSearchTime = 0;
	private long mWorkerSetUpTime = 0;
	private int mIterationsWithMaxThreads = 0;
	private int mIterationsWithOneThread = 0;
	private final int mExceptionInWorker = 0;

	private long mRefinementTime = 0;

	/**
	 * Based on the @NwaCegarLoop. Given a ThreadLimit, creates a ExecutionerService that will manage the worker
	 * threads. Executes each tracecheck in a new thread called worker. This loop, only searches for counterexamples and
	 * updates the abstraction. The feasiblity check and generalization of interpolant automata is done by the workers.
	 *
	 * TODO option to save memory, measure heap, then dont spawn worker / kill a worker
	 *
	 * @author Max Barth (max.barth@lmu.de)
	 */

	public ParallelNwaCegarLoop(final DebugIdentifier name,
			final INestedWordAutomaton<L, IPredicate> initialAbstraction, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<? extends IcfgLocation> errorLocs, final NwaHoareProofProducer<L> proofProducer,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, proofProducer,
				services, transitionClazz, stateFactoryForRefinement);
		// Start thread pool
		mThreadLimit = mPref.getThreadLimit();
		if (mThreadLimit == 0) { // maximum of available cores
			mThreadLimit = Runtime.getRuntime().availableProcessors();
			mThreadLimit -= 1; // one for main thread
		}

		mExec = Executors.newFixedThreadPool(mThreadLimit);
		Thread.currentThread().setName("Main Cegar Thread");
		getServices().getStorage().pushMarker(mDestroyEverything);
	}

	/*
	 * Sets up a worker with that communicates via blocking queues and stays alive after one counterexample check. Every
	 * transfer between controller and worker goes via @TransferBetweenMainAndWorker.
	 *
	 */
	private ICegarNwaWorkerThread<L, A> setUpContinuesWorker(final IUltimateServiceProvider iterationServices,
			final int id) throws InterruptedException {

		final TransferBetweenMainAndWorker<L, IPredicate> transferUtils = new TransferBetweenMainAndWorker<>(
				new AutomataLibraryServices(mServices), mLogger, mCsToolkit.getManagedScript(), iterationServices,
				getSolverSettings(iterationServices, "worker" + id + "parallel"),
				mCsToolkit);

		final CfgSmtToolkit freshToolKit = transferUtils.getWorkerCfgSmtToolKit();

		// Create predicateFactory with worker script
		final PredicateFactory predicateFactory =
				new PredicateFactory(mServices, freshToolKit.getManagedScript(), freshToolKit.getSymbolTable());

		// Create PredicateFactoryForInterpolantAutomata with worker script
		final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata =
				new PredicateFactoryForInterpolantAutomata(freshToolKit.getManagedScript(), predicateFactory,
						mComputeHoareAnnotation);

		final Set<IcfgLocation> hoareAnnotationLocs = Collections.emptySet();
		if (mComputeHoareAnnotation) {
			// TODO need different hoareAnnotationLocs
			throw new AssertionError("Hoare Annotations not yet supported in Parallel cegar loop");
		}
		final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(mServices,
				freshToolKit.getManagedScript(), predicateFactory, mComputeHoareAnnotation, hoareAnnotationLocs);

		// make sure that mPref.getCfgSmtToolkit returns the worker toolkit
		final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs =
				new TaCheckAndRefinementPreferences<>(getServices(), mPref, mInterpolationTechnique,
						mSimplificationTechnique, freshToolKit, predicateFactory, mIcfg);
		// initialize worker
		return new CegarNwaWorkerThread<>(mLogger, mPref, id, mResultBuilder, iterationServices, freshToolKit,
				predicateFactory, taCheckAndRefinementPrefs, predicateFactoryInterpolantAutomata,
				stateFactoryForRefinement, mComputeHoareAnnotation, this, mWorkerResultQueue, transferUtils);
	}

	/*
	 * Parallel CEGAR loop. In each iteration we pick a counterexample and put it into a blocking queue for a worker to
	 * check its feasibility
	 **
	 * As soon as we obtain a worker result via blocking queue, we refine our abstraction. If abstraction is not empty,
	 * we continue with the loop. If no worker is done, continue with the loop. If no thread is available and no worker
	 * is done we sleep.
	 */
	/*
	 * Parallel CEGAR loop. Each worker searches for its own counterexamples, claims them in the
	 * shared set, and analyses them. Main does not search at all any more: it drains the result
	 * queue, applies each worker result to the global abstraction, and decides when we are done.
	 */
	@Override
	protected void iterate() throws AutomataLibraryException {
		// TODO manage time and timeout
		final IUltimateServiceProvider iterationServices = createIterationTimer(getErrorLocFromCounterexample());
		for (int i = 0; i < mThreadLimit; i++) {
			try {
				mExec.submit(setUpContinuesWorker(iterationServices, i));
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
				throw new AssertionError("Interrupted during worker setup " + e);
			}
		}
		mLiveWorkers = mThreadLimit;
		// Main no longer owns a "current" counterexample; workers each have their own.
		mCounterexample = null;

		int resyncRounds = 0;
		for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
			abortIfTimeout();
			mLogger.info(String.format("=== Iteration %s ===", getIteration()));

			final WorkerThreadResult<L, A> workerResult;
			try {
				mLogger.info("Main: waiting for a worker result.");
				workerResult = mWorkerResultQueue.take();
			} catch (final InterruptedException ie) {
				Thread.currentThread().interrupt();
				mLogger.warn("Main was interrupted! " + ie);
				break;
			}

			if (workerResult.workerCrashed()) {
				// A crashed worker never parks and is never counted again, so drop it from the live
				// count or all-parked detection could never be reached and main would hang.
				mLiveWorkers -= 1;
				mLogger.error("Main: Worker Crashed! %s workers left.", mLiveWorkers);
				if (mLiveWorkers <= 0) {
					shutDownAndDestroy(mDestroyEverything);
					throw new AssertionError("All workers crashed, exiting CEGAR loop!");
				}
				mIteration -= 1; // a crash is not a refinement
				continue;
			}

			if (workerResult.noCounterexampleFound()) {
				mParkedWorkers.add(workerResult.getWorkerId());
				mLogger.info("Main: worker %s parked (%s of %s parked).", workerResult.getWorkerId(),
						mParkedWorkers.size(), mLiveWorkers);
				if (mParkedWorkers.size() >= mLiveWorkers && mWorkerResultQueue.isEmpty()) {
					if (isSafeThenTerminate()) {
						updateAndPrintStatistics(true);
						return;
					}
					// A worker's abstraction can be a strict under-approximation of main's (see
					// TransferBetweenMainAndWorker.transferAutomaton, which may drop transitions),
					// and IsEmptyParallel also gives up on a timeout or its recursion limit. So
					// "nobody found anything" does not prove the global abstraction is empty.
					resyncRounds += 1;
					if (resyncRounds > MAX_RESYNC_ROUNDS) {
						mLogger.warn("No worker can find a counterexample but the abstraction is not empty.");
						mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
						shutDownAndDestroy(mDestroyEverything);
						updateAndPrintStatistics(true);
						return;
					}
					mLogger.warn("All workers parked but abstraction is not empty; resync round %s", resyncRounds);
					wakeParkedWorkers();
				}
				mIteration -= 1; // parking is not a refinement
				continue;
			}

			// If Error automaton terminate immediately
			if (mPref.stopAfterFirstViolation() && workerResult.getAutomatonType().equals(AutomatonType.ERROR)) {
				shutDownAndDestroy(mDestroyEverything);
				updateAndPrintStatistics(true);
				return;
			}

			final long time = System.nanoTime() / 1000000000;
			try {
				mLogger.info("Worker Automaton Type: " + workerResult.getAutomatonType());
				mLogger.info("Refining Abstraction");
				refinement(workerResult);
				mRefinementsDone += 1;
				mCounterexamplesChecked += 1;
				workerResult.garbageCollect();
			} catch (final CancellationException e) {
				mLogger.warn("Worker was cancelled! " + e);
			} catch (final ToolchainCanceledException e) {
				mLogger.warn("Worker Failed! " + e);
				throw e;
			} finally {
				mRefinementTime += ((System.nanoTime() / 1000000000) - time);
			}

			if (!mPref.minimizeAbstractionPerWorker()) {
				// uses NWA CEGAR loop
				minimizeAbstractionIfEnabled();
			}
			// If new abstraction is empty terminate immediately
			if (isSafeThenTerminate()) {
				updateAndPrintStatistics(true);
				return;
			}

			// The global abstraction changed, so a parked worker may make progress after resyncing.
			resyncRounds = 0;
			if (!mParkedWorkers.isEmpty()) {
				wakeParkedWorkers();
			}
			updateAndPrintStatistics(false);
		}
		mExec.shutdownNow();
		mResultBuilder.addResultForAllRemaining(Result.USER_LIMIT_ITERATIONS);

	}

	private void updateAndPrintStatistics(final boolean printStatistics) {
		final int activeWorkers = mLiveWorkers - mParkedWorkers.size();
		if (activeWorkers > maxActiveThreads) {
			maxActiveThreads = activeWorkers;
		}
		if (activeWorkers == mThreadLimit) {
			mIterationsWithMaxThreads += 1;
		}
		if (activeWorkers == 1) {
			mIterationsWithOneThread += 1;
		}
		if (printStatistics) {
			mLogger.info("Iteration " + getIteration());
			mLogger.info("Refinements: " + mRefinementsDone);
			mLogger.info("Counterexamples: " + mCounterexamplesChecked);
			mLogger.info("SearchTimeout: " + mCountTimeoutsInSearch);
			mLogger.info("RunConstructionFailed: " + mCountFailedRunConstructions);
			mLogger.info("SearchFailed: " + mCountFailedToFindCex);
			mLogger.info("BFS: " + mCountBfsFoundCex);
			mLogger.info("IsEmptyParallel: " + mCountIsEmptyParallel);
			mLogger.info("ActiveThreads: " + maxActiveThreads);
			mLogger.info("ActiveExecutorsForPathPrograms: " + mActiveExecutors);
			mLogger.info("IterationsWithMaxThreads: " + mIterationsWithMaxThreads);
			mLogger.info("IterationsWithONEThread: " + mIterationsWithOneThread);
			mLogger.info("SearchTime: " + mSearchTime + " s");
			mLogger.info("WorkerSetUpTime: " + mWorkerSetUpTime + " s");
			mLogger.info("ExceptionInWorker: " + mExceptionInWorker);
			mLogger.info("mRefinementTime: " + mRefinementTime);
		}
	}

	private boolean isSafeThenTerminate() throws AutomataOperationCanceledException {
		// If IsEmpty says its empty, then we can terminate even if threads are still
		// running
		mLogger.info("Checking if program is safe");
		if (super.isAbstractionEmpty() || mAbstraction.size() == 0) {
			mResultBuilder.addResultForAllRemaining(Result.SAFE);
			shutDownAndDestroy(mDestroyEverything);
			return true;
		}
		// set cex to null to be certain we dont check counterexamples from the old
		// abstraction (super.isAbstractionEmpty() will set mCounterexample)
		mCounterexample = null;
		return false;
	}

	/**
	 * Generation counter that a worker reads *before* it starts searching. Handing the value back to
	 * {@link #awaitResync(int)} closes the lost-wakeup window: if main bumped the generation while
	 * the worker was still searching, the worker does not park at all.
	 */
	public int getResyncGeneration() {
		synchronized (mParkLock) {
			return mResyncGeneration;
		}
	}

	/**
	 * Park the calling worker until main asks it to resync its abstraction from main and search
	 * again. A worker must enqueue its idle marker *before* calling this, otherwise main can block
	 * on an empty result queue forever.
	 */
	public void awaitResync(final int generationBeforeSearch) throws InterruptedException {
		synchronized (mParkLock) {
			while (mResyncGeneration == generationBeforeSearch) {
				mParkLock.wait();
			}
		}
	}

	private void wakeParkedWorkers() {
		mParkedWorkers.clear();
		synchronized (mParkLock) {
			mResyncGeneration++;
			mParkLock.notifyAll();
		}
	}

	private void shutDownAndDestroy(final Object marker) {
		mExec.shutdownNow();
		final Set<String> destroyedStorables = getServices().getStorage().destroyMarker(marker);
		if (!destroyedStorables.isEmpty()) {
			mLogger.warn("Destroyed unattended storables created during the last iteration: "
					+ destroyedStorables.stream().collect(Collectors.joining(",")));
		}
	}

	private void refinement(final WorkerThreadResult<L, A> threadResult)
			throws AutomataOperationCanceledException, AutomataLibraryException {
		// mInterations equals the amount of refinements
		mCegarLoopBenchmark.announceNextIteration();

		final Set<IcfgLocation> hoareAnnotationLocs;
		// TODO support for HoareAnnotations
		hoareAnnotationLocs = Collections.emptySet();

		final PredicateFactoryRefinement stateFactoryForRefinement =
				new PredicateFactoryRefinement(getServices(), threadResult.getWorkerMgdScript(),
						threadResult.getPredicateFactory(), mComputeHoareAnnotation, hoareAnnotationLocs);
		mLogger.info("Difference in Main");
		final IOpWithDelayedDeadEndRemoval<L, IPredicate> diff =
				computeAutomataDifference(mAbstraction, threadResult, stateFactoryForRefinement);

		mAbstraction = diff.getResult();

		if (mPref.minimizeAbstractionPerWorker()) {
			minimizeAbstractionIfEnabled(stateFactoryForRefinement,
					new PredicateFactoryResultChecking(mPredicateFactory));
		}
		mLogger.info("Main: Refinement done.");
	}

	/**
	 * Atomically claim a counterexample for the calling worker. Returns true iff the caller won and
	 * may analyse this trace.
	 *
	 * A false return is an *expected* race between two concurrently searching workers, not an error:
	 * the loser simply searches again. Claims are never released.
	 */
	public boolean claimCounterexample(final NestedRun<L, ?> counterexample) {
		final int traceHash = counterexample.getWord().asList().hashCode();
		return mActiveCounterexamples.putIfAbsent(traceHash, counterexample) == null;
	}

	/**
	 * The shared claim set, handed to IsEmptyParallel so that a worker's search diverges from every
	 * trace already claimed by any worker.
	 */
	public Map<Integer, NestedRun<L, ?>> getActiveCounterexamples() {
		return mActiveCounterexamples;
	}

	/*
	 * The worker using this method to get the Abstraction need to ensure, they use the @TransferBetweenMainAndWorker To
	 * transfer the abstraction to their cfgscript. Worker may only use this to read-only access the abstraction!
	 */
	public INestedWordAutomaton<L, IPredicate> getAbstraction() {
		return mAbstraction;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<L, IPredicate> enhanceInterpolantAutomaton(
			final InterpolantAutomatonEnhancement enhanceMode, final IPredicateUnifier predicateUnifier,
			final IHoareTripleChecker htc, final NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		// Worker does the enhancement or nobody!
		subtrahend = interpolantAutomaton;
		return subtrahend;
	}

	/*
	 * Difference is calculated twice first in worker and then in master. All automata obtained from the worker need to
	 * be transferred to the master cfg script!
	 */
	private IOpWithDelayedDeadEndRemoval<L, IPredicate> computeAutomataDifference(
			final INestedWordAutomaton<L, IPredicate> minuend, final WorkerThreadResult<L, A> workerResult,
			final PredicateFactoryRefinement stateFactoryForRefinement)
			throws AutomataLibraryException, AssertionError {
		try {
			mLogger.debug("Start constructing difference");

			final PowersetDeterminizer<L, IPredicate> psd = new PowersetDeterminizer<>(workerResult.getSubtrahend(),
					true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;
			try {
				if (mPref.differenceSenwa()) {
					diff = new DifferenceSenwa<>(new AutomataLibraryServices(getServices()), stateFactoryForRefinement,
							minuend, workerResult.getSubtrahend(), psd, false);
				} else {
					diff = new Difference<>(new AutomataLibraryServices(getServices()), stateFactoryForRefinement,
							minuend, workerResult.getSubtrahend(), psd, workerResult.exploitSigmaStarConcatOfIa());
				}
				mCegarLoopBenchmark.reportInterpolantAutomatonStates(workerResult.getSubtrahend().size());

			} catch (final AutomataOperationCanceledException | ToolchainCanceledException tce) {
				throw tce;
			} finally {
				// We never enhance in main thread!
			}

			if (!workerResult.useErrorAutomaton()) {
				// TODO needs to get the worker counterexample
				// checkEnhancement(workerResult.getSubtrahendBeforeEnhancement(),
				// workerResult.getSubtrahend());
			}
			// Future work:
			assert !mPref.dumpOnlyReuseAutomata();
			assert mFaultLocalizationMode == RelevanceAnalysisMode.NONE;

			if (REMOVE_DEAD_ENDS) {
				diff.removeDeadEnds();
			}
			return diff;
		} finally {
		}
	}

	/**
	 * @param services
	 * @param filename
	 */
	private SolverSettings getSolverSettings(final IUltimateServiceProvider services, final String filename) {

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		final SolverMode solverMode = prefs.getEnum(IcfgPreferenceInitializer.LABEL_SOLVER, SolverMode.class);

		final boolean fakeNonIncrementalScript =
				prefs.getBoolean(IcfgPreferenceInitializer.LABEL_FAKE_NON_INCREMENTAL_SCRIPT);

		final boolean dumpSmtScriptToFile = prefs.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_TO_FILE);
		final boolean compressSmtScript = prefs.getBoolean(IcfgPreferenceInitializer.LABEL_COMPRESS_SMT_DUMP_FILE);
		final String pathOfDumpedScript = prefs.getString(IcfgPreferenceInitializer.LABEL_DUMP_PATH);

		final String commandExternalSolver = prefs.getString(IcfgPreferenceInitializer.LABEL_EXT_SOLVER_COMMAND);

		final boolean dumpUnsatCoreTrackBenchmark =
				prefs.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_UNSAT_CORE_BENCHMARK);

		final boolean dumpMainTrackBenchmark =
				prefs.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_MAIN_TRACK_BENCHMARK);

		final Map<String, String> additionalSmtOptions =
				prefs.getKeyValueMap(IcfgPreferenceInitializer.LABEL_ADDITIONAL_SMT_OPTIONS);

		final Logics logicForExternalSolver =
				Logics.valueOf(prefs.getString(IcfgPreferenceInitializer.LABEL_EXT_SOLVER_LOGIC));
		final SolverSettings solverSettings =
				SolverBuilder.constructSolverSettings().setUseFakeIncrementalScript(fakeNonIncrementalScript)
						.setDumpSmtScriptToFile(dumpSmtScriptToFile, pathOfDumpedScript, filename, compressSmtScript)
						.setDumpUnsatCoreTrackBenchmark(dumpUnsatCoreTrackBenchmark)
						.setDumpMainTrackBenchmark(dumpMainTrackBenchmark)
						.setUseExternalSolver(true, commandExternalSolver, logicForExternalSolver)
						.setSolverMode(solverMode).setAdditionalOptions(additionalSmtOptions);

		return solverSettings;
	}

	private void minimizeAbstractionIfEnabled(final PredicateFactoryRefinement stateFactoryForRefinement,
			final PredicateFactoryResultChecking predicateFactoryResultChecking)
			throws AutomataOperationCanceledException, AutomataLibraryException, AssertionError {
		final Minimization minimization = mPref.getMinimization();
		switch (minimization) {
		case NONE:
			// do not apply minimization
			break;
		case DFA_HOPCROFT_LISTS:
		case DFA_HOPCROFT_ARRAYS:
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
		case NWA_MAX_SAT:
		case NWA_MAX_SAT2:
		case RAQ_DIRECT_SIMULATION:
		case RAQ_DIRECT_SIMULATION_B:
		case NWA_COMBINATOR_PATTERN:
		case NWA_COMBINATOR_EVERY_KTH:
		case NWA_OVERAPPROXIMATION:
		case NWA_COMBINATOR_MULTI_DEFAULT:
		case NWA_COMBINATOR_MULTI_SIMULATION:
			// apply minimization
			minimizeAbstraction(stateFactoryForRefinement, predicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}
	}

	/**
	 * Automata theoretic minimization of the automaton stored in mAbstraction. Expects that mAbstraction does not have
	 * dead ends.
	 *
	 * @param predicateFactoryRefinement
	 *            PredicateFactory for the construction of the new (minimized) abstraction.
	 * @param resultCheckPredFac
	 *            PredicateFactory used for auxiliary automata used for checking correctness of the result (if
	 *            assertions are enabled).
	 */
	@Override
	protected void minimizeAbstraction(final PredicateFactoryRefinement predicateFactoryRefinement,
			final PredicateFactoryResultChecking resultCheckPredFac, final Minimization minimization)
			throws AutomataOperationCanceledException, AutomataLibraryException, AssertionError {

		final Function<IPredicate, Set<IcfgLocation>> lcsProvider =
				x -> (x instanceof ISLPredicate ? Collections.singleton(((ISLPredicate) x).getProgramPoint())
						: new HashSet<>(Arrays.asList(((IMLPredicate) x).getProgramPoints())));
		AutomataMinimization<Set<IcfgLocation>, IPredicate, L> am;
		try {
			am = new AutomataMinimization<>(getServices(), mAbstraction, minimization, mComputeHoareAnnotation,
					getIteration(), predicateFactoryRefinement, MINIMIZE_EVERY_KTH_ITERATION,
					mStoredRawInterpolantAutomata, mInterpolAutomaton, MINIMIZATION_TIMEOUT, resultCheckPredFac,
					lcsProvider, true);
		} catch (final AutomataMinimizationTimeout e) {
			mCegarLoopBenchmark.addAutomataMinimizationData(e.getStatistics());
			throw e.getAutomataOperationCanceledException();
		}
		mCegarLoopBenchmark.addAutomataMinimizationData(am.getStatistics());
		final boolean newAutomatonWasBuilt = am.newAutomatonWasBuilt();

		if (newAutomatonWasBuilt) {
			// postprocessing after minimization
			final IDoubleDeckerAutomaton<L, IPredicate> newAbstraction = am.getMinimizedAutomaton();

			// extract Hoare annotation
			if (mComputeHoareAnnotation) {
				final Map<IPredicate, IPredicate> oldState2newState = am.getOldState2newStateMapping();
				if (oldState2newState == null) {
					throw new AssertionError("Hoare annotation and " + minimization + " incompatible");
				}
			}

			// statistics
			final int oldSize = mAbstraction.size();
			final int newSize = newAbstraction.size();
			assert oldSize == 0 || oldSize >= newSize : "Minimization increased state space";

			// use result
			mAbstraction = newAbstraction;
		}
	}

	/*
	 * Each worker now owns its PathProgramCache. The shared cache that used to live here was handed
	 * to workers by reference (PathProgramCache.copyProgramCache aliases rather than copies) and is
	 * not synchronized, so sharing it became a race once workers run continuously.
	 *
	 * reportFailedContinuesWorkerThread() was removed with it: it built a replacement worker but
	 * never submitted it to the executor, so it only ever wasted a solver, and it read
	 * mCounterexample, which main no longer owns. A crashed worker is now handled by iterate(),
	 * which drops it from mLiveWorkers so that all-parked detection stays reachable.
	 */
}
