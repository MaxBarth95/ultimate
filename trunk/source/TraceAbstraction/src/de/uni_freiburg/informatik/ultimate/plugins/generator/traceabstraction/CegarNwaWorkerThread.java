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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TransferBetweenMainAndWorker.Mode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorGeneralizationEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IpTcStrategyModuleAcceleratedTraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

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
	private final ErrorGeneralizationEngine<L> mErrorGeneralizationEngine;
	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> mRefinementResult = null;
	private NestedWordAutomaton<L, IPredicate> mInterpolAutomaton = null;
	private IRun<L, ?> mCounterexample = null;
	private final TaCheckAndRefinementPreferences<L> mTaCheckAndRefinementPrefs;
	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	private final boolean mComputeHoareAnnotation;
	private IcfgLocation mCurrentErrorLoc;
	private final SimplificationTechnique mSimplificationTechnique;
	protected static final boolean REMOVE_DEAD_ENDS = true;
	private final ParallelNwaCegarLoop<L, A> mMainThread;
	/**
	 * This worker's own abstraction. It is searched by this worker for counterexamples, replaced by
	 * this worker's difference, and minimized by this worker. It shrinks only through this worker's
	 * own refinements, so it drifts away from main's abstraction and from the other workers'.
	 */
	private INestedWordAutomaton<L, IPredicate> mAbstraction;
	private final int mWorkerId;
	/** True while we have not yet searched the current abstraction; a plain BFS is worth trying. */
	private boolean mAbstractionChangedSinceLastSearch = true;
	/**
	 * Worker-local: AutomataMinimization *adds to* this collection under NWA_OVERAPPROXIMATION, so
	 * it must not be shared with main or with another worker.
	 */
	private final Collection<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mStoredRawInterpolantAutomata =
			new ArrayList<>();
	private static final int MINIMIZE_EVERY_KTH_ITERATION = 10;
	private static final int MINIMIZATION_TIMEOUT = 1_000;
	private StrategyFactory<L> mStrategyFactory;
	// communication with controller
	private WorkerThreadResult<L, A> mThreadResult = null;
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	private final TransferBetweenMainAndWorker<L, IPredicate> mNwaCexTransferrer;

	private final PathProgramCache<L> mProgramCache;

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
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils) throws InterruptedException {

		mLogger = logger;
		mPref = pref;
		mIteration = id;
		mWorkerId = id;
		mResultBuilder = resultBuilder;
		mErrorGeneralizationEngine = new ErrorGeneralizationEngine<>(services);
		mServices = services;
		mCfgSmtToolkit = cfgSmtToolkit;
		mTaCheckAndRefinementPrefs = taCheckAndRefinementPrefs;
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mComputeHoareAnnotation = computeHoareAnnotation;
		mSimplificationTechnique = pref.getSimplificationTechnique();
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;
		mNwaCexTransferrer = transferWorkerUtils;
		mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAbstraction();
		mProgramCache = new PathProgramCache<>(mLogger);

		final Thread.UncaughtExceptionHandler exhandler = (th, ex) -> {
			mThreadResult = new WorkerThreadResult<>(null, null, null, false, null, false, AutomatonType.ERROR, null,
					mCounterexample, null, true);
			try {
				mBlockingQueueForResults.put(mThreadResult);
			} catch (final InterruptedException e) {
				throw new AssertionError("Worker Thread failed due to " + e);
			}
			// The crash marker above is enough: main drops this worker from its live count so that
			// all-parked detection stays reachable. Nothing may touch main's counters from here,
			// this runs on a worker thread.
		};
		Thread.currentThread().setUncaughtExceptionHandler(exhandler);

	}

	/*
	 * Searches this worker's own abstraction for a counterexample and claims it in the set shared by
	 * all workers, so no two workers ever analyse the same trace. Then sets up a strategy (checks how
	 * often the pathprogram has been seen), checks feasibility, interpolates, creates an Error or
	 * Interpolant automaton, computes the difference — which becomes this worker's new abstraction,
	 * minimized in place — and puts a @WorkerThreadResult into the blocking queue for results.
	 *
	 * If no fresh counterexample can be found, the worker resyncs its abstraction from main and tries
	 * once more; only then does it report itself idle and park.
	 *
	 * Terminates if the Thread is interrupted (not used atm) or the Executioner service triggers a shutdown.
	 */
	@Override
	public void run() {
		while (!Thread.currentThread().isInterrupted()) {
			try {
				// Read before searching: if main bumps the generation while we search, we must not
				// park on a stale observation.
				final int generationBeforeSearch = mMainThread.getResyncGeneration();

				NestedRun<L, IPredicate> cex = searchForFreshCounterexample();
				if (cex == null) {
					// Our abstraction only ever shrinks by our *own* differences, so without a
					// resync we would never see the other workers' progress and could starve
					// forever on traces they have already claimed.
					resyncAbstractionFromMain();
					cex = searchForFreshCounterexample();
				}
				if (cex == null) {
					mLogger.info("Worker %s found no fresh counterexample, parking.", mWorkerId);
					// Enqueue *before* parking, or main can block on an empty result queue forever.
					mBlockingQueueForResults.put(WorkerThreadResult.noCounterexampleFound(mWorkerId));
					mMainThread.awaitResync(generationBeforeSearch);
					continue;
				}

				mIteration += 1;
				mCounterexample = cex;
				mProgramCache.addRun(cex.getWord());
				final List<L> trace = cex.getWord().asList();
				mCurrentErrorLoc = cex.getSymbol(cex.getLength() - 2).getTarget();
				final int traceHash = trace.hashCode();
				mLogger.info("Starting Thread: " + Thread.currentThread().getId() + "# for Trace Check: " + traceHash);
				Thread.currentThread().setName("Worker for " + traceHash);
				try {
					final var locations = getControlConfigurationsFromCounterexample(mCounterexample);
					final Counterexample<L> counterexample = new Counterexample<>(mCounterexample.getWord(), locations);
					final ITARefinementStrategy<L> strategy = setUpStrategy(counterexample);
					final Pair<LBool, IProgramExecution<L, Term>> isCexResult = isCounterexampleFeasible(strategy);

					final AbstractCegarLoop.AutomatonType automatonType = processFeasibilityCheckResult(strategy,
							isCexResult.getFirst(), isCexResult.getSecond(), mCurrentErrorLoc);
					constructRefinementAutomaton(automatonType);
					mThreadResult = refineAbstractionInternally();
				} catch (AutomataLibraryException | ToolchainCanceledException | SMTLIBException e) {
					throw new AssertionError("WorkerThread Failed: " + e);
				}
				mLogger.info("Done with Thread: " + Thread.currentThread().getId() + "#");
				mBlockingQueueForResults.put(mThreadResult);
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			} catch (final AutomataOperationCanceledException e) {
				mLogger.warn("Worker %s cancelled while searching: %s", mWorkerId, e);
				return;
			}
		}
	}

	/**
	 * Search this worker's own abstraction for a counterexample that no worker has claimed yet, and
	 * claim it atomically.
	 *
	 * Losing the claim race is expected, not an error: another worker searched concurrently and got
	 * there first. We then search again, but only with IsEmptyParallel — a plain BFS would just
	 * hand back the same trace. Returns null if nothing fresh can be found.
	 */
	private NestedRun<L, IPredicate> searchForFreshCounterexample() throws AutomataOperationCanceledException {
		boolean tryBfsFirst = mAbstractionChangedSinceLastSearch;
		while (true) {
			final NestedRun<L, IPredicate> cex = searchForErrorTrace(!tryBfsFirst);
			mAbstractionChangedSinceLastSearch = false;
			if (cex == null) {
				return null;
			}
			if (mMainThread.claimCounterexample(cex)) {
				return cex;
			}
			mLogger.info("Worker %s lost the claim race, searching again.", mWorkerId);
			tryBfsFirst = false;
		}
	}

	/*
	 * Search for an error trace in this worker's abstraction. On a freshly changed abstraction we try
	 * BFS first, otherwise only IsEmptyParallel, which diverges from every already-claimed trace.
	 */
	private NestedRun<L, IPredicate> searchForErrorTrace(final boolean onlyDoIsEmptyParallel)
			throws AutomataOperationCanceledException {
		IsEmpty<L, IPredicate> search;
		if (!onlyDoIsEmptyParallel) {
			search = new IsEmpty<>(new AutomataLibraryServices(getServices()), mAbstraction,
					IsEmpty.SearchStrategy.BFS);
			if (isSearchCorrectAndTraceFresh(search)) {
				mLogger.info("Worker %s found a new counterexample via BFS!", mWorkerId);
				return search.getNestedRun();
			}
		}
		search = new IsEmptyParallel<>(new AutomataLibraryServices(getServices()), mAbstraction,
				mAbstraction.getInitialStates(), Collections.emptySet(), null, true, IsEmpty.SearchStrategy.BFS,
				mMainThread.getActiveCounterexamples(), mPref.getSearchLoopBound());
		if (isSearchCorrectAndTraceFresh(search)) {
			mLogger.info("Worker %s found a new counterexample via IsEmptyParallel!", mWorkerId);
			return search.getNestedRun();
		}
		mLogger.info("Worker %s did not find a counterexample.", mWorkerId);
		return null;
	}

	// If search was BFS, the counterexample might not be fresh.
	private boolean isSearchCorrectAndTraceFresh(final IsEmpty<L, IPredicate> search) {
		boolean correct = false;
		try {
			correct = search.checkResult(mStateFactoryForRefinement);
		} catch (final AutomataLibraryException e) {
			e.printStackTrace();
			assert false;
		}
		final NestedRun<L, IPredicate> run = search.getNestedRun();
		if (run == null) {
			return false;
		}
		final boolean fresh = !mMainThread.getActiveCounterexamples().containsKey(run.getWord().asList().hashCode());
		return correct && fresh;
	}

	/**
	 * Replace this worker's abstraction with main's current one, which has every worker's
	 * refinements applied. Expensive (a full automaton walk plus TransFormula transfer), so this is
	 * done only when we are starved, never per task.
	 */
	private void resyncAbstractionFromMain() {
		mLogger.info("Worker %s resyncing its abstraction from main.", mWorkerId);
		mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAbstraction();
		mAbstractionChangedSinceLastSearch = true;
	}

	/**
	 * Minimize this worker's own abstraction. Deliberately does not call the CEGAR loop's
	 * minimizeAbstraction: that is an instance method which mutates the loop's abstraction and its
	 * mCegarLoopBenchmark, whose named stopwatches throw when started concurrently.
	 */
	private void minimizeOwnAbstraction() throws AutomataOperationCanceledException, AutomataLibraryException {
		final Minimization minimization = mPref.getMinimization();
		if (minimization == Minimization.NONE) {
			return;
		}
		final Function<IPredicate, Set<IcfgLocation>> lcsProvider =
				x -> (x instanceof ISLPredicate ? Collections.singleton(((ISLPredicate) x).getProgramPoint())
						: new HashSet<>(Arrays.asList(((IMLPredicate) x).getProgramPoints())));
		final AutomataMinimization<Set<IcfgLocation>, IPredicate, L> am;
		try {
			am = new AutomataMinimization<>(getServices(), mAbstraction, minimization, mComputeHoareAnnotation,
					mIteration, mStateFactoryForRefinement, MINIMIZE_EVERY_KTH_ITERATION,
					mStoredRawInterpolantAutomata, mInterpolAutomaton, MINIMIZATION_TIMEOUT,
					new PredicateFactoryResultChecking(mPredicateFactory), lcsProvider, true);
		} catch (final AutomataMinimizationTimeout e) {
			throw e.getAutomataOperationCanceledException();
		}
		if (am.newAutomatonWasBuilt()) {
			final IDoubleDeckerAutomaton<L, IPredicate> minimized = am.getMinimizedAutomaton();
			assert mAbstraction.size() == 0 || mAbstraction.size() >= minimized.size()
					: "Minimization increased state space";
			mAbstraction = minimized;
		}
	}

	protected List<?> getControlConfigurationsFromCounterexample(final IRun<L, ?> run) {
		return getIcfgLocationsFromRun(run);
	}

	private List<IcfgLocation> getIcfgLocationsFromRun(final IRun<L, ?> run) {
		return run.getStateSequence().stream().map(p -> ((ISLPredicate) p).getProgramPoint())
				.collect(Collectors.toList());
	}

	/*
	 * The worker creates for each counterexample a new strategy module. We can switch between different
	 * RefinementStrateies here. For example we can use {@link RefinementStrategy.ACCELERATED_TRACE_CHECK} if we have
	 * seen the pp 7 times.
	 *
	 * if (mStrategyFactory.getPathProgramCache().getPathProgramCount(mCounterexample.getWord()) == 7 ) { strategy =
	 * mStrategyFactory.constructStrategy(getServices(), counterexample, mAbstraction, new
	 * SubtaskIterationIdentifier(mMainThread.mTaskIdentifier, mIteration), mPredicateFactoryInterpolantAutomata,
	 * getPreconditionProvider(), getPostconditionProvider(), RefinementStrategy.ACCELERATED_TRACE_CHECK); }
	 *
	 * Warning, we have shared (read and write) access to the PathProgramCache here. But the PathProgramCache uses
	 * thread save lists and maps.
	 */
	private ITARefinementStrategy<L> setUpStrategy(final Counterexample<L> counterexample) {
		mStrategyFactory = new StrategyFactory<>(mLogger, mPref, mTaCheckAndRefinementPrefs, mCfgSmtToolkit,
				mPredicateFactory, mPredicateFactoryInterpolantAutomata, mMainThread.mTransitionClazz, mProgramCache);

		final ITARefinementStrategy<L> strategy;
		strategy = mStrategyFactory.constructStrategy(getServices(), counterexample, mAbstraction,
				new SubtaskIterationIdentifier(mMainThread.mTaskIdentifier, mIteration),
				mPredicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider(),
				mPref.getRefinementStrategy());
		return strategy;
	}

	/**
	 * Worker takes the current abstraction from the main thread (read only). Then transfers it to worker script.
	 */
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getAbstraction() {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mainAbstraction = mMainThread.getAbstraction();
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> workerAbstraction = mNwaCexTransferrer
				.transferAutomaton(mainAbstraction, mPredicateFactoryInterpolantAutomata, Mode.MAIN2WORKER);
		return workerAbstraction;
	}

	private IPreconditionProvider getPreconditionProvider() {
		return IPreconditionProvider.constructDefaultPreconditionProvider();
	}

	private IPostconditionProvider getPostconditionProvider() {
		return IPostconditionProvider.constructDefaultPostconditionProvider();
	}

	protected Pair<LBool, IProgramExecution<L, Term>>
			isCounterexampleFeasible(final ITARefinementStrategy<L> strategy) {
		try {
			if (mPref.hasLimitPathProgramCount() && mPref.getLimitPathProgramCount() < mStrategyFactory
					.getPathProgramCache().getPathProgramCount(mCounterexample.getWord())) {
				final String taskDescription = "bailout by path program count limit in iteration " + mIteration;
				throw new TaskCanceledException(UserDefinedLimit.PATH_PROGRAM_ATTEMPTS, getClass(), taskDescription);
			}

			final TraceAbstractionRefinementEngine<L> refinementEngine =
					new TraceAbstractionRefinementEngine<>(getServices(), mLogger, strategy);
			mRefinementResult = refinementEngine.getResult();

		} catch (final ToolchainCanceledException | SMTLIBException tce) {
			throw tce;
		}
		final LBool feasibility = mRefinementResult.getCounterexampleFeasibility();
		IProgramExecution<L, Term> rcfgProgramExecution = null;
		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample %s feasible", feasibility == LBool.SAT ? "is" : "might be");
			if (mRefinementResult.providesIcfgProgramExecution()) {
				rcfgProgramExecution = mRefinementResult.getIcfgProgramExecution();
			} else {
				rcfgProgramExecution =
						TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(mCounterexample.getWord());
			}
			((IcfgProgramExecution<L>) rcfgProgramExecution).setOriginCfgScript(mCfgSmtToolkit.getManagedScript());
		}
		// TODO use some kind of mCegarLoopBenchmark (currently leads to concurrency problems)
		return new Pair<>(feasibility, rcfgProgramExecution);
	}

	/**
	 * Report results from a feasibility check if necessary and return the type of the refinement automaton
	 *
	 * @param strategy
	 */
	private AbstractCegarLoop.AutomatonType processFeasibilityCheckResult(final ITARefinementStrategy<L> strategy,
			final LBool isCounterexampleFeasible, final IProgramExecution<L, Term> programExecution,
			final IcfgLocation currentErrorLoc) {
		if (isCounterexampleFeasible == Script.LBool.SAT) {
			mResultBuilder.addResultForProgramExecution(Result.UNSAFE, programExecution, null, null);
			if (mPref.stopAfterFirstViolation()) {
				mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
			}
			return AbstractCegarLoop.AutomatonType.ERROR;
		}
		if (isCounterexampleFeasible != Script.LBool.UNKNOWN) {
			return AbstractCegarLoop.AutomatonType.INTERPOLANT;
		}
		Result actualResult;
		if (programExecution != null) {
			for (final ITraceCheckStrategyModule<L, ?> module : strategy.getTraceCheckModules()) {
				if (module instanceof IpTcStrategyModuleAcceleratedTraceCheck) {
					throw new AssertionError(
							"TraceCheck Unknown, dont return result. Might be just this Strategy that fails");
				}
			}
			final UnprovabilityReason reasonUnknown =
					new UnprovabilityReason("unable to decide satisfiability of path constraint");
			actualResult = Result.UNKNOWN;
			mResultBuilder.addResultForProgramExecution(actualResult, programExecution, null, reasonUnknown);
		}
		actualResult = Result.TIMEOUT;
		mResultBuilder.addResult(currentErrorLoc, actualResult, null, null, null);

		if (mPref.stopAfterFirstViolation()) {
			mResultBuilder.addResultForAllRemaining(actualResult);
		}

		return AbstractCegarLoop.AutomatonType.UNKNOWN;
	}

	/**
	 * This Method does not do the sanity checks done in NWA for the correctness of Error and Interpolant automata!
	 *
	 * @param automatonType
	 * @throws AutomataOperationCanceledException
	 */
	private void constructRefinementAutomaton(final AbstractCegarLoop.AutomatonType automatonType)
			throws AutomataOperationCanceledException {
		switch (automatonType) {
		case ERROR:
		case UNKNOWN:
			mLogger.info("Excluding counterexample to continue analysis with %s automaton", automatonType);
			mErrorGeneralizationEngine.constructErrorAutomaton(mCounterexample, mPredicateFactory,
					mRefinementResult.getPredicateUnifier(), mCfgSmtToolkit, mSimplificationTechnique,
					mCfgSmtToolkit.getSymbolTable(), mPredicateFactoryInterpolantAutomata, mAbstraction, mIteration);
			mInterpolAutomaton = null;
			break;
		case INTERPOLANT:
			mInterpolAutomaton = mRefinementResult.getInfeasibilityProof();
			break;
		default:
			throw new UnsupportedOperationException("Unknown automaton type: " + automatonType);
		}
	}

	protected IUltimateServiceProvider getServices() {
		return mServices;
	}

	private WorkerThreadResult<L, A> refineAbstractionInternally() throws AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(mIteration);
		// mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final IPredicateUnifier predicateUnifier = mRefinementResult.getPredicateUnifier();
		final IHoareTripleChecker htc = getHoareTripleChecker();

		final AutomatonType automatonType;
		final boolean useErrorAutomaton;
		final NestedWordAutomaton<L, IPredicate> subtrahendBeforeEnhancement;
		final InterpolantAutomatonEnhancement enhanceMode;
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		final boolean exploitSigmaStarConcatOfIa;
		if (mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration)) {
			mErrorGeneralizationEngine.startDifference();
			automatonType = AutomatonType.ERROR;
			useErrorAutomaton = true;
			exploitSigmaStarConcatOfIa = false;
			enhanceMode = mErrorGeneralizationEngine.getEnhancementMode();
			subtrahendBeforeEnhancement = mErrorGeneralizationEngine.getResultBeforeEnhancement();
			subtrahend = mErrorGeneralizationEngine.getResultAfterEnhancement();

		} else {
			automatonType = AutomatonType.FLOYD_HOARE;
			useErrorAutomaton = false;
			exploitSigmaStarConcatOfIa = !mComputeHoareAnnotation;
			subtrahendBeforeEnhancement = mInterpolAutomaton;
			enhanceMode = mPref.interpolantAutomatonEnhancement();
			subtrahend = enhanceInterpolantAutomaton(enhanceMode, predicateUnifier, htc, subtrahendBeforeEnhancement);

		}

		mLogger.info("Difference in Worker");
		final IOpWithDelayedDeadEndRemoval<L, IPredicate> diff =
				computeAutomataDifference(mAbstraction, subtrahend, subtrahendBeforeEnhancement, predicateUnifier,
						exploitSigmaStarConcatOfIa, htc, enhanceMode, useErrorAutomaton, automatonType);
		// Keep the difference as this worker's own abstraction instead of discarding it, then
		// minimize it. Dead ends were already removed above, which minimization requires.
		mAbstraction = diff.getResult();
		mAbstractionChangedSinceLastSearch = true;
		if (mPref.minimizeAbstractionPerWorker()) {
			minimizeOwnAbstraction();
		}

		final WorkerThreadResult<L, A> workerResult = new WorkerThreadResult<>(
				mNwaCexTransferrer.transferAutomaton(subtrahend, mPredicateFactoryInterpolantAutomata,
						Mode.WORKER2MAIN),
				mNwaCexTransferrer.transferAutomaton(subtrahendBeforeEnhancement, mPredicateFactoryInterpolantAutomata,
						Mode.WORKER2MAIN),
				predicateUnifier, exploitSigmaStarConcatOfIa, enhanceMode, useErrorAutomaton, automatonType,
				mCfgSmtToolkit.getManagedScript(),
				mNwaCexTransferrer.transferRun((NestedRun<L, ?>) mCounterexample, Mode.WORKER2MAIN), mPredicateFactory,
				false);

		// TODO missing a lot of stuff from NwaCegarLoop

		return workerResult;
	}

	/*
	 * The difference against this worker's own abstraction. It serves two purposes: it forces the
	 * on-demand enhancement of the interpolant automaton, and its result becomes this worker's new
	 * abstraction. Main still computes the authoritative difference against the global abstraction.
	 *
	 * Unlike before, this runs even when enhanceMode is NONE, because the worker needs the result
	 * either way. That configuration is already exercised by the sequential NwaCegarLoop and by
	 * main itself, so it needs no special alphabet handling.
	 */
	private IOpWithDelayedDeadEndRemoval<L, IPredicate> computeAutomataDifference(
			final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final IPredicateUnifier predicateUnifier, final boolean explointSigmaStarConcatOfIA,
			final IHoareTripleChecker htc, final InterpolantAutomatonEnhancement enhanceMode,
			final boolean useErrorAutomaton, final AutomatonType automatonType)
			throws AutomataLibraryException, AssertionError {
		try {
			mLogger.debug("WORKER: Start constructing difference for enhancing interpolant automaton in worker");
			final PowersetDeterminizer<L, IPredicate> psd =
					new PowersetDeterminizer<>(subtrahend, true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;
			try {
				if (mPref.differenceSenwa()) {
					diff = new DifferenceSenwa<>(new AutomataLibraryServices(getServices()), mStateFactoryForRefinement,
							minuend, subtrahend, psd, false);
				} else {
					diff = new Difference<>(new AutomataLibraryServices(getServices()), mStateFactoryForRefinement,
							minuend, subtrahend, psd, explointSigmaStarConcatOfIA);
				}
			} catch (final AutomataOperationCanceledException | ToolchainCanceledException tce) {
				final RunningTaskInfo runningTaskInfo = executeDifferenceTimeoutActions(minuend, subtrahend,
						subtrahendBeforeEnhancement, automatonType);
				tce.addRunningTaskInfo(runningTaskInfo);
				throw tce;
			} finally {
				if (enhanceMode != InterpolantAutomatonEnhancement.NONE) {
					assert subtrahend instanceof AbstractInterpolantAutomaton
							: "if enhancement is used, we need AbstractInterpolantAutomaton";
					((AbstractInterpolantAutomaton<L>) subtrahend).switchToReadonlyMode();
				}
			}

			if (REMOVE_DEAD_ENDS) {
				if (mComputeHoareAnnotation) {
					// TODO missing stuff
				}
				diff.removeDeadEnds();
			}
			return diff;
		} finally {
			mLogger.info(predicateUnifier.collectPredicateUnifierStatistics());
			mLogger.info(htc.getStatistics());
			mLogger.info(htc);
			mLogger.debug("WORKER: Finished constructing difference");
		}

	}

	private RunningTaskInfo executeDifferenceTimeoutActions(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final AutomatonType automatonType) throws AutomataLibraryException {
		final RunningTaskInfo runningTaskInfo =
				getDifferenceTimeoutRunningTaskInfo(minuend, subtrahend, subtrahendBeforeEnhancement, automatonType);
		return runningTaskInfo;
	}

	private RunningTaskInfo getDifferenceTimeoutRunningTaskInfo(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final AutomatonType automatonType) {
		final String taskDescription = "WORKER: constructing difference of abstraction (" + minuend.size()
				+ "states) and " + automatonType + " automaton (currently " + subtrahend.size() + " states, "
				+ subtrahendBeforeEnhancement.size() + " states before enhancement)";
		return new RunningTaskInfo(getClass(), taskDescription);
	}

	protected final IHoareTripleChecker getHoareTripleChecker() {
		final IHoareTripleChecker refinementHtc = mRefinementResult.getHoareTripleChecker();
		if (refinementHtc != null) {
			return refinementHtc;
		}
		final HoareTripleCheckerCache initialCache =
				TraceAbstractionUtils.extractHoareTriplesfromAutomaton(mRefinementResult.getInfeasibilityProof());
		return HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(getServices(),
				mPref.getHoareTripleChecks(), mCfgSmtToolkit, mRefinementResult.getPredicateUnifier(), initialCache);
	}

	protected INwaOutgoingLetterAndTransitionProvider<L, IPredicate> enhanceInterpolantAutomaton(
			final InterpolantAutomatonEnhancement enhanceMode, final IPredicateUnifier predicateUnifier,
			final IHoareTripleChecker htc, final NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		if (enhanceMode == InterpolantAutomatonEnhancement.NONE) {
			subtrahend = interpolantAutomaton;
		} else {
			final AbstractInterpolantAutomaton<L> ia = constructInterpolantAutomatonForOnDemandEnhancement(
					interpolantAutomaton, predicateUnifier, htc, enhanceMode);
			subtrahend = ia;
		}
		return subtrahend;
	}

	protected AbstractInterpolantAutomaton<L> constructInterpolantAutomatonForOnDemandEnhancement(
			final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final InterpolantAutomatonEnhancement enhanceMode) {
		final AbstractInterpolantAutomaton<L> result;
		switch (enhanceMode) {
		case NONE:
			throw new IllegalArgumentException("In setting NONE we will not do any enhancement");
		case PREDICATE_ABSTRACTION:
		case PREDICATE_ABSTRACTION_CONSERVATIVE:
		case PREDICATE_ABSTRACTION_CANNIBALIZE:
			result = constructInterpolantAutomatonForOnDemandEnhancementPredicateAbstraction(inputInterpolantAutomaton,
					predicateUnifier, htc, enhanceMode);
			break;
		case EAGER:
		case NO_SECOND_CHANCE:
		case EAGER_CONSERVATIVE:
			result = constructInterpolantAutomatonForOnDemandEnhancementEager(inputInterpolantAutomaton,
					predicateUnifier, htc, enhanceMode);
			break;
		default:
			throw new UnsupportedOperationException("unknown " + enhanceMode);
		}
		return result;
	}

	private NondeterministicInterpolantAutomaton<L> constructInterpolantAutomatonForOnDemandEnhancementEager(
			final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final InterpolantAutomatonEnhancement enhanceMode) {
		final boolean conservativeSuccessorCandidateSelection =
				enhanceMode == InterpolantAutomatonEnhancement.EAGER_CONSERVATIVE;
		final boolean secondChance = enhanceMode != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE;
		return new NondeterministicInterpolantAutomaton<>(getServices(), mCfgSmtToolkit, htc, inputInterpolantAutomaton,
				predicateUnifier, conservativeSuccessorCandidateSelection, secondChance);
	}

	private DeterministicInterpolantAutomaton<L>
			constructInterpolantAutomatonForOnDemandEnhancementPredicateAbstraction(
					final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
					final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
					final InterpolantAutomatonEnhancement enhanceMode) {
		final boolean conservativeSuccessorCandidateSelection =
				enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE;
		final boolean cannibalize = enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE;
		return new DeterministicInterpolantAutomaton<>(getServices(), mCfgSmtToolkit, htc, inputInterpolantAutomaton,
				predicateUnifier, conservativeSuccessorCandidateSelection, cannibalize);
	}
}
