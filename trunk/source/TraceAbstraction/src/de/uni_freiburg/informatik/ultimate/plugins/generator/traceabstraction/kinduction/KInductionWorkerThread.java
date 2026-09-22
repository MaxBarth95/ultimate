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
import java.util.List;
import java.util.concurrent.BlockingQueue;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ICegarNwaWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ParallelNwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TransferBetweenMainAndWorker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TransferBetweenMainAndWorker.TransferMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WorkerThreadResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WorkerThreadTask;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPostconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;

/**
 * Worker thread running {@link KInduction} inside {@link ParallelNwaCegarLoop}'s thread pool, modeled directly on
 * {@code InterpolModelCheckingWorkerThread} (same constructor shape, same single-shot {@link #run()} behavior, same
 * {@link WorkerThreadResult} sentinel when the program is safe).
 * <p>
 * When k-induction refutes the program, {@link KInduction} reconstructs a concrete run from the solver's model and
 * this class reports it the same way {@code CegarNwaWorkerThread} reports a feasible counterexample: it runs the
 * counterexample through the refinement engine to obtain an {@code IcfgProgramExecution} with values, registers
 * {@code Result.UNSAFE} on the shared result builder, and hands the main thread a result marked
 * {@link AutomatonType#ERROR} so that it terminates instead of refining. Unlike IMC's worker it carries no
 * error-automaton scaffolding: the whole program is refuted at once, so there is nothing left to refine.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class KInductionWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {
	private final ILogger mLogger;
	private final TAPreferences mPref;
	private final CegarLoopResultBuilder mResultBuilder;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final PredicateFactory mPredicateFactory;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	private int mIteration;
	private final boolean mComputeHoareAnnotation;
	private final TaCheckAndRefinementPreferences<L> mTaCheckAndRefinementPrefs;
	public final ParallelNwaCegarLoop<L, A> mMainThread;
	private final INestedWordAutomaton<L, IPredicate> mAbstraction;
	// communication with controller
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	private final BlockingQueue<WorkerThreadTask<L>> mWorkerTaskQueue;
	private final TransferBetweenMainAndWorker<L, IPredicate> mNwaCexTransferrer;
	private final TaskIdentifier mTaskIdentifier;
	private final IInvariantSupplier<CallNode<IPredicate>> mInvariantSupplier;
	// Only used to build a refinement strategy for a counterexample; k-induction has no path-program history.
	private final PathProgramCache<L> mProgramCache;

	public KInductionWorkerThread(final ILogger logger, final TAPreferences pref, final int id,
			final CegarLoopResultBuilder resultBuilder, final IUltimateServiceProvider services,
			final CfgSmtToolkit cfgSmtToolkit, final PredicateFactory predicateFactory,
			final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final BlockingQueue<WorkerThreadTask<L>> workerTaskQueue,
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils, final TaskIdentifier taskIdentifier,
			final IInvariantSupplier<CallNode<IPredicate>> invariantSupplier) throws InterruptedException {
		mLogger = logger;
		mPref = pref;
		mIteration = id;
		mResultBuilder = resultBuilder;
		mServices = services;
		mCfgSmtToolkit = cfgSmtToolkit;
		mTaCheckAndRefinementPrefs = taCheckAndRefinementPrefs;
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mComputeHoareAnnotation = computeHoareAnnotation;
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;
		mWorkerTaskQueue = workerTaskQueue;
		mNwaCexTransferrer = transferWorkerUtils;
		mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAndTransferAbstraction();
		mTaskIdentifier = taskIdentifier;
		mInvariantSupplier = invariantSupplier;
		mProgramCache = new PathProgramCache<>(mLogger);
	}

	@Override
	public void run() {
		Thread.currentThread().setName("KInduction Thread");
		while (!Thread.currentThread().isInterrupted()) {
			try {
				mLogger.info("WorkerThread for KInduction Starts");
				mIteration = 1;

				switch (runKInduction()) {
				case SAFE:
					mBlockingQueueForResults
							.put(new WorkerThreadResult<>(WorkerType.KINDUCTION, null, null, null, null, null, false));
					return;
				case UNSAFE:
					// The violation is already registered on the shared result builder. AutomatonType.ERROR is what
					// tells the main thread that this is a refutation and not the "safe" sentinel, which carries a
					// null automaton type; no subtrahend, because there is nothing left to refine.
					mBlockingQueueForResults.put(new WorkerThreadResult<>(WorkerType.KINDUCTION, null,
							AutomatonType.ERROR, null, null, null, false));
					return;
				case NO_VERDICT:
					mBlockingQueueForResults.put(WorkerThreadResult.noVerdict(WorkerType.KINDUCTION));
					return;
				default:
					throw new AssertionError("unknown k-induction verdict");
				}

			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			} catch (final Throwable t) {
				mLogger.error("KInduction worker crashed: " + t);
				for (final StackTraceElement element : t.getStackTrace()) {
					mLogger.error("\tat " + element);
				}
				try {
					mBlockingQueueForResults
							.put(new WorkerThreadResult<>(WorkerType.KINDUCTION, null, null, null, null, null, true));
				} catch (final InterruptedException e) {
					e.printStackTrace();
				}
			}
			return;
		}
	}

	private enum Verdict {
		SAFE, UNSAFE, NO_VERDICT
	}

	private Verdict runKInduction() throws AutomataLibraryException, InterruptedException {
		final KInduction<L, IPredicate> kInduction = new KInduction<>(mServices, mLogger, mTaCheckAndRefinementPrefs,
				mCfgSmtToolkit, mAbstraction, mTaskIdentifier, this, mPref, mInvariantSupplier);
		if (kInduction.wasUnkown()) {
			// Not a crash: the encoding is fine, the query was just not decided. Retiring this worker leaves the
			// other workers - and, if there are none, the main thread's UNKNOWN result - to speak for the program.
			// The unrolling bound and a solver that gave up are entirely different situations, so name which one.
			mLogger.warn("KInduction: " + kInduction.getInconclusive());
			return Verdict.NO_VERDICT;
		}
		if (kInduction.isSafe()) {
			return Verdict.SAFE;
		}
		// No transfer: the run is built over the worker's own abstraction with worker-script letters, and the
		// refinement engine below runs on the worker toolkit, exactly as in CegarNwaWorkerThread.
		reportCounterexample(kInduction.getCounterexample());
		return Verdict.UNSAFE;
	}

	/**
	 * Registers a k-induction counterexample as {@code Result.UNSAFE}, going through the same refinement engine
	 * {@code CegarNwaWorkerThread} uses, so that the reported program execution carries variable values and
	 * backtranslates to the input program like any other counterexample.
	 */
	private void reportCounterexample(final NestedRun<L, IPredicate> counterexample) {
		final List<IcfgLocation> locations = new ArrayList<>();
		for (final IPredicate state : counterexample.getStateSequence()) {
			if (!(state instanceof ISLPredicate)) {
				throw new KInductionCounterexampleException("abstraction state " + state + " is a "
						+ state.getClass().getSimpleName() + ", not an ISLPredicate, so it has no program point");
			}
			locations.add(((ISLPredicate) state).getProgramPoint());
		}
		final Counterexample<L> cex = new Counterexample<>(counterexample.getWord(), locations);

		final StrategyFactory<L> strategyFactory = new StrategyFactory<>(mLogger, mPref, mTaCheckAndRefinementPrefs,
				mCfgSmtToolkit, mPredicateFactory, mPredicateFactoryInterpolantAutomata,
				mMainThread.mTransitionClazz, mProgramCache);
		final ITARefinementStrategy<L> strategy = strategyFactory.constructStrategy(mServices, cex, mAbstraction,
				new SubtaskIterationIdentifier(mTaskIdentifier, mIteration), mPredicateFactoryInterpolantAutomata,
				IPreconditionProvider.constructDefaultPreconditionProvider(),
				IPostconditionProvider.constructDefaultPostconditionProvider(), mPref.getRefinementStrategy());
		final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementResult =
				new TraceAbstractionRefinementEngine<>(mServices, mLogger, strategy).getResult();

		final LBool feasibility = refinementResult.getCounterexampleFeasibility();
		if (feasibility != LBool.SAT) {
			// Not an unsupported case: k-induction and the letter-level semantics of the very same abstraction
			// cannot both be right here, so one of the two encodings is wrong.
			throw new AssertionError("k-induction refuted the program, but the trace check of the reconstructed "
					+ "run answered " + feasibility + " instead of sat. The k-induction encoding and the "
					+ "letter-level semantics of the abstraction disagree. Run: " + counterexample.getWord());
		}

		final IProgramExecution<L, Term> programExecution;
		if (refinementResult.providesIcfgProgramExecution()) {
			programExecution = refinementResult.getIcfgProgramExecution();
		} else {
			programExecution = TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(counterexample.getWord());
		}
		((IcfgProgramExecution<L>) programExecution).setOriginCfgScript(mCfgSmtToolkit.getManagedScript());

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
