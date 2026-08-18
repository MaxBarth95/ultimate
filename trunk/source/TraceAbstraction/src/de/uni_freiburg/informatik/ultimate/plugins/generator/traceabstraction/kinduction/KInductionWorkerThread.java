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

import java.util.concurrent.BlockingQueue;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ICegarNwaWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ParallelNwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TransferBetweenMainAndWorker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TransferBetweenMainAndWorker.TransferMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WorkerThreadResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

/**
 * Worker thread running {@link KInduction} inside {@link ParallelNwaCegarLoop}'s thread pool, modeled directly on
 * {@code InterpolModelCheckingWorkerThread} (same constructor shape, same single-shot {@link #run()} behavior,
 * same {@link WorkerThreadResult} sentinel on success). Unlike that class, this one does not carry the dead
 * counterexample-refinement scaffolding ({@code constructErrorAutomatonAndPutItInQueue} and friends) - nothing in
 * either worker's current {@link #run()} path calls it, since neither algorithm can produce a counterexample yet
 * (see {@link KInduction}'s own TODO).
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
	private INestedWordAutomaton<L, IPredicate> mAbstraction;
	// communication with controller
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	private final BlockingQueue<IRun<L, ?>> mWorkerTaskQueue;
	private final TransferBetweenMainAndWorker<L, IPredicate> mNwaCexTransferrer;
	private final TaskIdentifier mTaskIdentifier;
	private final IInvariantSupplier<IPredicate> mInvariantSupplier;

	public KInductionWorkerThread(final ILogger logger, final TAPreferences pref, final int id,
			final CegarLoopResultBuilder resultBuilder, final IUltimateServiceProvider services,
			final CfgSmtToolkit cfgSmtToolkit, final PredicateFactory predicateFactory,
			final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final BlockingQueue<IRun<L, ?>> workerTaskQueue,
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils, final TaskIdentifier taskIdentifier,
			final IInvariantSupplier<IPredicate> invariantSupplier) throws InterruptedException {
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
	}

	@Override
	public void run() {
		Thread.currentThread().setName("KInduction Thread");
		while (!Thread.currentThread().isInterrupted()) {
			try {
				mLogger.info("WorkerThread for KInduction Starts");
				mIteration = 1;

				final boolean safe = runKInduction();
				if (safe) {
					mBlockingQueueForResults.put(new WorkerThreadResult<>(null, null, null, false, null, false, null,
							null, null, null, false));
					return;
				}
				throw new AssertionError("No Support for CEX yet");

			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			} catch (final Throwable t) {
				try {
					mBlockingQueueForResults.put(new WorkerThreadResult<>(null, null, null, false, null, false, null,
							null, null, null, true));
				} catch (final InterruptedException e) {
					e.printStackTrace();
				}
			}
			return;
		}
	}

	private boolean runKInduction() throws AutomataLibraryException, InterruptedException {
		final KInduction<L, IPredicate> kInduction = new KInduction<>(mServices, mLogger, mTaCheckAndRefinementPrefs,
				mCfgSmtToolkit, mAbstraction, mTaskIdentifier, this, mPref, mInvariantSupplier);
		if (kInduction.isSafe() && !kInduction.wasOverapproximated()) {
			return true;
		}
		if (!kInduction.isSafe() && !kInduction.wasUnkown()) {
			mNwaCexTransferrer.transferRun(kInduction.getCounterexample(), TransferMode.MAIN2WORKER);
			return false;
		}
		throw new AssertionError("Loop Bound");
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
