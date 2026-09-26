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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.absint;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.BlockingQueue;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.icfg.Call;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RCFGLiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IVariableMappedTermProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalTermUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.initializer.FixpointEngineParameterFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ICegarNwaWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ParallelNwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WorkerThreadResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WorkerThreadResult.WorkerType;

/**
 * Single-shot worker of {@link ParallelNwaCegarLoop} running abstract interpretation on the initial abstraction, with
 * one domain after the other: SAFE as soon as one proves no error state reachable, otherwise each fixpoint is
 * published to an {@link AbsIntInvariantStore}. The fixpoint runs off the main thread on main-script variables, so it
 * must not touch the main script; the constructor (main thread) does all ICFG-dependent setup and skips the domains
 * for which the fixpoint would.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class AbsIntWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {

	private record DomainRun(String domain,
			Supplier<? extends IAbstractInterpretationResult<?, IcfgEdge, IPredicate>> fixpoint) {
	}

	private final ILogger mLogger;
	private final BlockingQueue<WorkerThreadResult<L, A>> mResultQueue;
	private final AbsIntInvariantStore mStore;
	private final TermTransferrer mMainToStore;
	// Why the worker cannot run at all, or null
	private final String mUnsupported;
	private final List<DomainRun> mRuns;

	/**
	 * @param domains
	 *            the simple class names of flat AbstractInterpretationV2 domains, in the order in which they run
	 */
	public AbsIntWorkerThread(final ILogger logger, final IUltimateServiceProvider services,
			final INestedWordAutomaton<L, IPredicate> abstraction, final IIcfg<?> icfg,
			final ManagedScript mainScript, final AbsIntInvariantStore store, final List<String> domains,
			final BlockingQueue<WorkerThreadResult<L, A>> resultQueue) {
		mLogger = logger;
		mResultQueue = resultQueue;
		mStore = store;
		mMainToStore = new TermTransferrer(mainScript.getScript(), store.getScript().getScript());

		NwaTransitionProvider transitionProvider = null;
		String unsupported = null;
		try {
			transitionProvider = new NwaTransitionProvider(abstraction);
		} catch (final UnsupportedOperationException e) {
			unsupported = e.getMessage();
		}
		mUnsupported = unsupported;
		mRuns = transitionProvider == null ? List.of() : prepareRuns(services, icfg, transitionProvider, domains);
	}

	private List<DomainRun> prepareRuns(final IUltimateServiceProvider services, final IIcfg<?> icfg,
			final NwaTransitionProvider transitionProvider, final List<String> domains) {
		// The collector walks the ICFG's edge lists, which workers mutate when they transfer letters, and the octagon
		// domain asks for it again during the fixpoint. So collect once, here on the main thread.
		final RCFGLiteralCollector literals = new RCFGLiteralCollector(icfg);
		final FixpointEngineParameterFactory factory =
				new FixpointEngineParameterFactory(icfg, () -> literals, services);
		final boolean hasCallWithArguments =
				transitionProvider.getActions().stream().anyMatch(AbsIntWorkerThread::isCallWithArguments);

		final List<DomainRun> runs = new ArrayList<>();
		for (final String domain : domains) {
			final FixpointEngineParameters<?, IcfgEdge, IProgramVarOrConst, IPredicate> params = factory
					.createParams(services.getProgressMonitorService(), transitionProvider, new RcfgLoopDetector<>(),
							domain);
			// On a return, NonrelationalPostOperator translates the call's arguments into terms of the main script.
			// Asking for the post operator also creates it, here on the main thread.
			if (hasCallWithArguments
					&& params.getAbstractDomain().getPostOperator() instanceof NonrelationalPostOperator<?, ?>) {
				mLogger.warn("AbsInt: skipping %s, it would use the main script on the calls with arguments this "
						+ "program has", domain);
				continue;
			}
			runs.add(new DomainRun(domain,
					prepareFixpoint(params, transitionProvider, mStore.getScript().getScript())));
		}
		return runs;
	}

	private static boolean isCallWithArguments(final IcfgEdge action) {
		return action instanceof Call && ((Call) action).getCallStatement().getArguments().length > 0;
	}

	/**
	 * Binds the domain's state type, which is only known at runtime.
	 */
	private static <STATE extends IAbstractState<STATE>>
			Supplier<IAbstractInterpretationResult<STATE, IcfgEdge, IPredicate>> prepareFixpoint(
					final FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, IPredicate> params,
					final NwaTransitionProvider transitionProvider, final Script script) {
		// The default debug helper checks every post with the SMT solver when assertions are enabled.
		final FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, IPredicate> solverFreeParams =
				params.setDebugHelper((preState, hierachicalPreState, postState, transition) -> true);
		// The engine only stores the script, it never builds a term in it.
		return () -> new FixpointEngine<>(solverFreeParams).run(transitionProvider.getInitialStates(), script);
	}

	@Override
	public void run() {
		Thread.currentThread().setName("AbsInt Thread");
		try {
			mResultQueue.put(analyze());
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
		} catch (final Throwable t) {
			mLogger.error("AbsInt worker crashed: " + t);
			for (final StackTraceElement element : t.getStackTrace()) {
				mLogger.error("\tat " + element);
			}
			try {
				mResultQueue.put(new WorkerThreadResult<>(WorkerType.ABSINT, null, null, null, null, null, true));
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
		}
	}

	private WorkerThreadResult<L, A> analyze() {
		if (mUnsupported != null) {
			mLogger.warn("AbsInt: not running, " + mUnsupported);
			return WorkerThreadResult.noVerdict(WorkerType.ABSINT);
		}
		for (final DomainRun run : mRuns) {
			final IAbstractInterpretationResult<?, IcfgEdge, IPredicate> result;
			try {
				result = run.fixpoint().get();
			} catch (final ToolchainCanceledException e) {
				mLogger.warn("AbsInt: stopped during %s, %s", run.domain(), e.getMessage());
				return WorkerThreadResult.noVerdict(WorkerType.ABSINT);
			} catch (final UnsupportedOperationException e) {
				mLogger.warn("AbsInt: %s gave up, %s", run.domain(), e.getMessage());
				continue;
			}
			if (!result.hasReachedError()) {
				mLogger.info("AbsInt: %s proves that no error state is reachable, the program is safe", run.domain());
				return new WorkerThreadResult<>(WorkerType.ABSINT, null, null, null, null, null, false);
			}
			try {
				final Map<IPredicate, Term> invariants = toStoreTerms(result);
				mStore.publish(invariants);
				mLogger.info("AbsInt: published invariants of %d state(s) found by %s", invariants.size(),
						run.domain());
			} catch (final UnsupportedOperationException e) {
				mLogger.warn("AbsInt: cannot publish the invariants of %s, %s", run.domain(), e.getMessage());
			}
		}
		mLogger.info("AbsInt: all domains done");
		return WorkerThreadResult.noVerdict(WorkerType.ABSINT);
	}

	private Map<IPredicate, Term> toStoreTerms(final IAbstractInterpretationResult<?, IcfgEdge, IPredicate> result) {
		final Script storeScript = mStore.getScript().getScript();
		final Map<IPredicate, Term> invariants = new HashMap<>();
		for (final Entry<IPredicate, ?> entry : result.getLoc2SingleStates().entrySet()) {
			if (!(entry.getValue() instanceof IVariableMappedTermProvider)) {
				throw new UnsupportedOperationException(
						entry.getValue().getClass().getSimpleName() + " cannot be turned into terms of another script");
			}
			invariants.put(entry.getKey(),
					((IVariableMappedTermProvider) entry.getValue()).getTerm(storeScript, this::storeTermOf));
		}
		return invariants;
	}

	/**
	 * Only reads the main-script term of the variable; the copy is built in the store's script.
	 */
	private Term storeTermOf(final IProgramVarOrConst variable) {
		return mMainToStore.transform(NonrelationalTermUtils.getTermVar(variable));
	}
}
