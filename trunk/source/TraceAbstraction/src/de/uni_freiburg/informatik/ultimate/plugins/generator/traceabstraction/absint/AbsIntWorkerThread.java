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
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RCFGLiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IVariableMappedTermProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalTermUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.initializer.FixpointEngineParameterFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ICegarNwaWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ParallelNwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WorkerThreadResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.invariants.IInvariantSink;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.invariants.InvariantMessage.TrustedInvariants;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.invariants.InvariantSupplier;

/**
 * Single-shot worker of {@link ParallelNwaCegarLoop} running abstract interpretation on the initial abstraction, with
 * one domain after the other: SAFE as soon as one proves no error state reachable, otherwise each fixpoint is
 * submitted to the {@link InvariantSupplier} as invariants of the program locations. The fixpoint runs off the main
 * thread on main-script variables, so it must not touch the main script; the constructor (main thread) does all
 * ICFG-dependent setup and turns off the parts of the post operators that would. The terms are built in a script of
 * the worker's own, which only it builds terms in. Each domain gets a time budget; one that runs out gives no result.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class AbsIntWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {

	/**
	 * @param fixpoint
	 *            computes the fixpoint, stopping when the given timer runs out
	 */
	private record DomainRun(String domain,
			Function<IProgressAwareTimer, ? extends IAbstractInterpretationResult<?, IcfgEdge, IPredicate>> fixpoint) {
	}

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final long mDomainBudgetMs;
	private final long mHeapBudgetBytes;
	private final BlockingQueue<WorkerThreadResult<L, A>> mResultQueue;
	private final IInvariantSink mSink;
	// Only this worker builds terms in it; the supplier reads them.
	private final ManagedScript mTermScript;
	private final TermTransferrer mMainToTermScript;
	// Why the worker cannot run at all, or null
	private final String mUnsupported;
	private final List<DomainRun> mRuns;

	/**
	 * @param domains
	 *            the simple class names of flat AbstractInterpretationV2 domains, in the order in which they run
	 * @param domainBudgetSeconds
	 *            how long each domain may run; one that runs out gives no result and the next one starts
	 * @param heapBudgetPercent
	 *            how much of the JVM's maximum heap may be in use while a domain runs; a domain that exceeds it is
	 *            stopped like one that runs out of time
	 */
	public AbsIntWorkerThread(final ILogger logger, final IUltimateServiceProvider services,
			final INestedWordAutomaton<L, IPredicate> abstraction, final IIcfg<?> icfg,
			final CfgSmtToolkit mainCsToolkit, final IInvariantSink sink, final List<String> domains,
			final int domainBudgetSeconds, final int heapBudgetPercent,
			final BlockingQueue<WorkerThreadResult<L, A>> resultQueue) {
		if (domainBudgetSeconds <= 0) {
			throw new IllegalArgumentException("The time budget per domain must be positive: " + domainBudgetSeconds);
		}
		if (heapBudgetPercent < 1 || heapBudgetPercent > 100) {
			throw new IllegalArgumentException(
					"The memory budget per domain must be 1 to 100 % of the maximum heap: " + heapBudgetPercent);
		}
		mLogger = logger;
		mServices = services;
		mDomainBudgetMs = domainBudgetSeconds * 1000L;
		mHeapBudgetBytes = Runtime.getRuntime().maxMemory() / 100 * heapBudgetPercent;
		mResultQueue = resultQueue;
		mSink = sink;
		// Only used to build terms, never to solve, so an in-process SMTInterpol suffices. Created here, on the main
		// thread, because the main script's declarations are replayed onto it.
		mTermScript = mainCsToolkit.createFreshManagedScript(services,
				SolverBuilder.constructSolverSettings().setSolverLogics(Logics.ALL), "AbsIntTerms", "absint_");
		mMainToTermScript = new TermTransferrer(mainCsToolkit.getManagedScript().getScript(), mTermScript.getScript());

		NwaTransitionProvider transitionProvider = null;
		NwaLoopDetector loopDetector = null;
		String unsupported = null;
		try {
			transitionProvider = new NwaTransitionProvider(abstraction);
			loopDetector = new NwaLoopDetector(transitionProvider);
		} catch (final UnsupportedOperationException e) {
			unsupported = e.getMessage();
		}
		mUnsupported = unsupported;
		mRuns = unsupported != null ? List.of()
				: prepareRuns(services, icfg, transitionProvider, loopDetector, domains);
	}

	private List<DomainRun> prepareRuns(final IUltimateServiceProvider services, final IIcfg<?> icfg,
			final NwaTransitionProvider transitionProvider, final NwaLoopDetector loopDetector,
			final List<String> domains) {
		// The collector walks the ICFG's edge lists, which workers mutate when they transfer letters, and the octagon
		// domain asks for it again during the fixpoint. So collect once, here on the main thread.
		final RCFGLiteralCollector literals = new RCFGLiteralCollector(icfg);
		final FixpointEngineParameterFactory factory =
				new FixpointEngineParameterFactory(icfg, () -> literals, services);
		mLogger.info("AbsInt: widening at %d loop head(s)", loopDetector.getLoopHeads().size());

		final List<DomainRun> runs = new ArrayList<>();
		for (final String domain : domains) {
			final FixpointEngineParameters<?, IcfgEdge, IProgramVarOrConst, IPredicate> params = factory
					.createParams(services.getProgressMonitorService(), transitionProvider, loopDetector,
							domain);
			final Function<IProgressAwareTimer, ? extends IAbstractInterpretationResult<?, IcfgEdge, IPredicate>>
					fixpoint = prepareFixpoint(params, transitionProvider, mTermScript.getScript());
			// Asking for the post operator also creates it, here on the main thread.
			if (params.getAbstractDomain().getPostOperator() instanceof NonrelationalPostOperator<?, ?>) {
				final NonrelationalPostOperator<?, ?> postOperator =
						(NonrelationalPostOperator<?, ?>) params.getAbstractDomain().getPostOperator();
				// On a return it would translate the call's arguments into terms of the main script.
				postOperator.setRefineArgumentsOnReturn(false);
				// A single post can take longer than the whole budget.
				runs.add(new DomainRun(domain, timer -> {
					postOperator.setTimer(timer);
					return fixpoint.apply(timer);
				}));
			} else {
				runs.add(new DomainRun(domain, fixpoint));
			}
		}
		return runs;
	}

	/**
	 * Binds the domain's state type, which is only known at runtime.
	 */
	private static <STATE extends IAbstractState<STATE>>
			Function<IProgressAwareTimer, IAbstractInterpretationResult<STATE, IcfgEdge, IPredicate>> prepareFixpoint(
					final FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, IPredicate> params,
					final NwaTransitionProvider transitionProvider, final Script script) {
		// The default debug helper checks every post with the SMT solver when assertions are enabled.
		final FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, IPredicate> solverFreeParams =
				params.setDebugHelper((preState, hierachicalPreState, postState, transition) -> true);
		// The engine only stores the script, it never builds a term in it.
		return timer -> new FixpointEngine<>(solverFreeParams.setTimer(timer))
				.run(transitionProvider.getInitialStates(), script);
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
			// Created here, the budget starts now.
			final HeapBudgetTimer timer = new HeapBudgetTimer(
					mServices.getProgressMonitorService().getChildTimer(mDomainBudgetMs), mHeapBudgetBytes);
			try {
				result = run.fixpoint().apply(timer);
			} catch (final ToolchainCanceledException e) {
				if (timer.isHeapBudgetExceeded()) {
					mLogger.warn("AbsInt: %s exceeded its memory budget (%d MB of heap in use, budget %d MB)",
							run.domain(), timer.getHeapUsedWhenExceeded() >> 20, mHeapBudgetBytes >> 20);
					// Most of the heap is the domain's garbage. Collecting it now lets the JVM shrink its heap
					// instead of keeping it committed while the other workers and their solvers need the memory.
					System.gc();
					continue;
				}
				if (mServices.getProgressMonitorService().continueProcessing()) {
					mLogger.warn("AbsInt: %s ran out of its %d s budget", run.domain(), mDomainBudgetMs / 1000);
					continue;
				}
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
				final Map<IcfgLocation, Term> invariants = toTerms(result);
				mSink.submit(new TrustedInvariants(mTermScript, invariants, "AbsInt " + run.domain()));
				mLogger.info("AbsInt: submitted invariants of %d location(s) found by %s", invariants.size(),
						run.domain());
			} catch (final UnsupportedOperationException e) {
				mLogger.warn("AbsInt: cannot publish the invariants of %s, %s", run.domain(), e.getMessage());
			}
		}
		mLogger.info("AbsInt: all domains done");
		return WorkerThreadResult.noVerdict(WorkerType.ABSINT);
	}

	/**
	 * The fixpoint as invariants of program locations, in {@link #mTermScript}. Two states of one location, which the
	 * initial abstraction does not have, would be joined by a disjunction.
	 */
	private Map<IcfgLocation, Term> toTerms(final IAbstractInterpretationResult<?, IcfgEdge, IPredicate> result) {
		final Script termScript = mTermScript.getScript();
		final Map<IcfgLocation, Term> invariants = new HashMap<>();
		for (final Entry<IPredicate, ?> entry : result.getLoc2SingleStates().entrySet()) {
			if (!(entry.getValue() instanceof IVariableMappedTermProvider)) {
				throw new UnsupportedOperationException(
						entry.getValue().getClass().getSimpleName() + " cannot be turned into terms of another script");
			}
			final Term term = ((IVariableMappedTermProvider) entry.getValue()).getTerm(termScript, this::termOf);
			invariants.merge(InvariantSupplier.locationOf(entry.getKey()), term,
					(older, newer) -> SmtUtils.or(termScript, older, newer));
		}
		return invariants;
	}

	/**
	 * Only reads the main-script term of the variable; the copy is built in the worker's own script.
	 */
	private Term termOf(final IProgramVarOrConst variable) {
		return mMainToTermScript.transform(NonrelationalTermUtils.getTermVar(variable));
	}
}
