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

import java.util.concurrent.BlockingQueue;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.icfg.Call;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RCFGLiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array.ArrayDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.initializer.FixpointEngineParameterFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ICegarNwaWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ParallelNwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WorkerThreadResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WorkerThreadResult.WorkerType;

/**
 * Single-shot worker of {@link ParallelNwaCegarLoop} running abstract interpretation on the initial abstraction: SAFE
 * if no error state is reachable, otherwise the fixpoint is left behind as an {@link AbsIntInvariantSupplier}. The
 * fixpoint runs off the main thread on main-script variables, so it must not touch the main script; the constructor
 * (main thread) does all ICFG-dependent setup and refuses domains and programs for which it would.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class AbsIntWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {

	private final ILogger mLogger;
	private final ManagedScript mMainScript;
	private final BlockingQueue<WorkerThreadResult<L, A>> mResultQueue;
	// Exactly one of the two is non-null.
	private final Supplier<? extends IAbstractInterpretationResult<?, IcfgEdge, IPredicate>> mFixpoint;
	private final String mUnsupported;

	public AbsIntWorkerThread(final ILogger logger, final IUltimateServiceProvider services,
			final INestedWordAutomaton<L, IPredicate> abstraction, final IIcfg<?> icfg,
			final ManagedScript mainScript, final BlockingQueue<WorkerThreadResult<L, A>> resultQueue) {
		mLogger = logger;
		mMainScript = mainScript;
		mResultQueue = resultQueue;

		final NwaTransitionProvider transitionProvider;
		try {
			transitionProvider = new NwaTransitionProvider(abstraction);
		} catch (final UnsupportedOperationException e) {
			mUnsupported = e.getMessage();
			mFixpoint = null;
			return;
		}

		// The collector walks the ICFG's edge lists, which workers mutate when they transfer letters, and the octagon
		// domain asks for it again during the fixpoint. So collect once, here on the main thread.
		final RCFGLiteralCollector literals = new RCFGLiteralCollector(icfg);
		final FixpointEngineParameters<?, IcfgEdge, IProgramVarOrConst, IPredicate> params =
				new FixpointEngineParameterFactory(icfg, () -> literals, services)
						.createParams(services.getProgressMonitorService(), transitionProvider, new RcfgLoopDetector<>());

		final IAbstractDomain<?, IcfgEdge> domain = params.getAbstractDomain();
		if (domain instanceof ArrayDomain<?> || domain instanceof CompoundDomain) {
			throw new UnsupportedOperationException("The abstract interpretation worker does not support the "
					+ domain.getClass().getSimpleName() + ": it uses the SMT solver during the fixpoint computation");
		}
		// On a return, NonrelationalPostOperator translates the call's arguments into terms of the main script.
		if (domain.getPostOperator() instanceof NonrelationalPostOperator<?, ?>
				&& transitionProvider.getActions().stream().anyMatch(AbsIntWorkerThread::isCallWithArguments)) {
			mUnsupported = domain.getClass().getSimpleName()
					+ " would use the SMT solver on calls with arguments, which this program has";
			mFixpoint = null;
			return;
		}
		mUnsupported = null;
		mFixpoint = prepareFixpoint(params, transitionProvider, mainScript.getScript());
	}

	private static boolean isCallWithArguments(final IcfgEdge action) {
		return action instanceof Call && ((Call) action).getCallStatement().getArguments().length > 0;
	}

	/**
	 * Binds the domain's state type, which is only known at runtime.
	 */
	private static <STATE extends IAbstractState<STATE>>
			Supplier<IAbstractInterpretationResult<STATE, IcfgEdge, IPredicate>> prepareFixpoint(final FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, IPredicate> params,
					final NwaTransitionProvider transitionProvider, final Script mainScript) {
		// The default debug helper checks every post with the SMT solver when assertions are enabled.
		final FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, IPredicate> solverFreeParams =
				params.setDebugHelper((preState, hierachicalPreState, postState, transition) -> true);
		// The script is only stored, for turning the fixpoint into terms on demand.
		return () -> new FixpointEngine<>(solverFreeParams).run(transitionProvider.getInitialStates(), mainScript);
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
		final IAbstractInterpretationResult<?, IcfgEdge, IPredicate> result;
		try {
			result = mFixpoint.get();
		} catch (final ToolchainCanceledException | UnsupportedOperationException e) {
			mLogger.warn("AbsInt: no verdict, " + e.getMessage());
			return WorkerThreadResult.noVerdict(WorkerType.ABSINT);
		}
		if (!result.hasReachedError()) {
			mLogger.info("AbsInt: no error state is reachable, the program is safe");
			return new WorkerThreadResult<>(WorkerType.ABSINT, null, null, null, null, null, false);
		}
		mLogger.info("AbsInt: an error state may be reachable, leaving the fixpoint behind as invariants");
		return WorkerThreadResult.noVerdictWithInvariants(WorkerType.ABSINT,
				new AbsIntInvariantSupplier(result, mMainScript));
	}
}
