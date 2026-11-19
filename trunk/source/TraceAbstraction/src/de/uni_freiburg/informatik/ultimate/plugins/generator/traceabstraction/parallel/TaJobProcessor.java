/*
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel;

import java.util.List;
import java.util.function.BooleanSupplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPostconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorGeneralizationEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IpTcStrategyModuleAcceleratedTraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;

/**
 * The work of a TA worker on one counterexample: the trace check, and then the automaton that the coordinator refines
 * with. Shared by the TA worker threads of {@link ParallelNwaCegarLoop} and the TA worker processes of the
 * multi-process trace abstraction.
 *
 * A job has two steps, so that the caller records the verdict of the trace check before the automaton is built: the
 * difference that enhances the automaton may run out of time, and that must not lose a feasible counterexample.
 * <ol>
 * <li>{@link #checkFeasibility} runs the trace check and returns its verdict.</li>
 * <li>{@link #constructAutomaton} builds the interpolant automaton (infeasible) or the error automaton (feasible or
 * unknown) and enhances it by a difference with the abstraction.</li>
 * </ol>
 *
 * A processor has no state shared with other workers; each worker has its own. The difference only enhances the
 * automaton; the real difference is computed by the coordinator (or the main thread).
 *
 * @param <L>
 *            the letter type
 */
public final class TaJobProcessor<L extends IIcfgTransition<?>> {

	private static final boolean REMOVE_DEAD_ENDS = true;

	/**
	 * The verdict of the trace check of one job.
	 *
	 * @param status
	 *            UNSAT if the counterexample is infeasible, SAT if it is feasible, UNKNOWN otherwise
	 * @param programExecution
	 *            the execution of a feasible or unknown counterexample, null if it is infeasible or none was found
	 * @param counterexample
	 *            the checked counterexample
	 * @param abstraction
	 *            the abstraction the counterexample was taken from
	 * @param iteration
	 *            the id of the job, unique per processor
	 * @param refinementResult
	 *            the result of the refinement engine, with the interpolants of an infeasible counterexample
	 */
	public record Feasibility<L extends IIcfgTransition<?>>(LBool status, IProgramExecution<L, Term> programExecution,
			IRun<L, ?> counterexample, INestedWordAutomaton<L, IPredicate> abstraction, int iteration,
			IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementResult) {
	}

	/**
	 * The automaton of one job.
	 *
	 * @param type
	 *            {@link AutomatonType#INTERPOLANT} for an infeasible counterexample, {@link AutomatonType#ERROR}
	 *            otherwise
	 * @param automaton
	 *            the automaton after enhancement, explored as far as the difference with the abstraction needed
	 */
	public record RefinementAutomaton<L extends IIcfgTransition<?>>(AutomatonType type,
			INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton) {
	}

	private final ILogger mLogger;
	private final TAPreferences mPref;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final PredicateFactory mPredicateFactory;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	private final TaCheckAndRefinementPreferences<L> mTaCheckAndRefinementPrefs;
	// Whether the coordinator computes a proof. The worker never builds Hoare states itself, but its difference
	// decides which transitions of the subtrahend get computed, so it must explore what the coordinator explores.
	private final boolean mComputeHoareAnnotation;
	private final Class<L> mTransitionClazz;
	private final PathProgramCache<L> mProgramCache;
	private final TaskIdentifier mTaskIdentifier;
	private final SimplificationTechnique mSimplificationTechnique;
	private final ErrorGeneralizationEngine<L> mErrorGeneralizationEngine;

	public TaJobProcessor(final ILogger logger, final TAPreferences pref, final IUltimateServiceProvider services,
			final CfgSmtToolkit cfgSmtToolkit, final PredicateFactory predicateFactory,
			final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final Class<L> transitionClazz, final PathProgramCache<L> programCache,
			final TaskIdentifier taskIdentifier) {
		mLogger = logger;
		mPref = pref;
		mCfgSmtToolkit = cfgSmtToolkit;
		mPredicateFactory = predicateFactory;
		mTaCheckAndRefinementPrefs = taCheckAndRefinementPrefs;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mComputeHoareAnnotation = computeHoareAnnotation;
		mTransitionClazz = transitionClazz;
		mProgramCache = programCache;
		mTaskIdentifier = taskIdentifier;
		mSimplificationTechnique = pref.getSimplificationTechnique();
		mErrorGeneralizationEngine = new ErrorGeneralizationEngine<>(services);
	}

	/**
	 * @return the path program cache the strategies of this processor use
	 */
	public PathProgramCache<L> getPathProgramCache() {
		return mProgramCache;
	}

	/**
	 * Checks whether a counterexample is feasible.
	 *
	 * @param services
	 *            the services of this job
	 * @param counterexample
	 *            a run of the abstraction to an error location; its states must be {@link ISLPredicate}s
	 * @param abstraction
	 *            the abstraction the run belongs to
	 * @param iteration
	 *            an id of the job, unique per processor
	 * @param stopRequested
	 *            whether the job was stopped from outside (a retirement or a cancellation); an answer other than SAT
	 *            may then just be the stop and throws a {@link ToolchainCanceledException}
	 */
	public Feasibility<L> checkFeasibility(final IUltimateServiceProvider services, final IRun<L, ?> counterexample,
			final INestedWordAutomaton<L, IPredicate> abstraction, final int iteration,
			final BooleanSupplier stopRequested) {
		final List<IcfgLocation> locations = getIcfgLocationsFromRun(counterexample);
		final Counterexample<L> cex = new Counterexample<>(counterexample.getWord(), locations);
		final StrategyFactory<L> strategyFactory = new StrategyFactory<>(mLogger, mPref, mTaCheckAndRefinementPrefs,
				mCfgSmtToolkit, mPredicateFactory, mPredicateFactoryInterpolantAutomata, mTransitionClazz,
				mProgramCache);
		final ITARefinementStrategy<L> strategy = strategyFactory.constructStrategy(services, cex, abstraction,
				new SubtaskIterationIdentifier(mTaskIdentifier, iteration), mPredicateFactoryInterpolantAutomata,
				IPreconditionProvider.constructDefaultPreconditionProvider(),
				IPostconditionProvider.constructDefaultPostconditionProvider(), mPref.getRefinementStrategy());

		if (mPref.hasLimitPathProgramCount() && mPref.getLimitPathProgramCount() < strategyFactory
				.getPathProgramCache().getPathProgramCount(counterexample.getWord())) {
			final String taskDescription = "bailout by path program count limit in iteration " + iteration;
			throw new TaskCanceledException(UserDefinedLimit.PATH_PROGRAM_ATTEMPTS, getClass(), taskDescription);
		}
		final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementResult =
				new TraceAbstractionRefinementEngine<>(services, mLogger, strategy).getResult();
		final LBool feasibility = refinementResult.getCounterexampleFeasibility();
		IProgramExecution<L, Term> programExecution = null;
		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample %s feasible", feasibility == LBool.SAT ? "is" : "might be");
			if (refinementResult.providesIcfgProgramExecution()) {
				programExecution = refinementResult.getIcfgProgramExecution();
			} else {
				programExecution = TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(counterexample.getWord());
			}
			((IcfgProgramExecution<L>) programExecution).setOriginCfgScript(mCfgSmtToolkit.getManagedScript());
		}
		if (feasibility != LBool.SAT && stopRequested.getAsBoolean()) {
			// An unknown answer may just be the stop; it must not register a timeout for the error location.
			throw new ToolchainCanceledException(getClass(), "trace check of a stopped job");
		}
		if (feasibility == LBool.UNKNOWN && programExecution != null) {
			for (final ITraceCheckStrategyModule<L, ?> module : strategy.getTraceCheckModules()) {
				if (module instanceof IpTcStrategyModuleAcceleratedTraceCheck) {
					throw new AssertionError(
							"TraceCheck Unknown, dont return result. Might be just this Strategy that fails");
				}
			}
		}
		return new Feasibility<>(feasibility, programExecution, counterexample, abstraction, iteration,
				refinementResult);
	}

	/**
	 * Builds the automaton of a checked counterexample and enhances it by a difference with the abstraction.
	 *
	 * This method does not do the sanity checks of {@code NwaCegarLoop} for error and interpolant automata.
	 */
	public RefinementAutomaton<L> constructAutomaton(final IUltimateServiceProvider services,
			final Feasibility<L> feasibility) throws AutomataLibraryException {
		final int iteration = feasibility.iteration();
		final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementResult =
				feasibility.refinementResult();
		final NestedWordAutomaton<L, IPredicate> interpolantAutomaton;
		if (feasibility.status() == LBool.UNSAT) {
			interpolantAutomaton = refinementResult.getInfeasibilityProof();
		} else {
			mLogger.info("Excluding counterexample to continue analysis with %s automaton",
					feasibility.status() == LBool.SAT ? AutomatonType.ERROR : AutomatonType.UNKNOWN);
			mErrorGeneralizationEngine.constructErrorAutomaton(feasibility.counterexample(), mPredicateFactory,
					refinementResult.getPredicateUnifier(), mCfgSmtToolkit, mSimplificationTechnique,
					mCfgSmtToolkit.getSymbolTable(), mPredicateFactoryInterpolantAutomata, feasibility.abstraction(),
					iteration);
			interpolantAutomaton = null;
		}

		mStateFactoryForRefinement.setIteration(iteration);
		final IPredicateUnifier predicateUnifier = refinementResult.getPredicateUnifier();
		final IHoareTripleChecker htc = getHoareTripleChecker(services, refinementResult);

		final AutomatonType automatonType;
		final boolean useErrorAutomaton;
		final NestedWordAutomaton<L, IPredicate> subtrahendBeforeEnhancement;
		final InterpolantAutomatonEnhancement enhanceMode;
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		final boolean exploitSigmaStarConcatOfIa;
		if (mErrorGeneralizationEngine.hasAutomatonInIteration(iteration)) {
			mErrorGeneralizationEngine.startDifference();
			automatonType = AutomatonType.ERROR;
			useErrorAutomaton = true;
			exploitSigmaStarConcatOfIa = false;
			enhanceMode = mErrorGeneralizationEngine.getEnhancementMode();
			subtrahendBeforeEnhancement = mErrorGeneralizationEngine.getResultBeforeEnhancement();
			subtrahend = mErrorGeneralizationEngine.getResultAfterEnhancement();
		} else {
			automatonType = AutomatonType.INTERPOLANT;
			useErrorAutomaton = false;
			exploitSigmaStarConcatOfIa = !mComputeHoareAnnotation;
			subtrahendBeforeEnhancement = interpolantAutomaton;
			enhanceMode = mPref.interpolantAutomatonEnhancement();
			subtrahend = enhanceInterpolantAutomaton(services, enhanceMode, predicateUnifier, htc,
					subtrahendBeforeEnhancement);
		}

		mLogger.info("Difference in Worker for Generalization");
		computeAutomataDifference(services, feasibility.abstraction(), subtrahend, subtrahendBeforeEnhancement,
				predicateUnifier, exploitSigmaStarConcatOfIa, htc, enhanceMode, useErrorAutomaton, automatonType);
		return new RefinementAutomaton<>(automatonType, subtrahend);
	}

	/**
	 * @return the program points of the states of a run
	 */
	public static <L> List<IcfgLocation> getIcfgLocationsFromRun(final IRun<L, ?> run) {
		return run.getStateSequence().stream().map(p -> ((ISLPredicate) p).getProgramPoint())
				.collect(Collectors.toList());
	}

	/*
	 * WARNING The real difference has to be computed in the Main Thrad / CEGAR loop This is only used to enhance the
	 * interpolant automaton
	 */
	private IOpWithDelayedDeadEndRemoval<L, IPredicate> computeAutomataDifference(
			final IUltimateServiceProvider services, final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final IPredicateUnifier predicateUnifier, final boolean explointSigmaStarConcatOfIA,
			final IHoareTripleChecker htc, final InterpolantAutomatonEnhancement enhanceMode,
			final boolean useErrorAutomaton, final AutomatonType automatonType)
			throws AutomataLibraryException, AssertionError {
		if (enhanceMode == InterpolantAutomatonEnhancement.NONE) {
			return null;
		}
		try {
			mLogger.debug("WORKER: Start constructing difference for enhancing interpolant automaton in worker");
			final PowersetDeterminizer<L, IPredicate> psd =
					new PowersetDeterminizer<>(subtrahend, true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;
			try {
				if (mPref.differenceSenwa()) {
					diff = new DifferenceSenwa<>(new AutomataLibraryServices(services), mStateFactoryForRefinement,
							minuend, subtrahend, psd, false);
				} else {
					diff = new Difference<>(new AutomataLibraryServices(services), mStateFactoryForRefinement, minuend,
							subtrahend, psd, explointSigmaStarConcatOfIA);
				}
			} catch (final AutomataOperationCanceledException | ToolchainCanceledException tce) {
				tce.addRunningTaskInfo(
						getDifferenceTimeoutRunningTaskInfo(minuend, subtrahend, subtrahendBeforeEnhancement,
								automatonType));
				throw tce;
			} finally {
				assert subtrahend instanceof AbstractInterpolantAutomaton
						: "if enhancement is used, we need AbstractInterpolantAutomaton";
				((AbstractInterpolantAutomaton<L>) subtrahend).switchToReadonlyMode();
			}

			if (REMOVE_DEAD_ENDS) {
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

	private RunningTaskInfo getDifferenceTimeoutRunningTaskInfo(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final AutomatonType automatonType) {
		final String taskDescription = "WORKER: constructing difference of abstraction (" + minuend.size()
				+ "states) and " + automatonType + " automaton (currently " + subtrahend.size() + " states, "
				+ subtrahendBeforeEnhancement.size() + " states before enhancement)";
		return new RunningTaskInfo(getClass(), taskDescription);
	}

	private IHoareTripleChecker getHoareTripleChecker(final IUltimateServiceProvider services,
			final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementResult) {
		final IHoareTripleChecker refinementHtc = refinementResult.getHoareTripleChecker();
		if (refinementHtc != null) {
			return refinementHtc;
		}
		final HoareTripleCheckerCache initialCache =
				TraceAbstractionUtils.extractHoareTriplesfromAutomaton(refinementResult.getInfeasibilityProof());
		return HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(services,
				mPref.getHoareTripleChecks(), mCfgSmtToolkit, refinementResult.getPredicateUnifier(), initialCache);
	}

	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> enhanceInterpolantAutomaton(
			final IUltimateServiceProvider services, final InterpolantAutomatonEnhancement enhanceMode,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		if (enhanceMode == InterpolantAutomatonEnhancement.NONE) {
			return interpolantAutomaton;
		}
		return constructInterpolantAutomatonForOnDemandEnhancement(services, interpolantAutomaton, predicateUnifier,
				htc, enhanceMode);
	}

	private AbstractInterpolantAutomaton<L> constructInterpolantAutomatonForOnDemandEnhancement(
			final IUltimateServiceProvider services, final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final InterpolantAutomatonEnhancement enhanceMode) {
		switch (enhanceMode) {
		case NONE:
			throw new IllegalArgumentException("In setting NONE we will not do any enhancement");
		case PREDICATE_ABSTRACTION:
		case PREDICATE_ABSTRACTION_CONSERVATIVE:
		case PREDICATE_ABSTRACTION_CANNIBALIZE: {
			final boolean conservativeSuccessorCandidateSelection =
					enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE;
			final boolean cannibalize = enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE;
			return new DeterministicInterpolantAutomaton<>(services, mCfgSmtToolkit, htc, inputInterpolantAutomaton,
					predicateUnifier, conservativeSuccessorCandidateSelection, cannibalize);
		}
		case EAGER:
		case NO_SECOND_CHANCE:
		case EAGER_CONSERVATIVE: {
			final boolean conservativeSuccessorCandidateSelection =
					enhanceMode == InterpolantAutomatonEnhancement.EAGER_CONSERVATIVE;
			final boolean secondChance = enhanceMode != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE;
			return new NondeterministicInterpolantAutomaton<>(services, mCfgSmtToolkit, htc, inputInterpolantAutomaton,
					predicateUnifier, conservativeSuccessorCandidateSelection, secondChance);
		}
		default:
			throw new UnsupportedOperationException("unknown " + enhanceMode);
		}
	}
}
