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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * The difference of the abstraction and an automaton a worker built, for the threaded {@link ParallelNwaCegarLoop} and
 * the coordinator of the multi-process trace abstraction. The worker already enhanced its automaton, so the
 * difference here never enhances. The subtrahend must consist of predicates of the main script.
 */
public final class WorkerAutomatonDifference {

	private static final boolean REMOVE_DEAD_ENDS = true;

	private WorkerAutomatonDifference() {
		// static helpers only
	}

	/**
	 * Computes the difference and, if a proof is computed, updates the proof producer.
	 *
	 * @param counterexample
	 *            the word the worker checked, only for a debug message
	 * @param proofUpdater
	 *            the proof producer of the loop, or null if no proof is computed
	 */
	public static <L extends IIcfgTransition<?>> IOpWithDelayedDeadEndRemoval<L, IPredicate> compute(
			final IUltimateServiceProvider services, final ILogger logger, final TAPreferences pref,
			final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final AutomatonType automatonType, final NestedWord<L> counterexample,
			final PredicateFactoryRefinement stateFactoryForRefinement,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final NwaHoareProofProducer<L> proofUpdater, final CegarLoopStatisticsGenerator benchmark)
			throws AutomataLibraryException {
		logger.debug("Start constructing difference");
		if (logger.isDebugEnabled()
				&& !new Accepts<>(new AutomataLibraryServices(services), minuend, counterexample).getResult()) {
			logger.debug("Counterexample of worker result is no longer accepted by the abstraction");
		}

		final PowersetDeterminizer<L, IPredicate> psd =
				new PowersetDeterminizer<>(subtrahend, true, predicateFactoryInterpolantAutomata);
		// As in NwaCegarLoop: a proof needs the states that the sigma-star exploitation would skip.
		final boolean exploitSigmaStarConcatOfIa = automatonType.equals(AutomatonType.INTERPOLANT)
				&& (proofUpdater == null || proofUpdater.exploitSigmaStarConcatOfIa());
		final IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;
		if (pref.differenceSenwa()) {
			diff = new DifferenceSenwa<>(new AutomataLibraryServices(services), stateFactoryForRefinement, minuend,
					subtrahend, psd, false);
		} else {
			diff = new Difference<>(new AutomataLibraryServices(services), stateFactoryForRefinement, minuend,
					subtrahend, psd, exploitSigmaStarConcatOfIa);
		}
		benchmark.reportInterpolantAutomatonStates(subtrahend.size());

		if (REMOVE_DEAD_ENDS) {
			if (proofUpdater != null) {
				// SENWA is rejected by the loops if they compute a proof
				final Difference<L, IPredicate> difference = (Difference<L, IPredicate>) diff;
				proofUpdater.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
			}
			diff.removeDeadEnds();
			if (proofUpdater != null) {
				proofUpdater.addDeadEndDoubleDeckers(diff);
			}
		}
		return diff;
	}
}
