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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

/**
 * Copies the part of an automaton that is reachable from its initial states into a {@link NestedWordAutomaton}. For an
 * on-demand automaton in read-only mode (an enhanced interpolant automaton after the difference), that is the part
 * the difference explored.
 */
public final class ExploredAutomaton {

	private ExploredAutomaton() {
		// static helpers only
	}

	/**
	 * @return the reachable part of {@code automaton}, over the same alphabet
	 */
	public static <L, S> NestedWordAutomaton<L, S> copy(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> automaton,
			final IEmptyStackStateFactory<S> emptyStackFactory) {
		final NestedWordAutomaton<L, S> result =
				new NestedWordAutomaton<>(services, automaton.getVpAlphabet(), emptyStackFactory);
		final Set<S> states = new LinkedHashSet<>();
		final Set<S> hierPreds = new LinkedHashSet<>();
		hierPreds.add(automaton.getEmptyStackState());
		final Deque<S> worklist = new ArrayDeque<>();
		for (final S initial : automaton.getInitialStates()) {
			addState(result, automaton, states, worklist, initial);
		}
		boolean changed = true;
		while (changed) {
			while (!worklist.isEmpty()) {
				final S state = worklist.poll();
				for (final OutgoingInternalTransition<L, S> t : automaton.internalSuccessors(state)) {
					addState(result, automaton, states, worklist, t.getSucc());
					result.addInternalTransition(state, t.getLetter(), t.getSucc());
				}
				for (final OutgoingCallTransition<L, S> t : automaton.callSuccessors(state)) {
					addState(result, automaton, states, worklist, t.getSucc());
					result.addCallTransition(state, t.getLetter(), t.getSucc());
					hierPreds.add(state);
				}
			}
			// return transitions need a hierarchical predecessor; new call states may add some
			changed = false;
			for (final S state : new ArrayList<>(states)) {
				for (final S hier : new ArrayList<>(hierPreds)) {
					if (!states.contains(hier) && !hier.equals(automaton.getEmptyStackState())) {
						continue;
					}
					final List<OutgoingReturnTransition<L, S>> returns = new ArrayList<>();
					automaton.returnSuccessorsGivenHier(state, hier).forEach(returns::add);
					for (final OutgoingReturnTransition<L, S> t : returns) {
						if (hier.equals(automaton.getEmptyStackState())) {
							throw new UnsupportedOperationException(
									"Return transition from the empty stack in an automaton of the exchange");
						}
						if (!states.contains(t.getSucc())) {
							changed = true;
						}
						addState(result, automaton, states, worklist, t.getSucc());
						// the loop visits a pair of state and hierarchical predecessor again after a change
						if (!containsReturn(result, state, hier, t)) {
							result.addReturnTransition(state, hier, t.getLetter(), t.getSucc());
						}
					}
				}
			}
		}
		return result;
	}

	private static <L, S> boolean containsReturn(final NestedWordAutomaton<L, S> nwa, final S state, final S hier,
			final OutgoingReturnTransition<L, S> transition) {
		for (final OutgoingReturnTransition<L, S> t : nwa.returnSuccessors(state, hier, transition.getLetter())) {
			if (t.getSucc().equals(transition.getSucc())) {
				return true;
			}
		}
		return false;
	}

	private static <L, S> void addState(final NestedWordAutomaton<L, S> result,
			final INwaOutgoingLetterAndTransitionProvider<L, S> automaton, final Set<S> states, final Deque<S> worklist,
			final S state) {
		if (states.add(state)) {
			result.addState(automaton.isInitial(state), automaton.isFinal(state), state);
			worklist.add(state);
		}
	}
}
