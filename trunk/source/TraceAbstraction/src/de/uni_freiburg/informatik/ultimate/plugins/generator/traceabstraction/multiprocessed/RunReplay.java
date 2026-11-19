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

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * Finds the accepting run of a nested word in a nested word automaton. A TA worker gets only the word of a
 * counterexample and rebuilds the run through its own copy of the abstraction.
 *
 * The search follows every configuration (state and stack of call predecessors) letter by letter, so it also works for
 * a nondeterministic automaton. It throws if the automaton does not accept the word.
 */
public final class RunReplay {

	/**
	 * A configuration of the search, with the configuration it came from.
	 */
	private record Config<S>(S state, Stack<S> stack, Config<S> previous) {
	}

	/**
	 * The call predecessors of a configuration, innermost first; null is the empty stack.
	 */
	private record Stack<S>(S top, Stack<S> rest) {
	}

	private record Key<S>(S state, Stack<S> stack) {
	}

	private RunReplay() {
		// static helpers only
	}

	/**
	 * @return an accepting run of {@code word} in {@code nwa}
	 * @throws IllegalArgumentException
	 *             if {@code nwa} does not accept {@code word}
	 */
	public static <L, S> NestedRun<L, S> replay(final INestedWordAutomaton<L, S> nwa, final NestedWord<L> word) {
		Map<Key<S>, Config<S>> layer = new LinkedHashMap<>();
		for (final S initial : nwa.getInitialStates()) {
			layer.put(new Key<>(initial, null), new Config<>(initial, null, null));
		}
		for (int i = 0; i < word.length(); i++) {
			final L letter = word.getSymbol(i);
			final Map<Key<S>, Config<S>> next = new LinkedHashMap<>();
			for (final Config<S> config : layer.values()) {
				if (word.isInternalPosition(i)) {
					for (final OutgoingInternalTransition<L, S> t : nwa.internalSuccessors(config.state(), letter)) {
						add(next, t.getSucc(), config.stack(), config);
					}
				} else if (word.isCallPosition(i)) {
					final Stack<S> pushed = new Stack<>(config.state(), config.stack());
					for (final OutgoingCallTransition<L, S> t : nwa.callSuccessors(config.state(), letter)) {
						add(next, t.getSucc(), pushed, config);
					}
				} else {
					final Stack<S> stack = config.stack();
					if (stack == null && !word.isPendingReturn(i)) {
						throw new IllegalArgumentException("Return at position " + i + " without its call");
					}
					final S hier = stack == null ? nwa.getEmptyStackState() : stack.top();
					final Stack<S> popped = stack == null ? null : stack.rest();
					for (final OutgoingReturnTransition<L, S> t : nwa.returnSuccessors(config.state(), hier,
							letter)) {
						add(next, t.getSucc(), popped, config);
					}
				}
			}
			if (next.isEmpty()) {
				throw new IllegalArgumentException(
						"The automaton does not accept the word: no run reads position " + i + " (" + letter + ")");
			}
			layer = next;
		}
		for (final Config<S> config : layer.values()) {
			if (nwa.isFinal(config.state())) {
				return toRun(word, config);
			}
		}
		throw new IllegalArgumentException("The automaton does not accept the word: no run ends in a final state");
	}

	private static <S> void add(final Map<Key<S>, Config<S>> next, final S succ, final Stack<S> stack,
			final Config<S> previous) {
		next.putIfAbsent(new Key<>(succ, stack), new Config<>(succ, stack, previous));
	}

	private static <L, S> NestedRun<L, S> toRun(final NestedWord<L> word, final Config<S> last) {
		final List<S> states = new ArrayList<>(word.length() + 1);
		for (Config<S> config = last; config != null; config = config.previous()) {
			states.add(config.state());
		}
		final List<S> forward = new ArrayList<>(states.size());
		for (int i = states.size() - 1; i >= 0; i--) {
			forward.add(states.get(i));
		}
		return new NestedRun<>(word, forward);
	}
}
