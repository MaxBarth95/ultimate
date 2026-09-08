/*
 * Copyright (C) 2026 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;

/**
 * Given a nested word automaton and a {@link NestedWord} over (a subset of) its alphabet, constructs a new
 * {@link NestedWordAutomaton} that contains exactly the states and transitions of the operand that are reachable
 * using only letters that occur in the given nested word. This is the automaton-level analogue of the
 * {@code Library-Icfg} plugin's {@code PathProgram}, which projects an ICFG to a set of allowed transitions.
 * <p>
 * The traversal mirrors {@link IsEmpty}: reachability is tracked via {@link DoubleDecker} pairs (the state before
 * the last unmatched call, and the current state), because after a return the correct call-stack context to
 * continue with depends on which state the hierarchical predecessor was itself reached with.
 *
 * @author Max Barth
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class PathProgramNWAConstructor<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final NestedWord<LETTER> mNestedWord;
	private final NestedWordAutomaton<LETTER, STATE> mResult;

	/**
	 * Up-state -> set of down-states it was visited with. Doubles as the visited-set and as the lookup
	 * {@link #getCallStatesOfCallState(Object)} needs after a return (same trick as {@link IsEmpty}).
	 */
	private final Map<STATE, Set<STATE>> mVisitedPairs = new HashMap<>();
	private final Set<STATE> mAddedStates = new HashSet<>();
	private final ArrayDeque<DoubleDecker<STATE>> mWorklist = new ArrayDeque<>();

	public PathProgramNWAConstructor(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final NestedWord<LETTER> nestedWord,
			final IEmptyStackStateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mNestedWord = nestedWord;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = constructResult(stateFactory);
		assert assertResultIsSound(mResult) : "path program automaton contains a state/transition that is not "
				+ "justified by the operand or a letter that does not occur in the nested word";

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	/**
	 * Checks that every state and transition of {@code result} is justified: states carry the same initial/final
	 * status as in the operand, every transition's letter occurs in the nested word at a position of the matching
	 * kind (internal/call/return), and every transition also exists in the operand. This does not check
	 * completeness (that nothing reachable was omitted), only that nothing was fabricated.
	 */
	private boolean assertResultIsSound(final NestedWordAutomaton<LETTER, STATE> result) {
		final Set<LETTER> internalAlphabet = new HashSet<>();
		final Set<LETTER> callAlphabet = new HashSet<>();
		final Set<LETTER> returnAlphabet = new HashSet<>();
		for (int i = 0; i < mNestedWord.length(); i++) {
			if (mNestedWord.isInternalPosition(i)) {
				internalAlphabet.add(mNestedWord.getSymbol(i));
			} else if (mNestedWord.isCallPosition(i)) {
				callAlphabet.add(mNestedWord.getSymbol(i));
			} else {
				returnAlphabet.add(mNestedWord.getSymbol(i));
			}
		}

		for (final STATE state : result.getStates()) {
			if (result.isInitial(state) != mOperand.isInitial(state)) {
				return false;
			}
			if (result.isFinal(state) != mOperand.isFinal(state)) {
				return false;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> trans : result.internalSuccessors(state)) {
				if (!internalAlphabet.contains(trans.getLetter())) {
					return false;
				}
				if (!operandHasInternalTransition(state, trans.getLetter(), trans.getSucc())) {
					return false;
				}
			}
			for (final OutgoingCallTransition<LETTER, STATE> trans : result.callSuccessors(state)) {
				if (!callAlphabet.contains(trans.getLetter())) {
					return false;
				}
				if (!operandHasCallTransition(state, trans.getLetter(), trans.getSucc())) {
					return false;
				}
			}
			for (final OutgoingReturnTransition<LETTER, STATE> trans : result.returnSuccessors(state)) {
				if (!returnAlphabet.contains(trans.getLetter())) {
					return false;
				}
				if (!operandHasReturnTransition(state, trans.getHierPred(), trans.getLetter(), trans.getSucc())) {
					return false;
				}
			}
		}
		return true;
	}

	private boolean operandHasInternalTransition(final STATE pred, final LETTER letter, final STATE succ) {
		for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(pred, letter)) {
			if (trans.getSucc().equals(succ)) {
				return true;
			}
		}
		return false;
	}

	private boolean operandHasCallTransition(final STATE pred, final LETTER letter, final STATE succ) {
		for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(pred, letter)) {
			if (trans.getSucc().equals(succ)) {
				return true;
			}
		}
		return false;
	}

	private boolean operandHasReturnTransition(final STATE pred, final STATE hier, final LETTER letter,
			final STATE succ) {
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(pred, hier, letter)) {
			if (trans.getSucc().equals(succ)) {
				return true;
			}
		}
		return false;
	}

	private NestedWordAutomaton<LETTER, STATE> constructResult(final IEmptyStackStateFactory<STATE> stateFactory)
			throws AutomataOperationCanceledException {
		final Set<LETTER> internalAlphabet = new HashSet<>();
		final Set<LETTER> callAlphabet = new HashSet<>();
		final Set<LETTER> returnAlphabet = new HashSet<>();
		for (int i = 0; i < mNestedWord.length(); i++) {
			if (mNestedWord.isInternalPosition(i)) {
				internalAlphabet.add(mNestedWord.getSymbol(i));
			} else if (mNestedWord.isCallPosition(i)) {
				callAlphabet.add(mNestedWord.getSymbol(i));
			} else {
				assert mNestedWord.isReturnPosition(i);
				returnAlphabet.add(mNestedWord.getSymbol(i));
			}
		}

		final NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<>(mServices,
				new VpAlphabet<>(internalAlphabet, callAlphabet, returnAlphabet), stateFactory);

		for (final STATE initial : mOperand.getInitialStates()) {
			addPathProgramState(result, initial);
			enqueueAndMarkVisited(initial, mOperand.getEmptyStackState());
		}

		while (!mWorklist.isEmpty()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(
						new RunningTaskInfo(getClass(), generateGenericRunningTaskDescription()));
			}
			final DoubleDecker<STATE> pair = mWorklist.removeFirst();
			final STATE state = pair.getUp();
			final STATE stateK = pair.getDown();

			for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(state)) {
				if (!internalAlphabet.contains(trans.getLetter())) {
					continue;
				}
				final STATE succ = trans.getSucc();
				addPathProgramState(result, succ);
				result.addInternalTransition(state, trans.getLetter(), succ);
				if (!wasVisited(succ, stateK)) {
					enqueueAndMarkVisited(succ, stateK);
				}
			}

			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(state)) {
				if (!callAlphabet.contains(trans.getLetter())) {
					continue;
				}
				final STATE succ = trans.getSucc();
				addPathProgramState(result, succ);
				result.addCallTransition(state, trans.getLetter(), succ);
				if (!wasVisited(succ, state)) {
					enqueueAndMarkVisited(succ, state);
				}
			}

			// equality intended here, mirrors IsEmpty: the empty stack state has no return transitions
			if (stateK == mOperand.getEmptyStackState()) {
				continue;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessorsGivenHier(state,
					stateK)) {
				if (!returnAlphabet.contains(trans.getLetter())) {
					continue;
				}
				final STATE succ = trans.getSucc();
				addPathProgramState(result, succ);
				result.addReturnTransition(state, stateK, trans.getLetter(), succ);
				for (final STATE stateKk : getCallStatesOfCallState(stateK)) {
					if (!wasVisited(succ, stateKk)) {
						enqueueAndMarkVisited(succ, stateKk);
					}
				}
			}
		}
		return result;
	}

	private void addPathProgramState(final NestedWordAutomaton<LETTER, STATE> result, final STATE state) {
		if (mAddedStates.add(state)) {
			result.addState(mOperand.isInitial(state), mOperand.isFinal(state), state);
		}
	}

	private void enqueueAndMarkVisited(final STATE state, final STATE stateK) {
		mWorklist.addLast(new DoubleDecker<>(stateK, state));
		mVisitedPairs.computeIfAbsent(state, x -> new HashSet<>()).add(stateK);
	}

	private boolean wasVisited(final STATE state, final STATE stateK) {
		final Set<STATE> down = mVisitedPairs.get(state);
		return down != null && down.contains(stateK);
	}

	private Set<STATE> getCallStatesOfCallState(final STATE callState) {
		return mVisitedPairs.getOrDefault(callState, Collections.emptySet());
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public NestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}
}
