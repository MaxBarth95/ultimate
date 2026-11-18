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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.LetterNaming.LetterKind;

/**
 * Encodes a nested word as a list of letter names and an explicit nesting relation, the JSON form of a word.
 *
 * {@code nesting[i]} is the position of the matching return of a call at {@code i}, or of the matching call of a
 * return at {@code i}. It is {@value #INTERNAL} for an internal position, {@value #PENDING_CALL} for a call without a
 * return, and {@value #PENDING_RETURN} for a return without a call.
 */
public final class WordCodec {

	public static final int INTERNAL = -1;
	public static final int PENDING_CALL = -2;
	public static final int PENDING_RETURN = -3;

	/**
	 * A word in its JSON form.
	 *
	 * @param word
	 *            the letter names
	 * @param nesting
	 *            the nesting relation, see {@link WordCodec}
	 */
	public record EncodedWord(List<String> word, List<Integer> nesting) {
	}

	private WordCodec() {
		// static helpers only
	}

	/**
	 * @return the JSON form of a nested word
	 */
	public static <L extends IIcfgTransition<?>> EncodedWord encode(final NestedWord<L> word,
			final LetterNaming<L> naming) {
		final List<String> names = new ArrayList<>(word.length());
		final List<Integer> nesting = new ArrayList<>(word.length());
		for (int i = 0; i < word.length(); i++) {
			names.add(naming.name(word.getSymbol(i)));
			if (word.isPendingCall(i)) {
				nesting.add(PENDING_CALL);
			} else if (word.isPendingReturn(i)) {
				nesting.add(PENDING_RETURN);
			} else if (word.isCallPosition(i)) {
				nesting.add(word.getReturnPosition(i));
			} else if (word.isReturnPosition(i)) {
				nesting.add(word.getCallPosition(i));
			} else {
				nesting.add(INTERNAL);
			}
		}
		return new EncodedWord(names, nesting);
	}

	/**
	 * @return the nested word of a JSON form
	 * @throws IllegalArgumentException
	 *             if a letter is unknown, or the nesting relation is malformed or does not fit the letters
	 */
	public static <L extends IIcfgTransition<?>> NestedWord<L> decode(final EncodedWord encoded,
			final LetterNaming<L> naming) {
		final List<String> names = encoded.word();
		final List<Integer> nesting = encoded.nesting();
		if (names == null || nesting == null || names.size() != nesting.size()) {
			throw new IllegalArgumentException("A word needs as many nesting entries as letters");
		}
		final int length = names.size();
		@SuppressWarnings("unchecked")
		final L[] letters = (L[]) new IIcfgTransition<?>[length];
		final int[] relation = new int[length];
		final Deque<Integer> openCalls = new ArrayDeque<>();
		boolean pendingCallSeen = false;
		for (int i = 0; i < length; i++) {
			final L letter = naming.resolve(names.get(i));
			letters[i] = letter;
			final int n = nesting.get(i);
			final LetterKind kind = naming.kind(letter);
			switch (kind) {
			case INTERNAL:
				require(n == INTERNAL, i, "internal letter needs nesting " + INTERNAL);
				relation[i] = NestedWord.INTERNAL_POSITION;
				break;
			case CALL:
				if (n == PENDING_CALL) {
					require(openCalls.isEmpty(), i, "pending call inside a matched call");
					pendingCallSeen = true;
					relation[i] = NestedWord.PLUS_INFINITY;
				} else {
					require(n > i && n < length, i, "call needs a later return position, not " + n);
					require(nesting.get(n) == i, i, "return at " + n + " does not point back");
					openCalls.push(i);
					relation[i] = n;
				}
				break;
			case RETURN:
				if (n == PENDING_RETURN) {
					require(openCalls.isEmpty() && !pendingCallSeen, i, "pending return inside a call");
					relation[i] = NestedWord.MINUS_INFINITY;
				} else {
					require(n >= 0 && n < i, i, "return needs an earlier call position, not " + n);
					require(!openCalls.isEmpty() && openCalls.pop() == n, i,
							"return does not match the innermost open call");
					relation[i] = n;
				}
				break;
			default:
				throw new AssertionError(kind);
			}
		}
		require(openCalls.isEmpty(), length, "calls without their return: " + openCalls);
		return new NestedWord<>(letters, relation);
	}

	private static void require(final boolean condition, final int position, final String message) {
		if (!condition) {
			throw new IllegalArgumentException("Malformed nested word at position " + position + ": " + message);
		}
	}
}
