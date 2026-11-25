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

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.lib.icfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.AbstractIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;

/**
 * Names the letters of a program across processes.
 *
 * <ul>
 * <li>In messages (format ATS_V2 and the words of JSON_V1) a letter is {@code e<id>}, where {@code <id>} is the serial
 * number of the edge (the edge id of the program package, once sessions start from it). The fingerprint check of the
 * scheduler guarantees that all sessions of a run have the same edges with the same ids.</li>
 * <li>The full name {@code e<id>:<text>} adds the edge's {@code toString} without line breaks. It is what ATS_V1 used,
 * and what the fingerprint prints, so that the fingerprint also covers the text of every edge.</li>
 * </ul>
 * {@link #resolve(String)} accepts both forms; for a full name it checks that the text matches the local edge.
 *
 * The names are raw strings. Printing them into an automata script needs escaping, see {@link AtsCodec}; JSON escapes
 * them itself.
 *
 * @param <L>
 *            the letter type
 */
public final class LetterNaming<L extends IIcfgTransition<?>> {

	/**
	 * The kind of a letter in a nested word automaton.
	 */
	public enum LetterKind {
		INTERNAL, CALL, RETURN
	}

	/**
	 * Which form {@link LetterNaming#name(IIcfgTransition)} returns.
	 */
	public enum Style {
		/**
		 * {@code e<id>}, the form of the messages.
		 */
		ID,
		/**
		 * {@code e<id>:<text>}, the form of the fingerprint.
		 */
		FULL
	}

	private final Map<Integer, L> mSerialToLetter = new HashMap<>();
	private final Map<L, Integer> mLetterToSerial = new HashMap<>();
	private final Map<L, String> mLetterToFullName = new HashMap<>();
	private final Map<L, LetterKind> mLetterToKind = new HashMap<>();
	private final VpAlphabet<L> mAlphabet;
	private final Style mStyle;

	/**
	 * Names in the form of the messages, {@code e<id>}.
	 *
	 * @param alphabet
	 *            the alphabet of the initial abstraction
	 * @throws IllegalArgumentException
	 *             if a letter has no serial number, or two letters have the same one
	 */
	public LetterNaming(final VpAlphabet<L> alphabet) {
		this(alphabet, Style.ID);
	}

	/**
	 * @param alphabet
	 *            the alphabet of the initial abstraction
	 * @param style
	 *            the form of {@link #name(IIcfgTransition)}
	 * @throws IllegalArgumentException
	 *             if a letter has no serial number, or two letters have the same one
	 */
	public LetterNaming(final VpAlphabet<L> alphabet, final Style style) {
		mAlphabet = Objects.requireNonNull(alphabet);
		mStyle = Objects.requireNonNull(style);
		addAll(alphabet.getInternalAlphabet(), LetterKind.INTERNAL);
		addAll(alphabet.getCallAlphabet(), LetterKind.CALL);
		addAll(alphabet.getReturnAlphabet(), LetterKind.RETURN);
	}

	private void addAll(final Collection<L> letters, final LetterKind kind) {
		for (final L letter : letters) {
			final int serial = serialOf(letter);
			final L previous = mSerialToLetter.put(serial, letter);
			if (previous != null && previous != letter) {
				throw new IllegalArgumentException(
						"Two letters with serial " + serial + ": " + previous + " and " + letter);
			}
			if (mLetterToKind.put(letter, kind) != null) {
				throw new IllegalArgumentException("Letter " + letter + " is in more than one alphabet");
			}
			mLetterToSerial.put(letter, serial);
			mLetterToFullName.put(letter, "e" + serial + ":" + text(letter));
		}
	}

	/**
	 * @return the alphabet these names cover
	 */
	public VpAlphabet<L> getAlphabet() {
		return mAlphabet;
	}

	/**
	 * @return the name of a letter in this naming's {@link Style}
	 * @throws IllegalArgumentException
	 *             if the letter is not in the alphabet
	 */
	public String name(final L letter) {
		return mStyle == Style.ID ? idName(letter) : fullName(letter);
	}

	/**
	 * @return {@code e<id>}
	 * @throws IllegalArgumentException
	 *             if the letter is not in the alphabet
	 */
	public String idName(final L letter) {
		final Integer serial = mLetterToSerial.get(letter);
		if (serial == null) {
			throw new IllegalArgumentException("Letter not in the alphabet: " + letter);
		}
		return "e" + serial;
	}

	/**
	 * @return {@code e<id>:<text>}
	 * @throws IllegalArgumentException
	 *             if the letter is not in the alphabet
	 */
	public String fullName(final L letter) {
		final String name = mLetterToFullName.get(letter);
		if (name == null) {
			throw new IllegalArgumentException("Letter not in the alphabet: " + letter);
		}
		return name;
	}

	/**
	 * @return the form of {@link #name(IIcfgTransition)}
	 */
	public Style getStyle() {
		return mStyle;
	}

	/**
	 * @return whether the letter is an internal, call or return letter
	 */
	public LetterKind kind(final L letter) {
		final LetterKind kind = mLetterToKind.get(letter);
		if (kind == null) {
			throw new IllegalArgumentException("Letter not in the alphabet: " + letter);
		}
		return kind;
	}

	/**
	 * @return the letter with this name, {@code e<id>} or {@code e<id>:<text>}
	 * @throws IllegalArgumentException
	 *             if the name is malformed, its id is unknown, or (for a full name) its text does not match the letter
	 *             with that id
	 */
	public L resolve(final String name) {
		if (!name.startsWith("e")) {
			throw new IllegalArgumentException("Malformed letter name (no 'e'): " + name);
		}
		final int colon = name.indexOf(':');
		final String digits = colon < 0 ? name.substring(1) : name.substring(1, colon);
		if (digits.isEmpty() || !digits.chars().allMatch(c -> c >= '0' && c <= '9')) {
			throw new IllegalArgumentException("Malformed letter name (bad id): " + name);
		}
		final int serial;
		try {
			serial = Integer.parseInt(digits);
		} catch (final NumberFormatException e) {
			throw new IllegalArgumentException("Malformed letter name (bad id): " + name, e);
		}
		if (!digits.equals(String.valueOf(serial))) {
			throw new IllegalArgumentException("Malformed letter name (leading zeros): " + name);
		}
		final L letter = mSerialToLetter.get(serial);
		if (letter == null) {
			throw new IllegalArgumentException("Unknown letter id " + serial + " in " + name);
		}
		if (colon >= 0) {
			final String expected = mLetterToFullName.get(letter);
			if (!expected.equals(name)) {
				throw new IllegalArgumentException(
						"Letter " + name + " does not match the local letter with id " + serial + ": " + expected);
			}
		}
		return letter;
	}

	private static int serialOf(final IIcfgTransition<?> letter) {
		final int serial;
		if (letter instanceof CodeBlock) {
			serial = ((CodeBlock) letter).getSerialNumber();
		} else if (letter instanceof AbstractIcfgTransition) {
			// the hash code of these transitions is their id
			serial = letter.hashCode();
		} else {
			throw new IllegalArgumentException(
					"Letters of type " + letter.getClass().getSimpleName() + " have no serial number: " + letter);
		}
		if (serial < 0) {
			throw new IllegalArgumentException("Letter without a serial number: " + letter);
		}
		return serial;
	}

	private static String text(final IIcfgTransition<?> letter) {
		return letter.toString().replace("\r", "").replace("\n", "");
	}
}
