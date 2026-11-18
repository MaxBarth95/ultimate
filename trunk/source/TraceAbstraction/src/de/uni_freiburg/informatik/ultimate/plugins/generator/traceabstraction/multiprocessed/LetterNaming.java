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
 * Names the letters of a program across processes: {@code e<serial>:<text>}, where {@code <serial>} is the serial
 * number of the edge and {@code <text>} its {@code toString} without line breaks. The serial makes the name unique
 * ({@code toString} alone is not: every goto prints {@code goto;}), the text lets the receiver check that its letter
 * with that serial is the same edge.
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

	private final Map<Integer, L> mSerialToLetter = new HashMap<>();
	private final Map<L, String> mLetterToName = new HashMap<>();
	private final Map<L, LetterKind> mLetterToKind = new HashMap<>();
	private final VpAlphabet<L> mAlphabet;

	/**
	 * @param alphabet
	 *            the alphabet of the initial abstraction
	 * @throws IllegalArgumentException
	 *             if a letter has no serial number, or two letters have the same one
	 */
	public LetterNaming(final VpAlphabet<L> alphabet) {
		mAlphabet = Objects.requireNonNull(alphabet);
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
			mLetterToName.put(letter, "e" + serial + ":" + text(letter));
		}
	}

	/**
	 * @return the alphabet these names cover
	 */
	public VpAlphabet<L> getAlphabet() {
		return mAlphabet;
	}

	/**
	 * @return the name of a letter
	 * @throws IllegalArgumentException
	 *             if the letter is not in the alphabet
	 */
	public String name(final L letter) {
		final String name = mLetterToName.get(letter);
		if (name == null) {
			throw new IllegalArgumentException("Letter not in the alphabet: " + letter);
		}
		return name;
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
	 * @return the letter with this name
	 * @throws IllegalArgumentException
	 *             if the name is malformed, its serial is unknown, or its text does not match the letter with that
	 *             serial
	 */
	public L resolve(final String name) {
		if (!name.startsWith("e")) {
			throw new IllegalArgumentException("Malformed letter name (no 'e'): " + name);
		}
		final int colon = name.indexOf(':');
		if (colon < 0) {
			throw new IllegalArgumentException("Malformed letter name (no ':'): " + name);
		}
		final int serial;
		try {
			serial = Integer.parseInt(name.substring(1, colon));
		} catch (final NumberFormatException e) {
			throw new IllegalArgumentException("Malformed letter name (bad serial): " + name, e);
		}
		final L letter = mSerialToLetter.get(serial);
		if (letter == null) {
			throw new IllegalArgumentException("Unknown letter serial " + serial + " in " + name);
		}
		final String expected = mLetterToName.get(letter);
		if (!expected.equals(name)) {
			throw new IllegalArgumentException(
					"Letter " + name + " does not match the local letter with serial " + serial + ": " + expected);
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
