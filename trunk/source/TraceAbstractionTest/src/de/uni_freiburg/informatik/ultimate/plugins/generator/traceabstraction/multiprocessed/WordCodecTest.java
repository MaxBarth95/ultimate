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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertThrows;

import java.util.List;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.WordCodec.EncodedWord;

/**
 * Round trips and rejections of {@link WordCodec}.
 */
public class WordCodecTest {

	private TestProgram mProgram;
	private LetterNaming<IcfgEdge> mNaming;

	@Before
	public void setUp() {
		mProgram = new TestProgram();
		mNaming = new LetterNaming<>(mProgram.mAlphabet);
	}

	private NestedWord<IcfgEdge> word(final IcfgEdge[] letters, final int[] nesting) {
		return new NestedWord<>(letters, nesting);
	}

	private void assertRoundTrip(final NestedWord<IcfgEdge> word) {
		final EncodedWord encoded = WordCodec.encode(word, mNaming);
		for (final String name : encoded.word()) {
			assertFalse("message words use edge ids: " + name, name.contains(":"));
		}
		final NestedWord<IcfgEdge> decoded = WordCodec.decode(encoded, mNaming);
		assertEquals(word, decoded);
		assertEquals(encoded, WordCodec.encode(decoded, mNaming));
	}

	@Test
	public void matchedCallAndReturn() {
		final NestedWord<IcfgEdge> word = word(
				new IcfgEdge[] { mProgram.mInc, mProgram.mCall, mProgram.mSkip, mProgram.mReturn, mProgram.mAssume },
				new int[] { NestedWord.INTERNAL_POSITION, 3, NestedWord.INTERNAL_POSITION, 1,
						NestedWord.INTERNAL_POSITION });
		assertRoundTrip(word);
		assertEquals(List.of(WordCodec.INTERNAL, 3, WordCodec.INTERNAL, 1, WordCodec.INTERNAL),
				WordCodec.encode(word, mNaming).nesting());
	}

	@Test
	public void pendingCall() {
		final NestedWord<IcfgEdge> word = word(new IcfgEdge[] { mProgram.mInc, mProgram.mCall, mProgram.mSkip },
				new int[] { NestedWord.INTERNAL_POSITION, NestedWord.PLUS_INFINITY, NestedWord.INTERNAL_POSITION });
		assertRoundTrip(word);
		assertEquals(WordCodec.PENDING_CALL, (int) WordCodec.encode(word, mNaming).nesting().get(1));
	}

	@Test
	public void pendingReturn() {
		final NestedWord<IcfgEdge> word = word(new IcfgEdge[] { mProgram.mSkip, mProgram.mReturn, mProgram.mAssume },
				new int[] { NestedWord.INTERNAL_POSITION, NestedWord.MINUS_INFINITY, NestedWord.INTERNAL_POSITION });
		assertRoundTrip(word);
		assertEquals(WordCodec.PENDING_RETURN, (int) WordCodec.encode(word, mNaming).nesting().get(1));
	}

	@Test
	public void fullNamesAreRead() {
		final String inc = mNaming.fullName(mProgram.mInc);
		final NestedWord<IcfgEdge> decoded =
				WordCodec.decode(new EncodedWord(List.of(inc), List.of(WordCodec.INTERNAL)), mNaming);
		assertEquals(mProgram.mInc, decoded.getSymbol(0));
	}

	@Test
	public void malformedWordsAreRejected() {
		final String inc = mNaming.name(mProgram.mInc);
		final String call = mNaming.name(mProgram.mCall);
		final String ret = mNaming.name(mProgram.mReturn);
		final String skip = mNaming.name(mProgram.mSkip);
		final List<EncodedWord> malformed = List.of(
				// lengths differ
				new EncodedWord(List.of(inc), List.of()),
				// an internal letter with a nesting position
				new EncodedWord(List.of(inc, inc), List.of(1, 0)),
				// a call whose return does not point back
				new EncodedWord(List.of(call, skip, ret), List.of(2, WordCodec.INTERNAL, 1)),
				// a call letter used as a return
				new EncodedWord(List.of(call, call), List.of(1, 0)),
				// a pending return after a pending call
				new EncodedWord(List.of(call, ret), List.of(WordCodec.PENDING_CALL, WordCodec.PENDING_RETURN)),
				// a call without its return
				new EncodedWord(List.of(call, skip), List.of(1, WordCodec.INTERNAL)),
				// an unknown letter
				new EncodedWord(List.of("e1000000"), List.of(WordCodec.INTERNAL)));
		for (final EncodedWord word : malformed) {
			assertThrows(word.toString(), IllegalArgumentException.class, () -> WordCodec.decode(word, mNaming));
		}
	}
}
