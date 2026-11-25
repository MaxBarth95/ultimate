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
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.icfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.LetterNaming.LetterKind;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.LetterNaming.Style;

/**
 * Round trips and rejections of {@link LetterNaming}.
 */
public class LetterNamingTest {

	private TestProgram mProgram;
	private LetterNaming<IcfgEdge> mNaming;

	@Before
	public void setUp() {
		mProgram = new TestProgram();
		mNaming = new LetterNaming<>(mProgram.mAlphabet);
	}

	private static int id(final IcfgEdge edge) {
		// IcfgEdgeFactory edges hash to their id; a CodeBlock would use its serial number
		return edge instanceof CodeBlock ? ((CodeBlock) edge).getSerialNumber() : edge.hashCode();
	}

	@Test
	public void messageNamesAreEdgeIds() {
		assertEquals(Style.ID, mNaming.getStyle());
		for (final IcfgEdge letter : mProgram.mAlphabet.getInternalAlphabet()) {
			assertEquals("e" + id(letter), mNaming.name(letter));
		}
		assertEquals("e" + id(mProgram.mCall), mNaming.name(mProgram.mCall));
		assertEquals("e" + id(mProgram.mReturn), mNaming.name(mProgram.mReturn));
	}

	@Test
	public void idNamesRoundTrip() {
		for (final IcfgEdge letter : new IcfgEdge[] { mProgram.mInc, mProgram.mCall, mProgram.mSkip,
				mProgram.mReturn, mProgram.mAssume }) {
			assertSame(letter, mNaming.resolve(mNaming.name(letter)));
		}
	}

	@Test
	public void fullNamesRoundTrip() {
		final LetterNaming<IcfgEdge> full = new LetterNaming<>(mProgram.mAlphabet, Style.FULL);
		for (final IcfgEdge letter : new IcfgEdge[] { mProgram.mInc, mProgram.mCall, mProgram.mSkip,
				mProgram.mReturn, mProgram.mAssume }) {
			final String name = full.name(letter);
			assertEquals(mNaming.fullName(letter), name);
			assertTrue(name, name.startsWith(mNaming.idName(letter) + ":"));
			assertTrue(name, !name.contains("\n"));
			// an ID naming reads full names (ATS_V1) and the other way round
			assertSame(letter, mNaming.resolve(name));
			assertSame(letter, full.resolve(mNaming.idName(letter)));
		}
	}

	@Test
	public void kinds() {
		assertEquals(LetterKind.INTERNAL, mNaming.kind(mProgram.mInc));
		assertEquals(LetterKind.CALL, mNaming.kind(mProgram.mCall));
		assertEquals(LetterKind.RETURN, mNaming.kind(mProgram.mReturn));
	}

	@Test
	public void fullNameWithOtherTextIsRejected() {
		final String name = mNaming.idName(mProgram.mInc) + ":x := 42;";
		assertThrows(IllegalArgumentException.class, () -> mNaming.resolve(name));
	}

	@Test
	public void malformedOrUnknownNamesAreRejected() {
		final int unknown = 1_000_000;
		for (final String name : new String[] { "", "e", "x1", "e1a", "e-1", "e01", "e" + unknown,
				"e" + unknown + ":skip", "e:skip" }) {
			assertThrows(name, IllegalArgumentException.class, () -> mNaming.resolve(name));
		}
	}

	@Test
	public void lettersOutsideTheAlphabetAreRejected() {
		final LetterNaming<IcfgEdge> internalOnly = new LetterNaming<>(
				new de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet<>(
						mProgram.mAlphabet.getInternalAlphabet()));
		assertThrows(IllegalArgumentException.class, () -> internalOnly.name(mProgram.mCall));
		assertThrows(IllegalArgumentException.class, () -> internalOnly.resolve(mNaming.name(mProgram.mCall)));
	}
}
