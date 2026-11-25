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
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.LetterNaming.Style;

/**
 * Round trips of {@link AtsCodec}: printing what was parsed gives the same text, for abstractions and interpolant
 * automata, with edge-id letters (ATS_V2) and with full names (ATS_V1).
 */
public class AtsCodecTest {

	private TestProgram mProgram;
	private LetterNaming<IcfgEdge> mNaming;
	private AtsCodec<IcfgEdge> mCodec;
	private LocationNaming mLocations;

	@Before
	public void setUp() {
		mProgram = new TestProgram();
		mNaming = new LetterNaming<>(mProgram.mAlphabet);
		mCodec = new AtsCodec<>(mProgram.mServices, mProgram.mLogger, mNaming);
		mLocations = new LocationNaming(mProgram.mIcfg);
	}

	private NestedWordAutomaton<IcfgEdge, IPredicate> parseAbstraction(final AtsCodec<IcfgEdge> codec,
			final String ats) {
		return codec.parseAbstraction(ats, mLocations, mProgram::state, mProgram.emptyStackFactory());
	}

	private NestedWordAutomaton<IcfgEdge, IPredicate> interpolantAutomaton() {
		final NestedWordAutomaton<IcfgEdge, IPredicate> nwa = new NestedWordAutomaton<>(
				mProgram.automataServices(), mProgram.mAlphabet, mProgram.emptyStackFactory());
		final IPredicate t = mProgram.formula("true");
		final IPredicate positive = mProgram.formula("(> x 0)");
		final IPredicate f = mProgram.formula("false");
		nwa.addState(true, false, t);
		nwa.addState(false, false, positive);
		nwa.addState(false, true, f);
		nwa.addInternalTransition(t, mProgram.mInc, positive);
		nwa.addCallTransition(positive, mProgram.mCall, positive);
		nwa.addInternalTransition(positive, mProgram.mSkip, positive);
		nwa.addReturnTransition(positive, positive, mProgram.mReturn, positive);
		nwa.addInternalTransition(positive, mProgram.mAssume, f);
		nwa.addInternalTransition(f, mProgram.mAssume, f);
		return nwa;
	}

	private NestedWordAutomaton<IcfgEdge, IPredicate> parseInterpolantAutomaton(final AtsCodec<IcfgEdge> codec,
			final String ats) {
		final Map<String, IPredicate> unified = new HashMap<>();
		return codec.parseInterpolantAutomaton(ats, s -> unified.computeIfAbsent(s, mProgram::formula),
				mProgram.emptyStackFactory());
	}

	private void assertIdLetters(final String ats) {
		for (final IcfgEdge letter : new IcfgEdge[] { mProgram.mInc, mProgram.mCall, mProgram.mSkip,
				mProgram.mReturn, mProgram.mAssume }) {
			assertTrue(ats, ats.contains("\"" + mNaming.idName(letter) + "\""));
			assertFalse(ats, ats.contains("\"" + mNaming.idName(letter) + ":"));
		}
	}

	@Test
	public void abstractionRoundTrip() {
		final String ats = mCodec.printAbstraction("a", mProgram.abstraction(), mLocations);
		assertIdLetters(ats);
		final NestedWordAutomaton<IcfgEdge, IPredicate> parsed = parseAbstraction(mCodec, ats);
		assertEquals(6, parsed.size());
		assertEquals(ats, mCodec.printAbstraction("a", parsed, mLocations));
	}

	@Test
	public void interpolantAutomatonRoundTrip() {
		final String ats = mCodec.printInterpolantAutomaton("i", interpolantAutomaton());
		assertIdLetters(ats);
		final NestedWordAutomaton<IcfgEdge, IPredicate> parsed = parseInterpolantAutomaton(mCodec, ats);
		assertEquals(3, parsed.size());
		assertEquals(ats, mCodec.printInterpolantAutomaton("i", parsed));
	}

	@Test
	public void printingIsCanonical() {
		// two separately built equal automata print to the same bytes (the fingerprint relies on it)
		assertEquals(mCodec.printAbstraction("a", mProgram.abstraction(), mLocations),
				mCodec.printAbstraction("a", mProgram.abstraction(), mLocations));
		assertEquals(mCodec.printInterpolantAutomaton("i", interpolantAutomaton()),
				mCodec.printInterpolantAutomaton("i", interpolantAutomaton()));
	}

	@Test
	public void fullNamesAreReadAsV1() {
		final AtsCodec<IcfgEdge> full = new AtsCodec<>(mProgram.mServices, mProgram.mLogger,
				new LetterNaming<>(mProgram.mAlphabet, Style.FULL));
		final String v1 = full.printAbstraction("a", mProgram.abstraction(), mLocations);
		assertTrue(v1, v1.contains("\"" + mNaming.fullName(mProgram.mInc).replace("\"", "\\\"") + "\""));
		final String v2 = mCodec.printAbstraction("a", mProgram.abstraction(), mLocations);
		assertEquals(v2, mCodec.printAbstraction("a", parseAbstraction(mCodec, v1), mLocations));
		final String i1 = full.printInterpolantAutomaton("i", interpolantAutomaton());
		assertEquals(mCodec.printInterpolantAutomaton("i", interpolantAutomaton()),
				mCodec.printInterpolantAutomaton("i", parseInterpolantAutomaton(mCodec, i1)));
	}

	@Test
	public void unknownLetterIsRejected() {
		final String ats = mCodec.printAbstraction("a", mProgram.abstraction(), mLocations);
		final String inc = "\"" + mNaming.idName(mProgram.mInc) + "\"";
		final String broken = ats.replace(inc, "\"e1000000\"");
		assertFalse(ats.equals(broken));
		assertThrows(IllegalArgumentException.class, () -> parseAbstraction(mCodec, broken));
	}

	@Test
	public void unknownLocationIsRejected() {
		final String ats = mCodec.printAbstraction("a", mProgram.abstraction(), mLocations);
		final String broken = ats.replace("@main::l1\"", "@main::nowhere\"");
		assertFalse(ats.equals(broken));
		assertThrows(IllegalArgumentException.class, () -> parseAbstraction(mCodec, broken));
	}
}
