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
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.Edge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.EdgeKind;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage.Location;

/**
 * {@link ProgramPackageWriter}: the package of the test program, and equal bytes for equal programs.
 */
public class ProgramPackageWriterTest {

	@Test
	public void equalProgramsGiveEqualBytes() {
		final String first = ProgramPackageWriter.writeJson(new TestProgram().mIcfg);
		final String second = ProgramPackageWriter.writeJson(new TestProgram().mIcfg);
		assertEquals(first, second);
		assertTrue(first, first.startsWith("{\"format\":\"PACKAGE_JSON_V1\""));
	}

	@Test
	public void jsonRoundTrip() {
		final String json = ProgramPackageWriter.writeJson(new TestProgram().mIcfg);
		final ProgramPackage decoded = JsonCodec.decode(json, ProgramPackage.class, ProgramPackage.FORMAT);
		assertEquals(json, JsonCodec.encode(decoded, ProgramPackage.FORMAT));
	}

	@Test
	public void content() {
		final TestProgram program = new TestProgram();
		final ProgramPackage pkg = ProgramPackageWriter.write(program.mIcfg);

		assertEquals(1, pkg.globals().size());
		assertEquals("x", pkg.globals().get(0).variable().identifier());
		assertEquals("Int", pkg.globals().get(0).variable().sort());
		assertEquals("x", pkg.globals().get(0).oldVariable().identifier());
		assertFalse(pkg.globals().get(0).variable().termVariable()
				.equals(pkg.globals().get(0).oldVariable().termVariable()));
		// the constants of x and old(x) are declared, nothing else
		assertEquals(4, pkg.declarations().size());
		for (final String declaration : pkg.declarations()) {
			assertTrue(declaration, declaration.startsWith("(declare-fun "));
		}

		assertEquals(List.of("f", "main"), pkg.procedures().stream().map(ProgramPackage.Procedure::name).toList());
		assertEquals(List.of("x"), pkg.procedures().get(1).modifiableGlobals());

		assertEquals(6, pkg.locations().size());
		final Location l0 = pkg.locations().stream().filter(l -> l.debugId().equals("l0")).findFirst().orElseThrow();
		assertTrue(l0.initial() && l0.entry() && !l0.error());
		final Location err = pkg.locations().stream().filter(l -> l.debugId().equals("err")).findFirst().orElseThrow();
		assertTrue(err.error() && !err.initial());

		assertEquals(5, pkg.edges().size());
		for (int i = 1; i < pkg.edges().size(); i++) {
			assertTrue(pkg.edges().get(i - 1).id() < pkg.edges().get(i).id());
		}
		final Edge call = edge(pkg, LetterNaming.idOf(program.mCall));
		assertEquals(EdgeKind.CALL, call.kind());
		assertEquals("main::l1", call.source());
		assertEquals("f::entry", call.target());
		final Edge ret = edge(pkg, LetterNaming.idOf(program.mReturn));
		assertEquals(EdgeKind.RETURN, ret.kind());
		assertEquals(Integer.valueOf(call.id()), ret.call());
		final Edge assume = edge(pkg, LetterNaming.idOf(program.mAssume));
		assertEquals(EdgeKind.INTERNAL, assume.kind());
		assertNull(assume.call());
		assertTrue(assume.transFormula().formula(), assume.transFormula().formula().contains("1"));
		assertEquals(1, assume.transFormula().inVars().size());
		assertEquals(List.of("float in integer mode"), assume.overapproximations());
		assertNull(call.overapproximations());
	}

	private static Edge edge(final ProgramPackage pkg, final int id) {
		return pkg.edges().stream().filter(e -> e.id() == id).findFirst().orElseThrow();
	}
}
