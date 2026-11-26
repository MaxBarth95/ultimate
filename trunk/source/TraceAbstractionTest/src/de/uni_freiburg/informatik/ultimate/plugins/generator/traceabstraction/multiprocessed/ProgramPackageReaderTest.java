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
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import java.util.Set;
import java.util.TreeSet;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Round trips of {@link ProgramPackageReader}: writing the read ICFG gives the same bytes, and inconsistent packages
 * throw.
 */
public class ProgramPackageReaderTest {

	private TestProgram mProgram;
	private String mJson;

	@Before
	public void setUp() {
		mProgram = new TestProgram();
		mJson = ProgramPackageWriter.writeJson(mProgram.mIcfg);
	}

	private ManagedScript freshScript(final Logics logic) {
		final Script script = new HistoryRecordingScript(UltimateMocks.createZ3Script(LogLevel.INFO));
		script.setLogic(logic);
		return new ManagedScript(mProgram.mServices, script);
	}

	@Test
	public void writeReadWriteIsByteIdentical() {
		final BasicIcfg<IcfgLocation> read = ProgramPackageReader.readJson(freshScript(Logics.ALL), mJson);
		assertEquals(mJson, ProgramPackageWriter.writeJson(read));
	}

	@Test
	public void readIcfgKeepsIdsAndStructure() {
		final BasicIcfg<IcfgLocation> read = ProgramPackageReader.readJson(freshScript(Logics.ALL), mJson);
		assertEquals("test", read.getIdentifier());
		assertEquals(ids(mProgram.mIcfg), ids(read));
		assertEquals(1, read.getInitialNodes().size());
		assertEquals("l0", read.getInitialNodes().iterator().next().getDebugIdentifier().toString());
		assertEquals(Set.of("main", "f"), read.getProgramPoints().keySet());
		final Set<IProgramNonOldVar> globals = read.getCfgSmtToolkit().getSymbolTable().getGlobals();
		assertEquals(1, globals.size());
		final IProgramNonOldVar x = globals.iterator().next();
		assertEquals(mProgram.mX.getTermVariable().getName(), x.getTermVariable().getName());
		assertEquals(mProgram.mX.getOldVar().getTermVariable().getName(), x.getOldVar().getTermVariable().getName());
		assertTrue(read.getCfgSmtToolkit().getModifiableGlobalsTable().getModifiedBoogieVars("main").contains(x));
		// the overapproximating edge stays one
		final IcfgEdge assume = read.getProgramPoints().get("main").values().stream()
				.flatMap(l -> l.getOutgoingEdges().stream())
				.filter(e -> LetterNaming.idOf(e) == LetterNaming.idOf(mProgram.mAssume)).findFirst().orElseThrow();
		assertEquals(Set.of("float in integer mode"),
				Overapprox.getAnnotation(assume).getOverapproximatedLocations().keySet());
		// letters of the read ICFG have the ids of the original
		final LetterNaming<IcfgEdge> naming = new LetterNaming<>(mProgram.mAlphabet);
		for (final IcfgLocation loc : read.getProgramPoints().get("main").values()) {
			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
				assertEquals(naming.idName(originalEdge(LetterNaming.idOf(edge))), "e" + LetterNaming.idOf(edge));
			}
		}
	}

	private IcfgEdge originalEdge(final int id) {
		for (final IcfgEdge edge : new IcfgEdge[] { mProgram.mInc, mProgram.mCall, mProgram.mSkip, mProgram.mReturn,
				mProgram.mAssume, mProgram.mShortcut }) {
			if (LetterNaming.idOf(edge) == id) {
				return edge;
			}
		}
		throw new AssertionError("No original edge with id " + id);
	}

	private static Set<Integer> ids(final BasicIcfg<IcfgLocation> icfg) {
		final Set<Integer> result = new TreeSet<>();
		for (final var points : icfg.getProgramPoints().values()) {
			for (final IcfgLocation loc : points.values()) {
				loc.getOutgoingEdges().forEach(e -> result.add(LetterNaming.idOf(e)));
			}
		}
		return result;
	}

	@Test
	public void freshNamesContinueAsInTheWriter() {
		// the writer's script already constructed fresh variables (as the C pipeline does)
		final ManagedScript original = mProgram.mMgdScript;
		original.constructFreshTermVariable("x", mProgram.mX.getSort());
		original.constructFreshTermVariable("x", mProgram.mX.getSort());
		final String json = ProgramPackageWriter.writeJson(mProgram.mIcfg);
		final ManagedScript readScript = freshScript(Logics.ALL);
		final BasicIcfg<IcfgLocation> read = ProgramPackageReader.readJson(readScript, json);
		final IProgramNonOldVar readX = read.getCfgSmtToolkit().getSymbolTable().getGlobals().iterator().next();
		assertEquals(original.constructFreshTermVariable("x", mProgram.mX.getSort()).getName(),
				readScript.constructFreshTermVariable("x", readX.getSort()).getName());
		assertEquals(original.constructFreshCopy(mProgram.mX.getTermVariable()).getName(),
				readScript.constructFreshCopy(readX.getTermVariable()).getName());
		assertEquals(original.getFreshVariableCounters(), readScript.getFreshVariableCounters());
	}

	/**
	 * The read ICFG iterates its program points, the edges of each location and its special locations in the order of
	 * the original, and its locations have the original hash codes: then TraceAbstraction builds the same queries in
	 * the same order.
	 */
	@Test
	public void iterationOrderAndHashCodesAreKept() {
		final BasicIcfg<IcfgLocation> read = ProgramPackageReader.readJson(freshScript(Logics.ALL), mJson);
		assertEquals(order(mProgram.mIcfg), order(read));
		final IcfgLocation l1 = mProgram.mL1;
		assertTrue("the test needs an edge order other than the id order",
				LetterNaming.idOf(l1.getOutgoingEdges().get(0)) > LetterNaming.idOf(l1.getOutgoingEdges().get(1)));
		assertEquals(mProgram.mIcfg.getCfgSmtToolkit().getProcedures().stream().toList(),
				read.getCfgSmtToolkit().getProcedures().stream().toList());
		assertEquals(names(mProgram.mIcfg.getCfgSmtToolkit().getSymbolTable().getLocals("main")),
				names(read.getCfgSmtToolkit().getSymbolTable().getLocals("main")));
	}

	private static java.util.List<String> names(final Set<? extends IProgramVar> vars) {
		return vars.stream().map(v -> v.getTermVariable().getName()).toList();
	}

	/**
	 * Program points with their hash codes and the ids of their outgoing and incoming edges, and the special
	 * locations, all in iteration order.
	 */
	private static java.util.List<String> order(final BasicIcfg<IcfgLocation> icfg) {
		final java.util.List<String> result = new java.util.ArrayList<>();
		for (final var entry : icfg.getProgramPoints().entrySet()) {
			for (final IcfgLocation loc : entry.getValue().values()) {
				result.add(entry.getKey() + "::" + loc + "#" + loc.hashCode() + " out "
						+ loc.getOutgoingEdges().stream().map(LetterNaming::idOf).toList() + " in "
						+ loc.getIncomingEdges().stream().map(LetterNaming::idOf).toList());
			}
		}
		result.add("initial " + icfg.getInitialNodes());
		result.add("errors " + icfg.getProcedureErrorNodes());
		result.add("entries " + icfg.getProcedureEntryNodes());
		result.add("exits " + icfg.getProcedureExitNodes());
		return result;
	}

	@Test
	public void otherLogicIsRejected() {
		assertThrows(IllegalArgumentException.class,
				() -> ProgramPackageReader.readJson(freshScript(Logics.QF_LIA), mJson));
	}

	@Test
	public void inconsistentPackagesAreRejected() {
		final String x = mProgram.mX.getTermVariable().getName();
		final String[] broken = { mJson.replace("\"format\":\"PACKAGE_JSON_V1\"", "\"format\":\"JSON_V1\""),
				mJson.replace("\"source\":\"main::l1\"", "\"source\":\"main::nowhere\""),
				mJson.replaceFirst("\"inVars\":\\{\"" + x + "\"", "\"inVars\":{\"unknown\""),
				mJson.replace("\"kind\":\"RETURN\"", "\"kind\":\"INTERNAL\""),
				mJson.replace("\"edges\":", "\"edgez\":") };
		for (final String json : broken) {
			assertTrue(!json.equals(mJson));
			assertThrows(IllegalArgumentException.class,
					() -> ProgramPackageReader.readJson(freshScript(Logics.ALL), json));
		}
	}
}
