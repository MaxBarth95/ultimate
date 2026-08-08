/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainExceptionWrapper;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.icfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.icfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

public final class Dumper implements AutoCloseable {
	private final PrintWriter mIterationPW;
	private final ILogger mLogger;

	Dumper(final ILogger logger, final TAPreferences prefs, final DebugIdentifier name, final int iteration) {
		final File file = new File(prefs.dumpPath() + "/" + name + "_iteration" + iteration + ".txt");
		try {
			mIterationPW = new PrintWriter(new FileWriter(file));
		} catch (final IOException e) {
			throw new ToolchainExceptionWrapper(Activator.PLUGIN_ID, e);
		}
		mLogger = logger;
	}

	@Override
	public void close() {
		if (mIterationPW != null) {
			mIterationPW.close();
		}
	}

	@SuppressWarnings("unused")
	private void dumpSsa(final Term[] ssa) {
		final FormulaUnLet unflet = new FormulaUnLet();
		try {
			mIterationPW.println("===============SSA of potential Counterexample==========");
			for (int i = 0; i < ssa.length; i++) {
				mIterationPW.println("UnFletedTerm" + i + ": " + unflet.unlet(ssa[i]));
			}
			mIterationPW.println("");
			mIterationPW.println("");
		} finally {
			mIterationPW.flush();
		}
	}

	@SuppressWarnings("unused")
	private void dumpStateFormulas(final IPredicate[] interpolants) {
		try {
			mIterationPW.println("===============Interpolated StateFormulas==========");
			for (int i = 0; i < interpolants.length; i++) {
				mIterationPW.println("Interpolant" + i + ": " + interpolants[i]);
			}
			mIterationPW.println("");
			mIterationPW.println("");
		} finally {
			mIterationPW.flush();
		}
	}

	public void dumpNestedRunJson(final IRun<?, ?> run, final int pathProgramCount) {
		if (run == null || !(run instanceof NestedRun)) {
			throw new AssertionError("Failed to dump NestedRun");
		}

		final NestedWord<CodeBlock> counterexample = NestedWord.nestedWord(((IRun<CodeBlock, ?>) run).getWord());

		final StringBuilder json = new StringBuilder();

		json.append("{\n");
		json.append("  \"pathProgramCount\": ").append(pathProgramCount).append(",\n");
		json.append("  \"symbols\": [\n");

		for (int i = 0; i < counterexample.length(); i++) {
			final CodeBlock symbol = counterexample.getSymbol(i);

			json.append("    \"").append(escapeJsonString(String.valueOf(symbol))).append("\"");

			if (i < counterexample.length() - 1) {
				json.append(",");
			}

			json.append("\n");
		}

		json.append("  ]\n");
		json.append("}\n");

		try {
			Files.writeString(Path.of("./input/counterexamples/nested-run.json"), json.toString(),
					StandardCharsets.UTF_8);
		} catch (final IOException e) {
			throw new RuntimeException("Failed to write nested-run.json", e);
		}

	}

	private String escapeJsonString(final String value) {
		if (value == null) {
			return "";
		}

		final StringBuilder escaped = new StringBuilder();

		for (final char c : value.toCharArray()) {
			switch (c) {
			case '"' -> escaped.append("\\\"");
			case '\\' -> escaped.append("\\\\");
			case '\n' -> escaped.append("\\n");
			case '\r' -> escaped.append("\\r");
			case '\t' -> escaped.append("\\t");
			case '\b' -> escaped.append("\\b");
			case '\f' -> escaped.append("\\f");
			default -> escaped.append(c);
			}
		}

		return escaped.toString();
	}

	public void dumpNestedRun(final IRun<?, ?> run) {
		if (run == null || !(run instanceof NestedRun)) {
			return;
		}

		final List<IPredicate> stateSequence = ((NestedRun<CodeBlock, IPredicate>) run).getStateSequence();
		final NestedWord<CodeBlock> counterexample = NestedWord.nestedWord(((IRun<CodeBlock, ?>) run).getWord());
		String line;
		int indentation = 0;
		try {
			line = "===============Run of potential Counterexample==========";
			mIterationPW.println(line);
			for (int i = 0; i < counterexample.length(); i++) {

				if (run instanceof NestedRun) {
					line = CoreUtil.addIndentation(indentation,
							"Location" + i + ": " + ((ISLPredicate) stateSequence.get(i)).getProgramPoint());
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(line);
					}
					mIterationPW.println(line);
				}

				if (counterexample.isCallPosition(i)) {
					indentation++;
				}
				line = CoreUtil.addIndentation(indentation,
						"Statement" + i + ": " + counterexample.getSymbol(i).getPrettyPrintedStatements());
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(line);
				}
				mIterationPW.println(line);
				if (counterexample.isReturnPosition(i)) {
					indentation--;
				}
			}
			mIterationPW.println("ErrorLocation");
			mIterationPW.println("");
			mIterationPW.println("");
		} finally {
			mIterationPW.flush();
		}
	}

	void dumpBackedges(final BoogieIcfgLocation repLocName, final int position, final IPredicate state,
			final Collection<IPredicate> linPredStates, final CodeBlock transition, final IPredicate succState,
			final IPredicate sf1, final IPredicate sf2, final LBool result, final int iteration, final int satProblem) {
		try {
			mIterationPW.println(repLocName + " occured once again at position " + position + ". Added backedge");
			mIterationPW.println("from:   " + state);
			mIterationPW.println("labeled with:   " + transition.getPrettyPrintedStatements());
			mIterationPW.println("to:   " + succState);
			if (linPredStates != null) {
				mIterationPW.println("for each linPredStates:   " + linPredStates);
			}
			if (satProblem == -1) {
				mIterationPW.println("because ");
			} else {
				assert result == Script.LBool.UNSAT;
				mIterationPW.println("because Iteration" + iteration + "_SatProblem" + satProblem + " says:");
			}
			mIterationPW.println("  " + sf1);
			mIterationPW.println("implies");
			mIterationPW.println("  " + sf2);
			mIterationPW.println("");
		} finally {
			mIterationPW.flush();
		}
	}

}
