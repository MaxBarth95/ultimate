/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE ProgramPackageReader plug-in.
 *
 * The ULTIMATE ProgramPackageReader plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ProgramPackageReader plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ProgramPackageReader plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ProgramPackageReader plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ProgramPackageReader plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.source.programpackage;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.preferences.IcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackage;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackageReader;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.ProgramPackageWriter;

/**
 * Reads a program package (PACKAGE_JSON_V1, written by the FRONTEND session) into an ICFG, in place of the C pipeline
 * (toolchain {@code AutomizerPackage.xml}: this plug-in, then TraceAbstraction).
 *
 * The SMT script is built exactly like the IcfgBuilder's, from the IcfgBuilder's SMT settings of the session. Under
 * {@code -ea} the read ICFG is written again and must give the same bytes.
 */
public class ProgramPackageSource implements ISource {

	private static final String FILE_TYPE = ".json";
	private static final byte[] HEADER =
			("{\"format\":\"" + ProgramPackage.FORMAT + "\"").getBytes(StandardCharsets.UTF_8);

	private IUltimateServiceProvider mServices;
	private ILogger mLogger;
	private List<String> mFileNames = Collections.emptyList();

	@Override
	public void init() {
		// nothing to do
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public File[] parseable(final File[] files) {
		return Arrays.stream(files).filter(ProgramPackageSource::isPackage).toArray(File[]::new);
	}

	private static boolean isPackage(final File file) {
		if (!file.getName().endsWith(FILE_TYPE) || !file.isFile()) {
			return false;
		}
		try (InputStream in = Files.newInputStream(file.toPath())) {
			return Arrays.equals(in.readNBytes(HEADER.length), HEADER);
		} catch (final IOException e) {
			throw new UncheckedIOException("Cannot read " + file, e);
		}
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		if (files.length != 1) {
			throw new IllegalArgumentException("Expected exactly one program package, got " + files.length + " files");
		}
		final File file = files[0];
		mFileNames = List.of(file.getAbsolutePath());
		final long start = System.nanoTime();
		final String json = Files.readString(file.toPath(), StandardCharsets.UTF_8);
		final BasicIcfg<IcfgLocation> icfg =
				ProgramPackageReader.readJson(new ManagedScript(mServices, constructScript(file.getName())), json);
		// results stay on the level of the ICFG: there is no C or Boogie program to translate back to
		mServices.getBacktranslationService().addTranslator(
				new DefaultTranslator<>(IcfgEdge.class, IcfgEdge.class, Term.class, Term.class));
		// as the C pipeline's ICFG carries the location of its C file; not part of the package, so not of the
		// fingerprint
		// results need a location on every program point and edge; the package has no source positions
		final DefaultLocation location = new DefaultLocation(file.getAbsolutePath(), -1, -1, -1, -1);
		location.annotate(icfg);
		for (final Map<?, IcfgLocation> points : icfg.getProgramPoints().values()) {
			for (final IcfgLocation loc : points.values()) {
				location.annotate(loc);
				loc.getOutgoingEdges().forEach(location::annotate);
			}
		}
		mLogger.info(String.format("Read the program package %s (%d bytes) in %d ms", file.getName(),
				json.getBytes(StandardCharsets.UTF_8).length, (System.nanoTime() - start) / 1_000_000));
		assert ProgramPackageWriter.writeJson(icfg).equals(json) : "Writing the read package gives other bytes";
		return icfg;
	}

	/**
	 * The script of the IcfgBuilder ({@code CfgBuilder.constructAndInitializeSolver}), from the same settings.
	 */
	private Script constructScript(final String filename) {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(
				de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.Activator.PLUGIN_ID);
		final SolverMode solverMode = prefs.getEnum(IcfgPreferenceInitializer.LABEL_SOLVER, SolverMode.class);
		final boolean fakeNonIncrementalScript =
				prefs.getBoolean(IcfgPreferenceInitializer.LABEL_FAKE_NON_INCREMENTAL_SCRIPT);
		final boolean dumpSmtScriptToFile = prefs.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_TO_FILE);
		final boolean compressSmtScript = prefs.getBoolean(IcfgPreferenceInitializer.LABEL_COMPRESS_SMT_DUMP_FILE);
		final String pathOfDumpedScript = prefs.getString(IcfgPreferenceInitializer.LABEL_DUMP_PATH);
		final String commandExternalSolver = prefs.getString(IcfgPreferenceInitializer.LABEL_EXT_SOLVER_COMMAND);
		final boolean dumpUnsatCoreTrackBenchmark =
				prefs.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_UNSAT_CORE_BENCHMARK);
		final boolean dumpMainTrackBenchmark =
				prefs.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_MAIN_TRACK_BENCHMARK);
		final Map<String, String> additionalSmtOptions =
				prefs.getKeyValueMap(IcfgPreferenceInitializer.LABEL_ADDITIONAL_SMT_OPTIONS);
		final Logics logicForExternalSolver =
				Logics.valueOf(prefs.getString(IcfgPreferenceInitializer.LABEL_EXT_SOLVER_LOGIC));
		final SolverSettings solverSettings =
				SolverBuilder.constructSolverSettings().setUseFakeIncrementalScript(fakeNonIncrementalScript)
						.setDumpSmtScriptToFile(dumpSmtScriptToFile, pathOfDumpedScript, filename, compressSmtScript)
						.setDumpUnsatCoreTrackBenchmark(dumpUnsatCoreTrackBenchmark)
						.setDumpMainTrackBenchmark(dumpMainTrackBenchmark)
						.setUseExternalSolver(true, commandExternalSolver, logicForExternalSolver)
						.setSolverMode(solverMode).setAdditionalOptions(additionalSmtOptions);
		return SolverBuilder.buildAndInitializeSolver(mServices, solverSettings, "CfgBuilderScript");
	}

	@Override
	public String[] getFileTypes() {
		return new String[] { FILE_TYPE };
	}

	@Override
	public ModelType getOutputDefinition() {
		return new ModelType(Activator.PLUGIN_ID, ModelType.Type.CFG, mFileNames);
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public void finish() {
		// nothing to do
	}
}
