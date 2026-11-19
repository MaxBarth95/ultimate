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

import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.OptionalLong;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.MultiProcessComponent;

/**
 * What every session kind does at start and on a crash: open the session directory, announce readiness with the
 * fingerprint of the program, and report an exception before the process ends.
 */
public final class MultiProcessSession {

	/**
	 * The plug-ins whose settings shape the program and its analysis. Their settings must agree between the sessions
	 * of a run, see {@link #settingsHash(IUltimateServiceProvider)}.
	 */
	private static final List<String> HASHED_PLUGINS = List.of("de.uni_freiburg.informatik.ultimate.core",
			"de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
			"de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
			"de.uni_freiburg.informatik.ultimate.boogie.preprocessor",
			"de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder",
			"de.uni_freiburg.informatik.ultimate.plugins.blockencoding", Activator.PLUGIN_ID);

	/**
	 * Settings that differ between the sessions of one run by design. The logger patterns carry the session id.
	 */
	private static final Set<String> SESSION_SETTINGS = Set.of(CorePreferenceInitializer.LABEL_LOG4J_PATTERN,
			CorePreferenceInitializer.LABEL_LOG4J_CONTROLLER_PATTERN,
			TraceAbstractionPreferenceInitializer.LABEL_MULTI_PROCESS_COMPONENT,
			TraceAbstractionPreferenceInitializer.LABEL_MULTI_PROCESS_EXCHANGE_ROOT,
			TraceAbstractionPreferenceInitializer.LABEL_MULTI_PROCESS_SESSION_ID,
			TraceAbstractionPreferenceInitializer.LABEL_NUM_TA_WORKERS);

	private static final String INITIAL_ABSTRACTION_NAME = "initialAbstraction";

	private MultiProcessSession() {
		// static helpers only
	}

	/**
	 * Opens the session directory of the configured kind.
	 */
	public static FileExchange openExchange(final TAPreferences prefs) {
		final MultiProcessComponent kind = prefs.getMultiProcessComponent();
		return new FileExchange(Path.of(prefs.getMultiProcessExchangeRoot()), ReadyFile.accepts(kind),
				ReadyFile.emits(kind));
	}

	/**
	 * Writes {@code ready.json}: the kind, the fingerprint of the program, the Ultimate version and the settings hash.
	 *
	 * @return the fingerprint, the SHA-256 of the initial abstraction printed by {@link AtsCodec}
	 */
	public static <L extends IIcfgTransition<?>> String announceReady(final IExchange exchange,
			final MultiProcessComponent kind, final IUltimateServiceProvider services, final ILogger logger,
			final IIcfg<? extends IcfgLocation> icfg, final INestedWordAutomaton<L, IPredicate> initialAbstraction) {
		final String fingerprint = fingerprint(services, logger, icfg, initialAbstraction);
		final ReadyFile ready =
				ReadyFile.of(kind, fingerprint, new UltimateCore().getUltimateVersionString(), settingsHash(services));
		exchange.announceReady(ready);
		logger.info("Session " + kind + " is ready, program fingerprint " + fingerprint + ", settings hash "
				+ ready.settingsHash());
		return fingerprint;
	}

	/**
	 * @return the SHA-256 of the initial abstraction printed by {@link AtsCodec}
	 */
	public static <L extends IIcfgTransition<?>> String fingerprint(final IUltimateServiceProvider services,
			final ILogger logger, final IIcfg<? extends IcfgLocation> icfg,
			final INestedWordAutomaton<L, IPredicate> initialAbstraction) {
		final LetterNaming<L> letters = new LetterNaming<>(initialAbstraction.getVpAlphabet());
		final String ats = new AtsCodec<>(services, logger, letters).printAbstraction(INITIAL_ABSTRACTION_NAME,
				initialAbstraction, new LocationNaming(icfg));
		if (logger.isDebugEnabled()) {
			logger.debug("Initial abstraction, as printed for the fingerprint:%n%s", ats);
		}
		return FileExchange.sha256(ats.getBytes(StandardCharsets.UTF_8));
	}

	/**
	 * @return the SHA-256 of the settings of {@link #HASHED_PLUGINS}, without the settings that differ per session
	 */
	public static String settingsHash(final IUltimateServiceProvider services) {
		final StringBuilder text = new StringBuilder();
		for (final String plugin : HASHED_PLUGINS) {
			final Map<String, Object> settings = new TreeMap<>(services.getPreferenceProvider(plugin).getPreferences());
			for (final Map.Entry<String, Object> setting : settings.entrySet()) {
				if (SESSION_SETTINGS.contains(setting.getKey())) {
					continue;
				}
				text.append(plugin).append('\0').append(setting.getKey()).append('\0').append(setting.getValue())
						.append('\n');
			}
		}
		return FileExchange.sha256(text.toString().getBytes(StandardCharsets.UTF_8));
	}

	/**
	 * Sends an {@code EXCEPTION} message for a failure of the session, if it still can. A failure while reporting is
	 * added to {@code failure} as suppressed; the caller rethrows {@code failure}.
	 */
	public static void reportException(final IExchange exchange, final MultiProcessComponent kind,
			final Throwable failure) {
		try {
			final StringWriter stackTrace = new StringWriter();
			failure.printStackTrace(new PrintWriter(stackTrace));
			exchange.send(MessageType.EXCEPTION, OptionalLong.empty(), OptionalLong.empty(),
					JsonCodec.encode(new JsonCodec.ExceptionReport(kind.name(), failure.getClass().getName(),
							failure.getMessage(), stackTrace.toString())));
		} catch (final RuntimeException e) {
			failure.addSuppressed(e);
		}
	}
}
