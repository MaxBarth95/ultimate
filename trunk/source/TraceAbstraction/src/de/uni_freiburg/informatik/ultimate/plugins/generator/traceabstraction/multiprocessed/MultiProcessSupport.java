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

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IWitnessTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.CegarRestartBehaviour;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.MultiProcessComponent;

/**
 * Checks that a multi-process session runs in a configuration it supports. Every unsupported case throws, so that a
 * misconfigured session fails at startup instead of silently running something else. The session kind takes
 * precedence over the parallel and the sequential k-induction CEGAR loop, which the SV-COMP settings turn on.
 *
 * See {@code TraceAbstraction/.doc/multiprocessed/} for the protocol.
 */
public final class MultiProcessSupport {

	/**
	 * The log4j pattern of every log line of a session (R8): an ISO-8601 time, the level, the session id in brackets
	 * and the logger, so that the worker service can parse and forward the lines. {@code %s} is the session id.
	 */
	private static final String LOG_PATTERN = "%%d{yyyy-MM-dd'T'HH:mm:ss.SSSXXX} %%p [%s] %%c: %%m%%n";

	private MultiProcessSupport() {
		// static helpers only
	}

	/**
	 * @return true if this process runs as a session of a multi-process run, i.e. the kind is not
	 *         {@link MultiProcessComponent#DISABLED}
	 */
	public static boolean isMultiProcess(final TAPreferences prefs) {
		return prefs.getMultiProcessComponent() != MultiProcessComponent.DISABLED;
	}

	/**
	 * @return the log4j pattern a session with this id must use for both core logger patterns
	 */
	public static String logPattern(final String sessionId) {
		return String.format(LOG_PATTERN, sessionId);
	}

	/**
	 * Throws if the program or the settings are not supported by the multi-process session kinds.
	 *
	 * @param prefs
	 *            the trace abstraction settings
	 * @param services
	 *            the services, for the settings of the trace abstraction and the core plug-in
	 * @param icfg
	 *            the program
	 * @param witnessTransformer
	 *            the witness transformer of a witness validation run, or null
	 */
	public static void checkSupported(final TAPreferences prefs, final IUltimateServiceProvider services,
			final IIcfg<?> icfg, final IWitnessTransformer<?> witnessTransformer) {
		final IPreferenceProvider rawPrefs = services.getPreferenceProvider(
				de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator.PLUGIN_ID);
		final MultiProcessComponent kind = prefs.getMultiProcessComponent();
		if (kind == MultiProcessComponent.DISABLED) {
			throw new IllegalStateException("Not a multi-process session");
		}
		if (prefs.getMultiProcessExchangeRoot().isBlank()) {
			throw new IllegalArgumentException("Session kind " + kind + " needs the setting "
					+ label(TraceAbstractionPreferenceInitializer.LABEL_MULTI_PROCESS_EXCHANGE_ROOT));
		}
		if (prefs.getMultiProcessSessionId().isBlank()) {
			throw new IllegalArgumentException("Session kind " + kind + " needs the setting "
					+ label(TraceAbstractionPreferenceInitializer.LABEL_MULTI_PROCESS_SESSION_ID));
		}
		checkLogging(services.getPreferenceProvider(Activator.PLUGIN_ID), prefs.getMultiProcessSessionId());
		if (IcfgUtils.isConcurrent(icfg)) {
			throw new UnsupportedOperationException("Multi-process sessions support only sequential programs");
		}
		if (witnessTransformer != null) {
			throw new UnsupportedOperationException("Multi-process sessions do not support witness validation");
		}
		final CegarRestartBehaviour restart = rawPrefs.getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_CEGAR_RESTART_BEHAVIOUR, CegarRestartBehaviour.class);
		if (restart != CegarRestartBehaviour.ONLY_ONE_CEGAR) {
			throw new UnsupportedOperationException(
					"Multi-process sessions need one CEGAR loop for all error locations, not " + restart);
		}
		if (prefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
			throw new UnsupportedOperationException("Multi-process sessions do not support Floyd-Hoare automata reuse");
		}
		final LanguageOperation languageOperation = rawPrefs
				.getEnum(TraceAbstractionPreferenceInitializer.LABEL_LANGUAGE_OPERATION, LanguageOperation.class);
		if (languageOperation != LanguageOperation.DIFFERENCE) {
			throw new UnsupportedOperationException(
					"Multi-process sessions need the language operation DIFFERENCE, not " + languageOperation);
		}
		if (!prefs.interprocedural()) {
			// the program package leaves out the summary edges of implemented calls, which only a
			// non-interprocedural analysis uses
			throw new UnsupportedOperationException("Multi-process sessions need the setting "
					+ label(TraceAbstractionPreferenceInitializer.LABEL_INTERPROCEDURAL));
		}
		if (prefs.interpolantAutomaton() == InterpolantAutomaton.TOTALINTERPOLATION) {
			throw new UnsupportedOperationException("Multi-process sessions do not support total interpolation");
		}
	}

	/**
	 * A session logs to stdout and stderr only, and every line starts with the prefix of {@link #logPattern(String)}.
	 */
	private static void checkLogging(final IPreferenceProvider corePrefs, final String sessionId) {
		if (corePrefs.getBoolean(CorePreferenceInitializer.LABEL_LOGFILE)) {
			throw new IllegalArgumentException("A multi-process session logs to stdout and stderr only; turn off "
					+ label(CorePreferenceInitializer.LABEL_LOGFILE));
		}
		final String expected = logPattern(sessionId);
		for (final String patternLabel : new String[] { CorePreferenceInitializer.LABEL_LOG4J_PATTERN,
				CorePreferenceInitializer.LABEL_LOG4J_CONTROLLER_PATTERN }) {
			final String actual = corePrefs.getString(patternLabel);
			if (!expected.equals(actual)) {
				throw new IllegalArgumentException("A multi-process session needs the core setting "
						+ label(patternLabel) + " to be " + label(expected) + ", not " + label(actual));
			}
		}
	}

	private static String label(final String label) {
		return "\"" + label + "\"";
	}
}
