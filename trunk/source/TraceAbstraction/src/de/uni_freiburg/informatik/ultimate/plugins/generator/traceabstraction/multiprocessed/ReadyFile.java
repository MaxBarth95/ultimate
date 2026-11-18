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

import java.util.EnumSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.MultiProcessComponent;

/**
 * The content of {@code out/ready.json}: a session is set up and has computed the fingerprint of its program. The
 * worker service fills its {@code SetupResponse} from it.
 *
 * @param protocol
 *            always {@value #PROTOCOL}
 * @param kind
 *            the session kind
 * @param fingerprint
 *            the SHA-256 of the initial abstraction, see {@link AtsCodec}
 * @param ultimateVersion
 *            the version of this Ultimate
 * @param settingsHash
 *            the SHA-256 of the settings that must agree between the sessions of a run
 * @param accepts
 *            the message types the kind reads
 * @param emits
 *            the message types the kind writes
 */
public record ReadyFile(String protocol, String kind, String fingerprint, String ultimateVersion,
		String settingsHash, List<String> accepts, List<String> emits) {

	public static final String PROTOCOL = "EXCHANGE_V1";

	/**
	 * @return the ready file of a session kind, with accepts and emits from the routing table
	 */
	public static ReadyFile of(final MultiProcessComponent kind, final String fingerprint,
			final String ultimateVersion, final String settingsHash) {
		return new ReadyFile(PROTOCOL, kind.name(), fingerprint, ultimateVersion, settingsHash,
				accepts(kind).stream().map(Enum::name).toList(), emits(kind).stream().map(Enum::name).toList());
	}

	/**
	 * The message types a kind reads, as in the routing table of UltimateCloud's {@code plans/main-plan.md}, limited
	 * to what the kind uses in this phase.
	 */
	public static Set<MessageType> accepts(final MultiProcessComponent kind) {
		return switch (kind) {
		case COORDINATOR -> EnumSet.of(MessageType.RESULT, MessageType.INTERPOLANT_AUTOMATON);
		case TA_WORKER -> EnumSet.of(MessageType.ABSTRACTION, MessageType.COUNTEREXAMPLE, MessageType.CANCEL);
		case WITNESS -> EnumSet.of(MessageType.RESULT, MessageType.PROOF_ANNOTATION, MessageType.VERDICT);
		case DISABLED -> throw new IllegalArgumentException("DISABLED is not a session kind");
		};
	}

	/**
	 * The message types a kind writes. Every kind may write {@link MessageType#EXCEPTION}. The witness of the WITNESS
	 * kind is {@code out/witness.yml}, not a numbered message.
	 */
	public static Set<MessageType> emits(final MultiProcessComponent kind) {
		return switch (kind) {
		case COORDINATOR -> EnumSet.of(MessageType.ABSTRACTION, MessageType.COUNTEREXAMPLE, MessageType.CANCEL,
				MessageType.VERDICT, MessageType.PROOF_ANNOTATION, MessageType.EXCEPTION);
		case TA_WORKER -> EnumSet.of(MessageType.RESULT, MessageType.INTERPOLANT_AUTOMATON, MessageType.EXCEPTION);
		case WITNESS -> EnumSet.of(MessageType.WITNESS, MessageType.EXCEPTION);
		case DISABLED -> throw new IllegalArgumentException("DISABLED is not a session kind");
		};
	}
}
