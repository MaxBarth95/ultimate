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

/**
 * The message types of the exchange, as UltimateCloud's {@code UltimateMessage.MessageType}. Only the types that a
 * session kind of this phase sends or receives are listed; any other type in the session directory throws.
 */
public enum MessageType {
	/**
	 * The coordinator's abstraction, a full snapshot, by generation.
	 */
	ABSTRACTION(ContentFormat.ATS_V1),
	/**
	 * A counterexample word for a TA worker to check (a job).
	 */
	COUNTEREXAMPLE(ContentFormat.JSON_V1),
	/**
	 * Cancels a job.
	 */
	CANCEL(ContentFormat.JSON_V1),
	/**
	 * A TA worker's result for a job.
	 */
	RESULT(ContentFormat.JSON_V1),
	/**
	 * The automaton a TA worker built for a job, which the coordinator refines with.
	 */
	INTERPOLANT_AUTOMATON(ContentFormat.ATS_V1),
	/**
	 * A decision of the run, with its evidence.
	 */
	VERDICT(ContentFormat.JSON_V1),
	/**
	 * The coordinator's final Floyd-Hoare annotation.
	 */
	PROOF_ANNOTATION(ContentFormat.JSON_V1),
	/**
	 * The witness of the WITNESS session.
	 */
	WITNESS(ContentFormat.YAML_V1),
	/**
	 * A failure of a session.
	 */
	EXCEPTION(ContentFormat.JSON_V1),
	/**
	 * A session stops early without a verdict.
	 */
	RETIRED(ContentFormat.JSON_V1);

	private final ContentFormat mFormat;

	MessageType(final ContentFormat format) {
		mFormat = format;
	}

	/**
	 * @return the format of the body of this message type
	 */
	public ContentFormat getFormat() {
		return mFormat;
	}

	/**
	 * @return the message type with this name
	 * @throws IllegalArgumentException
	 *             if there is no such message type
	 */
	public static MessageType fromName(final String name) {
		for (final MessageType type : values()) {
			if (type.name().equals(name)) {
				return type;
			}
		}
		throw new IllegalArgumentException("Unknown message type: " + name);
	}
}
