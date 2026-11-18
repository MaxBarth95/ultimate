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

import java.util.Objects;
import java.util.OptionalLong;

/**
 * One message of the exchange: its type, the optional job id and abstraction generation from its file name, and its
 * body. A body stored in {@code blobs/} is already resolved.
 *
 * @param seq
 *            the sequence number of the message in its direction
 * @param type
 *            the message type
 * @param job
 *            the job id, if the message belongs to a job
 * @param generation
 *            the abstraction generation, if the message refers to one
 * @param body
 *            the body, in the format of the type
 */
public record ExchangeMessage(long seq, MessageType type, OptionalLong job, OptionalLong generation, String body) {

	public ExchangeMessage {
		Objects.requireNonNull(type);
		Objects.requireNonNull(job);
		Objects.requireNonNull(generation);
		Objects.requireNonNull(body);
		if (seq < 0) {
			throw new IllegalArgumentException("Negative sequence number " + seq);
		}
	}

	/**
	 * @return the job id
	 * @throws IllegalStateException
	 *             if the message has no job id
	 */
	public long requireJob() {
		if (job.isEmpty()) {
			throw new IllegalStateException(type + " message " + seq + " has no job id");
		}
		return job.getAsLong();
	}

	/**
	 * @return the abstraction generation
	 * @throws IllegalStateException
	 *             if the message has no generation
	 */
	public long requireGeneration() {
		if (generation.isEmpty()) {
			throw new IllegalStateException(type + " message " + seq + " has no generation");
		}
		return generation.getAsLong();
	}
}
