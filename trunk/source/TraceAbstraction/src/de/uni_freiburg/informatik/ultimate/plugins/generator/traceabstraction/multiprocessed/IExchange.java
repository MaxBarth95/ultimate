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

import java.time.Instant;
import java.util.Optional;
import java.util.OptionalLong;

/**
 * How a session reads and writes messages. Role code uses only this interface and never touches paths, so that the
 * exchange can be the session directory ({@link FileExchange}), or later gRPC or memory.
 */
public interface IExchange extends AutoCloseable {

	/**
	 * Waits for the next incoming message, in sequence order.
	 *
	 * @param deadline
	 *            when to stop waiting
	 * @return the next message, or empty if the session was asked to shut down
	 * @throws DeadlineExpiredException
	 *             if no message arrived before the deadline
	 * @throws IllegalArgumentException
	 *             if the next message has an unknown type or format, or one the session kind does not accept
	 */
	Optional<ExchangeMessage> take(Instant deadline);

	/**
	 * @return the next incoming message if one is already there, or empty if there is none or the session was asked
	 *         to shut down; never waits
	 */
	Optional<ExchangeMessage> poll();

	/**
	 * @return whether the session was asked to shut down
	 */
	boolean isShutdownRequested();

	/**
	 * Sends a message.
	 *
	 * @param type
	 *            the message type; the session kind must emit it
	 * @param job
	 *            the job id, if the message belongs to a job
	 * @param generation
	 *            the abstraction generation, if the message refers to one
	 * @param body
	 *            the body, in the format of the type
	 */
	void send(MessageType type, OptionalLong job, OptionalLong generation, String body);

	/**
	 * Announces that the session is ready. Must be called once, before any message is sent.
	 *
	 * @param ready
	 *            the content of the ready announcement
	 */
	void announceReady(ReadyFile ready);

	@Override
	void close();
}
