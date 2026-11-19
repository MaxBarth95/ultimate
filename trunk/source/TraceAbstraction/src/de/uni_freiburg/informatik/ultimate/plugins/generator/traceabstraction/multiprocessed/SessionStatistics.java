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

import java.util.Map;
import java.util.TreeMap;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.MultiProcessComponent;

/**
 * The statistics of a session, written as {@code out/statistics.json} when the session ends (R8):
 * {@code {format, kind, sessionId, end, wallTimeMs, counters, ultimate}}. {@code counters} are the kind's own
 * numbers, {@code ultimate} is Ultimate's flattened benchmark data.
 */
public final class SessionStatistics {

	/**
	 * How the session ended.
	 */
	public enum End {
		/** {@code in/shutdown} asked the session to stop. */
		SHUTDOWN,
		/** The session reached its time limit. */
		TIME_LIMIT,
		/** The kind wrote its final output. */
		DONE,
		/** The session failed. */
		EXCEPTION
	}

	private static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();

	private final MultiProcessComponent mKind;
	private final String mSessionId;
	private final long mStartNanos = System.nanoTime();
	private final Map<String, Long> mCounters = new TreeMap<>();
	private final Map<String, Object> mUltimate = new TreeMap<>();

	public SessionStatistics(final MultiProcessComponent kind, final String sessionId) {
		mKind = kind;
		mSessionId = sessionId;
	}

	/**
	 * Adds one to a counter.
	 */
	public void increment(final String counter) {
		add(counter, 1);
	}

	/**
	 * Adds to a counter.
	 */
	public void add(final String counter, final long value) {
		mCounters.merge(counter, value, Long::sum);
	}

	/**
	 * Raises a counter to {@code value} if it is lower.
	 */
	public void max(final String counter, final long value) {
		mCounters.merge(counter, value, Long::max);
	}

	/**
	 * Sets a counter.
	 */
	public void set(final String counter, final long value) {
		mCounters.put(counter, value);
	}

	/**
	 * Sets a counter to 0 if it has no value yet, so that it shows up.
	 */
	public void declare(final String... counters) {
		for (final String counter : counters) {
			mCounters.putIfAbsent(counter, 0L);
		}
	}

	/**
	 * Adds Ultimate's benchmark data; values that are no numbers or booleans become strings.
	 */
	public void addUltimate(final Map<String, Object> flattened) {
		for (final Map.Entry<String, Object> entry : flattened.entrySet()) {
			final Object value = entry.getValue();
			if (value instanceof Number || value instanceof Boolean) {
				mUltimate.put(entry.getKey(), value);
			} else {
				mUltimate.put(entry.getKey(), String.valueOf(value));
			}
		}
	}

	/**
	 * @return the JSON of {@code out/statistics.json}
	 */
	public String toJson(final End end) {
		final JsonObject object = new JsonObject();
		object.addProperty(JsonCodec.FORMAT_KEY, JsonCodec.FORMAT);
		object.addProperty("kind", mKind.name());
		object.addProperty("sessionId", mSessionId);
		object.addProperty("end", end.name());
		object.addProperty("wallTimeMs", (System.nanoTime() - mStartNanos) / 1_000_000);
		object.add("counters", GSON.toJsonTree(mCounters));
		object.add("ultimate", GSON.toJsonTree(mUltimate));
		return GSON.toJson(object);
	}

	/**
	 * Writes {@code out/statistics.json}. A failure while writing is added to {@code failure} as suppressed, if there is
	 * one, and thrown otherwise.
	 */
	public void write(final IExchange exchange, final End end, final Throwable failure) {
		try {
			exchange.writeStatistics(toJson(end));
		} catch (final RuntimeException e) {
			if (failure == null) {
				throw e;
			}
			failure.addSuppressed(e);
		}
	}
}
