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

import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParseException;
import com.google.gson.JsonParser;

/**
 * Reads and writes the JSON_V1 messages. Every message object carries {@code "format": "JSON_V1"}. Reading is strict:
 * a wrong format, an unknown field, or a missing required field throws.
 *
 * Formulas are SMT-LIB terms over the program variables, locations are {@link LocationNaming} names, and words are
 * {@link WordCodec} forms.
 */
public final class JsonCodec {

	public static final String FORMAT_KEY = "format";
	public static final String FORMAT = "JSON_V1";

	private static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();

	/**
	 * The outcome of a TA worker's job.
	 */
	public enum ResultStatus {
		/** The counterexample is infeasible; the interpolant automaton is a Floyd-Hoare automaton. */
		UNSAT,
		/** The counterexample is feasible; the result carries its word. */
		SAT,
		/** The trace check could not decide. */
		UNKNOWN
	}

	/**
	 * The kind of automaton a TA worker returns with its result.
	 */
	public enum AutomatonType {
		FLOYD_HOARE, ERROR
	}

	/**
	 * A verdict of the run.
	 */
	public enum VerdictValue {
		TRUE, FALSE, UNKNOWN
	}

	/**
	 * {@code COUNTEREXAMPLE}: a word for a TA worker to check against an abstraction generation.
	 * {@code pathProgramCount} is how often the coordinator handed out a word of this path program, this one included.
	 */
	public record Counterexample(long job, long generation, List<String> word, List<Integer> nesting,
			int pathProgramCount) {
		static final Set<String> OPTIONAL = Set.of();
	}

	/**
	 * The reason of the synthetic {@link Result} for a TA session that was killed by a signal or became unreachable.
	 */
	public static final String REASON_SESSION_LOST = "SESSION_LOST";
	/** The reason of the synthetic {@link Result} for a TA session whose Ultimate threw. */
	public static final String REASON_SESSION_CRASHED = "SESSION_CRASHED";

	/**
	 * {@code RESULT}: a TA worker's answer for a job. A SAT result carries the feasible word. A TA worker always sets
	 * the automaton type; only the synthetic result for a lost or crashed session ({@link #REASON_SESSION_LOST},
	 * {@link #REASON_SESSION_CRASHED}) has none.
	 */
	public record Result(long job, long generation, ResultStatus status, AutomatonType automatonType,
			List<String> word, List<Integer> nesting, String reason) {
		static final Set<String> OPTIONAL = Set.of("automatonType", "word", "nesting", "reason");

		/**
		 * @return whether this is the synthetic result for a lost or crashed TA session (see {@link #reason()})
		 * @throws IllegalArgumentException
		 *             if the result has no automaton type but is not a synthetic one
		 */
		public boolean isSynthetic() {
			final boolean synthetic = REASON_SESSION_LOST.equals(reason) || REASON_SESSION_CRASHED.equals(reason);
			if (synthetic && (status != ResultStatus.UNKNOWN || automatonType != null || word != null)) {
				throw new IllegalArgumentException("Malformed " + reason + " result for job " + job);
			}
			if (!synthetic && automatonType == null) {
				throw new IllegalArgumentException("Result for job " + job + " without an automaton type");
			}
			return synthetic;
		}
	}

	/** {@code CANCEL}: stop working on a job. */
	public record Cancel(long job) {
		static final Set<String> OPTIONAL = Set.of();
	}

	/** {@code PROOF_ANNOTATION}: the Floyd-Hoare annotation, location name to formula. */
	public record ProofAnnotation(long generation, SortedMap<String, String> invariants) {
		static final Set<String> OPTIONAL = Set.of();
	}

	/** The evidence of a {@link Verdict}. Phase 8 adds waypoints and the proving invariant version. */
	public record Evidence(List<String> word, List<Integer> nesting, SortedMap<String, String> invariants) {
		static final Set<String> OPTIONAL = Set.of("word", "nesting", "invariants");
	}

	/** {@code VERDICT}: a decision of the run and the kind that decided it. */
	public record Verdict(VerdictValue verdict, String decidedBy, Evidence evidence) {
		static final Set<String> OPTIONAL = Set.of();
	}

	/** {@code EXCEPTION}: a session failed. */
	public record ExceptionReport(String kind, String exceptionClass, String message, String stackTrace) {
		static final Set<String> OPTIONAL = Set.of("message");
	}

	/** {@code RETIRED}: a session stops early without a verdict. */
	public record Retired(String reason) {
		static final Set<String> OPTIONAL = Set.of();
	}

	private JsonCodec() {
		// static helpers only
	}

	/**
	 * @return the JSON_V1 text of a message record
	 */
	public static String encode(final Record message) {
		final JsonObject object = new JsonObject();
		object.addProperty(FORMAT_KEY, FORMAT);
		final JsonObject fields = GSON.toJsonTree(message).getAsJsonObject();
		for (final Map.Entry<String, JsonElement> entry : fields.entrySet()) {
			object.add(entry.getKey(), entry.getValue());
		}
		return GSON.toJson(object);
	}

	/**
	 * @return the message record of a JSON_V1 text
	 * @throws IllegalArgumentException
	 *             if the text is not JSON_V1, has unknown fields, or misses a required field
	 */
	public static <T extends Record> T decode(final String json, final Class<T> clazz) {
		final JsonObject object = parseObject(json);
		final JsonElement format = object.remove(FORMAT_KEY);
		if (format == null || !format.isJsonPrimitive() || !FORMAT.equals(format.getAsString())) {
			throw new IllegalArgumentException(
					"Not a " + FORMAT + " message (format " + format + "): " + clazz.getSimpleName());
		}
		return decodePlain(object, clazz);
	}

	/**
	 * Reads a record from a JSON object without a format field (the blob reference and the ready file).
	 */
	static <T extends Record> T decodePlain(final String json, final Class<T> clazz) {
		return decodePlain(parseObject(json), clazz);
	}

	/**
	 * Writes a record as JSON without a format field (the blob reference and the ready file).
	 */
	static String encodePlain(final Record record) {
		return GSON.toJson(record);
	}

	private static <T extends Record> T decodePlain(final JsonObject object, final Class<T> clazz) {
		checkFields(object, clazz);
		try {
			return GSON.fromJson(object, clazz);
		} catch (final JsonParseException | IllegalStateException | NumberFormatException e) {
			throw new IllegalArgumentException("Malformed " + clazz.getSimpleName() + ": " + e.getMessage(), e);
		}
	}

	private static JsonObject parseObject(final String json) {
		final JsonElement element;
		try {
			element = JsonParser.parseString(json);
		} catch (final JsonParseException e) {
			throw new IllegalArgumentException("Malformed JSON: " + e.getMessage(), e);
		}
		if (!element.isJsonObject()) {
			throw new IllegalArgumentException("Expected a JSON object, got " + json);
		}
		return element.getAsJsonObject();
	}

	private static void checkFields(final JsonObject object, final Class<?> clazz) {
		final Set<String> optional = optionalFields(clazz);
		final Set<String> known = new HashSet<>();
		for (final RecordComponent component : clazz.getRecordComponents()) {
			final String name = component.getName();
			known.add(name);
			final JsonElement value = object.get(name);
			if (value == null || value.isJsonNull()) {
				if (!optional.contains(name)) {
					throw new IllegalArgumentException(
							clazz.getSimpleName() + " misses the required field \"" + name + "\"");
				}
				continue;
			}
			final Class<?> type = component.getType();
			if (type.isEnum()) {
				// Gson reads an unknown enum constant as null instead of failing
				checkEnumConstant(clazz, name, type, value);
			}
			if (type.isRecord()) {
				if (!value.isJsonObject()) {
					throw new IllegalArgumentException(
							clazz.getSimpleName() + "." + name + " must be an object, not " + value);
				}
				checkFields(value.getAsJsonObject(), type);
			}
			checkNoNullElements(clazz, name, component.getGenericType(), value);
		}
		for (final String key : object.keySet()) {
			if (!known.contains(key)) {
				throw new IllegalArgumentException(clazz.getSimpleName() + " has an unknown field \"" + key + "\"");
			}
		}
	}

	private static void checkEnumConstant(final Class<?> clazz, final String name, final Class<?> type,
			final JsonElement value) {
		if (value.isJsonPrimitive() && value.getAsJsonPrimitive().isString()) {
			for (final Object constant : type.getEnumConstants()) {
				if (((Enum<?>) constant).name().equals(value.getAsString())) {
					return;
				}
			}
		}
		throw new IllegalArgumentException(
				clazz.getSimpleName() + "." + name + " has an unknown value " + value + " for " + type.getSimpleName());
	}

	private static void checkNoNullElements(final Class<?> clazz, final String name, final Type type,
			final JsonElement value) {
		if (!(type instanceof ParameterizedType)) {
			return;
		}
		if (value.isJsonArray()) {
			for (final JsonElement element : value.getAsJsonArray()) {
				if (element.isJsonNull()) {
					throw new IllegalArgumentException(clazz.getSimpleName() + "." + name + " contains null");
				}
			}
		} else if (value.isJsonObject()) {
			for (final Map.Entry<String, JsonElement> entry : value.getAsJsonObject().entrySet()) {
				if (entry.getValue().isJsonNull()) {
					throw new IllegalArgumentException(
							clazz.getSimpleName() + "." + name + "." + entry.getKey() + " is null");
				}
			}
		}
	}

	@SuppressWarnings("unchecked")
	private static Set<String> optionalFields(final Class<?> clazz) {
		try {
			final var field = clazz.getDeclaredField("OPTIONAL");
			field.setAccessible(true);
			return (Set<String>) field.get(null);
		} catch (final NoSuchFieldException e) {
			return Set.of();
		} catch (final IllegalAccessException e) {
			throw new IllegalStateException(e);
		}
	}
}
