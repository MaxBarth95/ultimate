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

import java.util.Arrays;

/**
 * The format of a message body, as UltimateCloud's {@code ContentFormat}. The file extension of a message in the
 * session directory follows the format.
 */
public enum ContentFormat {
	/**
	 * An automaton in the automata script format with full letter names {@code e<id>:<text>} (Phases 2 to 5). It has
	 * the extension of {@link #ATS_V2}; {@link AtsCodec} still reads it, for old recordings.
	 */
	ATS_V1("ats"),
	/**
	 * An automaton in the automata script format with edge-id letters {@code e<id>}, see {@link AtsCodec}. Since Phase
	 * 6, the extension {@code ats} means this format.
	 */
	ATS_V2("ats"),
	/**
	 * Every message that is not an automaton, see {@link JsonCodec}.
	 */
	JSON_V1("json"),
	/**
	 * A YAML witness, format 2.x.
	 */
	YAML_V1("yml"),
	/**
	 * A protobuf nested word automaton (Phase 6).
	 */
	NWA_PB_V1("pb");

	private final String mExtension;

	ContentFormat(final String extension) {
		mExtension = extension;
	}

	/**
	 * @return the file extension, without the dot
	 */
	public String getExtension() {
		return mExtension;
	}

	/**
	 * @return the current format with this file extension ({@link #ATS_V2} for {@code ats})
	 * @throws IllegalArgumentException
	 *             if no format has this extension
	 */
	public static ContentFormat fromExtension(final String extension) {
		return Arrays.stream(values()).filter(f -> f != ATS_V1 && f.mExtension.equals(extension)).findFirst()
				.orElseThrow(() -> new IllegalArgumentException("Unknown message file extension: ." + extension));
	}
}
