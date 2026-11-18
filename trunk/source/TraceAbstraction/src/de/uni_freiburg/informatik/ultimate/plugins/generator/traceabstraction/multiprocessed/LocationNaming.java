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

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Names the program points of a program across processes: {@code <procedure>::<debugId>}.
 * {@link IcfgLocation#toString()} lacks the procedure, so it alone is not unique.
 */
public final class LocationNaming {

	private final Map<String, IcfgLocation> mNameToLocation = new HashMap<>();
	private final Map<IcfgLocation, String> mLocationToName = new HashMap<>();

	/**
	 * @param icfg
	 *            the program
	 * @throws IllegalArgumentException
	 *             if two program points get the same name
	 */
	public LocationNaming(final IIcfg<? extends IcfgLocation> icfg) {
		for (final Entry<String, ? extends Map<?, ? extends IcfgLocation>> proc : icfg.getProgramPoints()
				.entrySet()) {
			for (final IcfgLocation loc : proc.getValue().values()) {
				final String name = nameOf(loc);
				final IcfgLocation previous = mNameToLocation.put(name, loc);
				if (previous != null && previous != loc) {
					throw new IllegalArgumentException("Two program points named " + name);
				}
				mLocationToName.put(loc, name);
			}
		}
	}

	/**
	 * @return the name of a program point
	 * @throws IllegalArgumentException
	 *             if it is not a program point of the program
	 */
	public String name(final IcfgLocation loc) {
		final String name = mLocationToName.get(loc);
		if (name == null) {
			throw new IllegalArgumentException("Not a program point of the program: " + loc);
		}
		return name;
	}

	/**
	 * @return the program point with this name
	 * @throws IllegalArgumentException
	 *             if there is none
	 */
	public IcfgLocation resolve(final String name) {
		final IcfgLocation loc = mNameToLocation.get(name);
		if (loc == null) {
			throw new IllegalArgumentException("Unknown program point: " + name);
		}
		return loc;
	}

	private static String nameOf(final IcfgLocation loc) {
		return loc.getProcedure() + "::" + loc.getDebugIdentifier();
	}
}
