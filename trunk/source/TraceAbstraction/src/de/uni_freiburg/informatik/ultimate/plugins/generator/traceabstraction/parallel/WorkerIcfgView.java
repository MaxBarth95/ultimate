/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;

/**
 * The ICFG of the main thread as a worker sees it: the same locations, but the {@link CfgSmtToolkit} of the worker.
 * <p>
 * The letters of a worker are copies whose transition formulas live in the worker's script, while their source and
 * target are the locations of the main ICFG. Techniques that build a path program from the letters of a trace, such
 * as PDR or accelerated interpolation, take the toolkit of the path program from the ICFG they are given, so with the
 * main ICFG they would mix the terms of both scripts.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class WorkerIcfgView<LOC extends IcfgLocation> implements IIcfg<LOC> {

	private final IIcfg<LOC> mMainIcfg;
	private final CfgSmtToolkit mWorkerToolkit;

	public WorkerIcfgView(final IIcfg<LOC> mainIcfg, final CfgSmtToolkit workerToolkit) {
		mMainIcfg = mainIcfg;
		mWorkerToolkit = workerToolkit;
	}

	@Override
	public CfgSmtToolkit getCfgSmtToolkit() {
		return mWorkerToolkit;
	}

	@Override
	public Map<String, Map<DebugIdentifier, LOC>> getProgramPoints() {
		return mMainIcfg.getProgramPoints();
	}

	@Override
	public Map<String, LOC> getProcedureEntryNodes() {
		return mMainIcfg.getProcedureEntryNodes();
	}

	@Override
	public Map<String, LOC> getProcedureExitNodes() {
		return mMainIcfg.getProcedureExitNodes();
	}

	@Override
	public Map<String, Set<LOC>> getProcedureErrorNodes() {
		return mMainIcfg.getProcedureErrorNodes();
	}

	@Override
	public Set<LOC> getLocationsOfInterest() {
		return mMainIcfg.getLocationsOfInterest();
	}

	@Override
	public Set<LOC> getLoopLocations() {
		return mMainIcfg.getLoopLocations();
	}

	@Override
	public Set<LOC> getInitialNodes() {
		return mMainIcfg.getInitialNodes();
	}

	@Override
	public String getIdentifier() {
		return mMainIcfg.getIdentifier();
	}

	@Override
	public Class<LOC> getLocationClass() {
		return mMainIcfg.getLocationClass();
	}

	@Override
	public IPayload getPayload() {
		return mMainIcfg.getPayload();
	}

	@Override
	public boolean hasPayload() {
		return mMainIcfg.hasPayload();
	}

	@Override
	public String toString() {
		return "worker view of " + mMainIcfg;
	}
}
