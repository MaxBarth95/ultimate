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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.absint;

import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.IInvariantSupplier;

/**
 * The fixpoint of an abstract interpretation run over the main abstraction, as invariants of its states. The terms
 * are main-script terms, built lazily on the first request, so the caller must be the owner of the main script.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class AbsIntInvariantSupplier implements IInvariantSupplier<IPredicate> {

	private final IAbstractInterpretationResult<?, IcfgEdge, IPredicate> mResult;
	private final ManagedScript mMainScript;

	public AbsIntInvariantSupplier(final IAbstractInterpretationResult<?, IcfgEdge, IPredicate> result,
			final ManagedScript mainScript) {
		mResult = result;
		mMainScript = mainScript;
	}

	@Override
	public Optional<Term> getInvariant(final IPredicate state, final ManagedScript targetScript) {
		if (targetScript != mMainScript) {
			return Optional.empty();
		}
		return Optional.ofNullable(mResult.getLoc2Term().get(state));
	}
}
