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

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicReference;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.CallNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.IInvariantSupplier;

/**
 * The invariants the abstract interpretation worker has found so far, one term per abstraction state, published and
 * read without anyone waiting. Only the worker builds terms in the store's private script; snapshots are immutable,
 * and each k-induction worker copies what it needs into its own script.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class AbsIntInvariantStore {

	private final ManagedScript mScript;
	private final AtomicReference<Map<IPredicate, Term>> mInvariants = new AtomicReference<>(Collections.emptyMap());

	/**
	 * Must be called on the thread that owns the main script, whose declarations are replayed onto the store's.
	 */
	public AbsIntInvariantStore(final CfgSmtToolkit mainCsToolkit, final IUltimateServiceProvider services) {
		// Only used to build terms, never to solve, so an in-process SMTInterpol suffices.
		mScript = mainCsToolkit.createFreshManagedScript(services,
				SolverBuilder.constructSolverSettings().setSolverLogics(Logics.ALL), "AbsIntTerms", "absint_");
	}

	/**
	 * @return the script the published terms belong to; only the abstract interpretation worker may build terms in it
	 */
	public ManagedScript getScript() {
		return mScript;
	}

	/**
	 * Conjoins {@code invariants} with what was published before. Only to be called by the abstract interpretation
	 * worker.
	 */
	public void publish(final Map<IPredicate, Term> invariants) {
		final Map<IPredicate, Term> conjunction = new HashMap<>(mInvariants.get());
		for (final Entry<IPredicate, Term> entry : invariants.entrySet()) {
			conjunction.merge(entry.getKey(), entry.getValue(),
					(older, newer) -> SmtUtils.and(mScript.getScript(), older, newer));
		}
		mInvariants.set(Collections.unmodifiableMap(conjunction));
	}

	/**
	 * @param targetScript
	 *            the script of one k-induction worker
	 * @return a supplier of the latest invariants as terms of {@code targetScript}, to be used only by the thread that
	 *         owns {@code targetScript}
	 */
	public IInvariantSupplier<CallNode<IPredicate>> supplierFor(final ManagedScript targetScript) {
		return new IInvariantSupplier<>() {
			private TermTransferrer mTransferrer;

			@Override
			public Optional<Term> getInvariant(final CallNode<IPredicate> loopHead, final ManagedScript script) {
				if (script != targetScript) {
					return Optional.empty();
				}
				// The invariant of a state holds in every calling context, hence for every call node of it.
				final Term invariant = mInvariants.get().get(loopHead.getState());
				if (invariant == null) {
					return Optional.empty();
				}
				if (mTransferrer == null) {
					mTransferrer = new TermTransferrer(mScript.getScript(), targetScript.getScript());
				}
				return Optional.of(mTransferrer.transform(invariant));
			}
		};
	}
}
