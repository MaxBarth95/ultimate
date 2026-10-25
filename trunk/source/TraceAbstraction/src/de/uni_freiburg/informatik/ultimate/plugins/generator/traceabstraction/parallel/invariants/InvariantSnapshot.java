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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * The invariants a TA worker took from its {@link InvariantSubscription}, as predicates of the worker's own script,
 * for the counterexample it checks. The subscription delivers terms only; the predicates are built here with the
 * worker's predicate factory, so that their variables are the worker's own program variables.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class InvariantSnapshot {

	private static final InvariantSnapshot EMPTY = new InvariantSnapshot(Collections.emptyMap(), 0);

	private final Map<IcfgLocation, IPredicate> mInvariants;
	private final int mVersion;

	private InvariantSnapshot(final Map<IcfgLocation, IPredicate> invariants, final int version) {
		mInvariants = invariants;
		mVersion = version;
	}

	/**
	 * @return a snapshot without invariants
	 */
	public static InvariantSnapshot empty() {
		return EMPTY;
	}

	/**
	 * Takes what the supplier published since the last call and builds predicates for it. Must be called by the thread
	 * that owns the subscription's target script.
	 *
	 * @param cache
	 *            term -> its predicate, kept by the worker across snapshots, since an unchanged invariant is always
	 *            the very same term
	 */
	public static InvariantSnapshot take(final InvariantSubscription subscription,
			final BasicPredicateFactory predicateFactory, final IIcfgSymbolTable symbolTable,
			final Map<Term, IPredicate> cache, final ILogger logger) {
		subscription.update();
		final Map<IcfgLocation, IPredicate> invariants = new HashMap<>();
		for (final IcfgLocation location : subscription.getLocations()) {
			final Optional<Term> term = subscription.getInvariantAt(location);
			if (term.isEmpty() || SmtUtils.isTrueLiteral(term.get())) {
				continue;
			}
			final IPredicate predicate = cache.computeIfAbsent(term.get(),
					t -> toPredicate(t, location, predicateFactory, symbolTable, logger));
			if (predicate != null) {
				invariants.put(location, predicate);
			}
		}
		return new InvariantSnapshot(invariants, subscription.takenVersion());
	}

	/**
	 * @return the predicate, or {@code null} if the term cannot be expressed over the worker's program variables
	 */
	private static IPredicate toPredicate(final Term term, final IcfgLocation location,
			final BasicPredicateFactory predicateFactory, final IIcfgSymbolTable symbolTable, final ILogger logger) {
		for (final TermVariable tv : term.getFreeVars()) {
			if (symbolTable.getProgramVar(tv) == null) {
				logger.warn("TA worker: ignoring the invariant of %s, %s is no program variable of the worker: %s",
						location, tv, term);
				return null;
			}
		}
		try {
			return predicateFactory.newPredicate(term);
		} catch (final AssertionError e) {
			// Only an invariant gets lost, which is always sound: e.g. a program function the worker does not know.
			logger.warn("TA worker: ignoring the invariant of %s, no predicate for it (%s): %s", location,
					e.getMessage(), term);
			return null;
		}
	}

	/**
	 * @return the invariant of {@code location}, or {@code null} if there is none
	 */
	public IPredicate at(final IcfgLocation location) {
		return mInvariants.get(location);
	}

	public boolean isEmpty() {
		return mInvariants.isEmpty();
	}

	public Set<IcfgLocation> getLocations() {
		return Collections.unmodifiableSet(mInvariants.keySet());
	}

	/**
	 * @return the version of the published invariants this snapshot was taken from
	 */
	public int getVersion() {
		return mVersion;
	}
}
