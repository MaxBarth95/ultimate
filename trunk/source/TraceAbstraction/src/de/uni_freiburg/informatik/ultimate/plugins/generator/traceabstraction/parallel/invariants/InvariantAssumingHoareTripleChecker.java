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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Checks {@code {P} a {Q}} like the underlying checker, and if that is not valid, checks
 * {@code {P and I(src(a))} a {Q}} once more, where {@code I(src(a))} is the proven invariant of the source location of
 * {@code a}. For a return, only the linear predecessor is strengthened.
 * <p>
 * <b>Soundness.</b> The triples this checker calls valid are not valid in general, only in the states the program can
 * reach. That is enough for an interpolant automaton built with them: along a feasible execution of a word, the state
 * before each letter {@code a} satisfies {@code I(src(a))}, since the invariants hold in every reachable state of their
 * location. By induction over a run of the automaton from {@code true}, every state of the execution satisfies the
 * predicate of the automaton state, so no feasible word reaches {@code false}, and the difference removes only
 * infeasible words. The invariants must therefore be location invariants, i.e. hold at every visit of the location;
 * see {@link InvariantSupplier#subscribeForTa}.
 * <p>
 * The strengthened predecessors never go into the predicate unifier, which would compare them with every predicate.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class InvariantAssumingHoareTripleChecker implements IHoareTripleChecker {

	private final IHoareTripleChecker mUnderlying;
	private final MonolithicHoareTripleChecker mStrengthened;
	private final BasicPredicateFactory mPredicateFactory;
	private final ManagedScript mMgdScript;
	private final InvariantSnapshot mInvariants;
	// (pre, [preHier,] act, post) -> what the check with the invariant answered
	private final Map<List<Object>, Validity> mCache = new HashMap<>();
	private int mChecks;
	private int mValidOnlyWithInvariant;

	public InvariantAssumingHoareTripleChecker(final IHoareTripleChecker underlying, final CfgSmtToolkit csToolkit,
			final BasicPredicateFactory predicateFactory, final InvariantSnapshot invariants) {
		mUnderlying = underlying;
		mStrengthened = new MonolithicHoareTripleChecker(csToolkit);
		mPredicateFactory = predicateFactory;
		mMgdScript = csToolkit.getManagedScript();
		mInvariants = invariants;
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		final Validity result = mUnderlying.checkInternal(pre, act, succ);
		final IPredicate invariant = invariantBefore(act, result, pre);
		if (invariant == null) {
			return result;
		}
		return checkStrengthened(List.of(pre, act, succ), result,
				() -> mStrengthened.checkInternal(mPredicateFactory.and(pre, invariant), act, succ));
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		final Validity result = mUnderlying.checkCall(pre, act, succ);
		final IPredicate invariant = invariantBefore(act, result, pre);
		if (invariant == null) {
			return result;
		}
		return checkStrengthened(List.of(pre, act, succ), result,
				() -> mStrengthened.checkCall(mPredicateFactory.and(pre, invariant), act, succ));
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		final Validity result = mUnderlying.checkReturn(preLin, preHier, act, succ);
		final IPredicate invariant = invariantBefore(act, result, preLin);
		if (invariant == null) {
			return result;
		}
		return checkStrengthened(List.of(preLin, preHier, act, succ), result,
				() -> mStrengthened.checkReturn(mPredicateFactory.and(preLin, invariant), preHier, act, succ));
	}

	/**
	 * @return the invariant to assume before {@code act}, or {@code null} if there is no point in a second check
	 */
	private IPredicate invariantBefore(final IAction act, final Validity result, final IPredicate pre) {
		if (result == Validity.VALID || !(act instanceof IIcfgTransition<?>) || mPredicateFactory.isDontCare(pre)) {
			return null;
		}
		return mInvariants.at(((IIcfgTransition<?>) act).getSource());
	}

	private Validity checkStrengthened(final List<Object> key, final Validity unstrengthened,
			final Supplier<Validity> check) {
		final Validity cached = mCache.get(key);
		if (cached != null) {
			return cached == Validity.VALID ? cached : unstrengthened;
		}
		// The underlying checker may hold the solver between its checks, the monolithic one locks it per check.
		mUnderlying.releaseLock();
		if (mMgdScript.isLocked()) {
			mMgdScript.requestLockRelease();
		}
		mChecks++;
		final Validity result = check.get();
		mCache.put(key, result);
		if (result == Validity.VALID) {
			mValidOnlyWithInvariant++;
			return result;
		}
		return unstrengthened;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mUnderlying.getStatistics();
	}

	@Override
	public void releaseLock() {
		mUnderlying.releaseLock();
		mStrengthened.releaseLock();
	}

	/**
	 * @return how many triples were checked again with an invariant
	 */
	public int getStrengthenedChecks() {
		return mChecks;
	}

	/**
	 * @return how many triples were valid only with an invariant
	 */
	public int getValidOnlyWithInvariant() {
		return mValidOnlyWithInvariant;
	}

	@Override
	public String toString() {
		return "InvariantAssumingHtc: " + mValidOnlyWithInvariant + " of " + mChecks
				+ " triple(s) checked with invariants valid only with invariants, underlying: " + mUnderlying;
	}
}
