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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.invariants;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.CallNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.IndexedConstantVars;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.PcTransitionSystem;

/**
 * Finds the largest subset of candidate invariants that is inductive relative to invariants already known, on the
 * {@link PcTransitionSystem} of the program (Houdini).
 * <p>
 * A candidate is a conjunct attached to a program location; it stands for every pc node of that location (loop heads
 * and waypoints, in every calling context). One query checks all remaining candidates at once:
 *
 * <pre>
 *   AND_node (pc_0 = node  ->  known(loc(node)) and candidates(loc(node)))  at step 0
 *   and step(0)
 *   and OR_node OR_c (pc_1 = node  and  not c)                             at step 1
 * </pre>
 *
 * INIT has no precondition, so the query covers initiation and consecution together. If it is unsatisfiable, every
 * remaining candidate holds at the first visit of its location and is preserved from every pc node to the next, given
 * that the known invariants and all remaining candidates hold at the source, so by induction over the pc steps of an
 * execution all of them are invariants - provided the known ones are. If it is satisfiable, the candidates that are
 * false at the target of the model are dropped and the query is repeated; each round drops at least one, so this ends.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
final class InductivenessChecker {

	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final PcTransitionSystem<CallNode<IPredicate>> mSystem;
	// pc node -> its program location, for every loop head and waypoint
	private final Map<Integer, IcfgLocation> mLocationOfNode = new LinkedHashMap<>();
	private final Map<TermVariable, IProgramVar> mVarOfTermVariable = new HashMap<>();
	private final IndexedConstantVars mConstants;
	private Term mStep;

	InductivenessChecker(final ILogger logger, final ManagedScript mgdScript,
			final PcTransitionSystem<CallNode<IPredicate>> system) {
		mLogger = logger;
		mMgdScript = mgdScript;
		mSystem = system;
		for (final Map.Entry<CallNode<IPredicate>, Integer> head : system.getHeadNodes().entrySet()) {
			mLocationOfNode.put(head.getValue(), InvariantSupplier.locationOf(head.getKey().getState()));
		}
		for (final Map.Entry<CallNode<IPredicate>, Integer> waypoint : system.getWaypointNodes().entrySet()) {
			mLocationOfNode.put(waypoint.getValue(), InvariantSupplier.locationOf(waypoint.getKey().getState()));
		}
		for (final IProgramVar pv : system.getVars()) {
			mVarOfTermVariable.put(pv.getTermVariable(), pv);
		}
		mConstants = new IndexedConstantVars(mgdScript.getScript(), new HashMap<>(), "inv");
	}

	/** @return true if {@code location} has a pc node, i.e. a candidate there can be checked */
	boolean hasNode(final IcfgLocation location) {
		return mLocationOfNode.containsValue(location);
	}

	/**
	 * @return true if every free variable of {@code term} is a variable of the transition system. Anything else cannot
	 *         be checked and would be ignored by k-induction anyway.
	 */
	boolean isExpressible(final Term term) {
		for (final TermVariable tv : term.getFreeVars()) {
			if (!mVarOfTermVariable.containsKey(tv)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * @param known
	 *            invariants that are known to hold, per location
	 * @param candidates
	 *            candidate conjuncts per location, every one {@link #isExpressible} at a location that
	 *            {@link #hasNode}
	 * @return the candidates that are inductive relative to {@code known}, per location, or {@code null} if the solver
	 *         could not decide a query
	 */
	Map<IcfgLocation, Set<Term>> check(final Map<IcfgLocation, Set<Term>> known,
			final Map<IcfgLocation, Set<Term>> candidates) {
		final Map<IcfgLocation, Set<Term>> remaining = new LinkedHashMap<>();
		for (final Map.Entry<IcfgLocation, Set<Term>> entry : candidates.entrySet()) {
			if (!hasNode(entry.getKey())) {
				throw new IllegalArgumentException("location " + entry.getKey() + " has no pc node");
			}
			remaining.put(entry.getKey(), new LinkedHashSet<>(entry.getValue()));
		}
		mMgdScript.lock(this);
		try {
			int rounds = 0;
			while (remaining.values().stream().anyMatch(set -> !set.isEmpty())) {
				rounds++;
				final LBool result = checkRound(known, remaining);
				if (result == LBool.UNSAT) {
					mLogger.debug("InvariantSupplier: inductive after %d round(s)", rounds);
					return remaining;
				}
				if (result == LBool.UNKNOWN) {
					return null;
				}
			}
			return remaining;
		} finally {
			mMgdScript.unlock(this);
		}
	}

	/**
	 * One query. If it is satisfiable, removes the candidates the model refutes from {@code remaining}.
	 */
	private LBool checkRound(final Map<IcfgLocation, Set<Term>> known, final Map<IcfgLocation, Set<Term>> remaining) {
		final Script script = mMgdScript.getScript();
		// Everything that declares a constant has to happen before the push, see IndexedConstantVars.
		if (mStep == null) {
			mStep = mSystem.step(0, mConstants, mMgdScript);
		}
		final Term pc0 = mConstants.pc(0);
		final Term pc1 = mConstants.pc(1);
		final List<Term> pre = new ArrayList<>();
		final List<Term> violations = new ArrayList<>();
		// location -> (candidate -> candidate at step 1)
		final Map<IcfgLocation, Map<Term, Term>> atTarget = new HashMap<>();
		for (final Map.Entry<Integer, IcfgLocation> node : mLocationOfNode.entrySet()) {
			final IcfgLocation location = node.getValue();
			final Set<Term> candidates = remaining.getOrDefault(location, Collections.emptySet());
			final List<Term> assumed = new ArrayList<>();
			for (final Term invariant : known.getOrDefault(location, Collections.emptySet())) {
				// Assuming less than is known is sound, and a variable outside the system is unconstrained anyway.
				if (isExpressible(invariant)) {
					assumed.add(instantiate(invariant, 0));
				}
			}
			for (final Term candidate : candidates) {
				assumed.add(instantiate(candidate, 0));
			}
			final Term isNode0 = SmtUtils.binaryEquality(script, pc0, PcTransitionSystem.pcValue(script, node.getKey()));
			if (!assumed.isEmpty()) {
				pre.add(SmtUtils.implies(script, isNode0, SmtUtils.and(script, assumed)));
			}
			final Term isNode1 = SmtUtils.binaryEquality(script, pc1, PcTransitionSystem.pcValue(script, node.getKey()));
			final Map<Term, Term> instantiated = atTarget.computeIfAbsent(location, x -> new LinkedHashMap<>());
			for (final Term candidate : candidates) {
				final Term at1 = instantiated.computeIfAbsent(candidate, c -> instantiate(c, 1));
				violations.add(SmtUtils.and(script, isNode1, SmtUtils.not(script, at1)));
			}
		}

		mMgdScript.push(this, 1);
		try {
			mMgdScript.assertTerm(this, mStep);
			for (final Term term : pre) {
				mMgdScript.assertTerm(this, term);
			}
			mMgdScript.assertTerm(this, SmtUtils.or(script, violations));
			final LBool result = mMgdScript.checkSat(this);
			if (result == LBool.SAT) {
				dropRefuted(remaining, atTarget, pc1);
			}
			return result;
		} finally {
			mMgdScript.pop(this, 1);
		}
	}

	/**
	 * Reads the model of a satisfiable query: the location of step 1 and which of its candidates are false there.
	 */
	private void dropRefuted(final Map<IcfgLocation, Set<Term>> remaining,
			final Map<IcfgLocation, Map<Term, Term>> atTarget, final Term pc1) {
		final Script script = mMgdScript.getScript();
		final Map<Term, Term> pcValue;
		try {
			pcValue = SmtUtils.getValues(script, List.of(pc1));
		} catch (final UnsupportedOperationException e) {
			throw new UnsupportedOperationException("The invariant supplier's solver cannot produce a model, so it "
					+ "cannot tell which candidate invariant is not inductive. It needs a mode that sets "
					+ ":produce-models (e.g. External_ModelsAndUnsatCoreMode, the default).", e);
		}
		final Rational node = SmtUtils.tryToConvertToLiteral(pcValue.get(pc1));
		if (node == null || !node.isIntegral()) {
			throw new AssertionError("the model gives " + pcValue.get(pc1) + " for the pc, not an integer literal");
		}
		final IcfgLocation location = mLocationOfNode.get(node.numerator().intValueExact());
		if (location == null || !atTarget.containsKey(location)) {
			throw new AssertionError("the model violates a candidate at pc " + node + ", which has none");
		}
		final Map<Term, Term> candidates = atTarget.get(location);
		final Map<Term, Term> values = SmtUtils.getValues(script, candidates.values());
		boolean dropped = false;
		for (final Map.Entry<Term, Term> candidate : candidates.entrySet()) {
			if (SmtUtils.isFalseLiteral(values.get(candidate.getValue()))) {
				remaining.get(location).remove(candidate.getKey());
				dropped = true;
			}
		}
		if (!dropped) {
			throw new AssertionError("the model reaches " + location + " with a violated candidate, but gives every "
					+ "candidate there the value true");
		}
	}

	/** {@code term} over the program variables' term variables, as a term over the constants of step {@code idx}. */
	private Term instantiate(final Term term, final int idx) {
		final Map<Term, Term> substitution = new HashMap<>();
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar pv = mVarOfTermVariable.get(tv);
			if (pv == null) {
				throw new IllegalArgumentException(term + " mentions " + tv + ", which is no variable of the system");
			}
			substitution.put(tv, mConstants.var(pv, idx));
		}
		return PureSubstitution.apply(mMgdScript, substitution, term);
	}
}
