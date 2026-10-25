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

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.IndexedConstantVars;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem;

/**
 * Samples reachable states at the loop heads by bounded unrollings of the {@link PcTransitionSystem}: for each head
 * node and each depth {@code d}, a model of
 *
 * <pre>
 *   pc_0 = INIT  and  step(0) and ... and step(d-1)  and  pc_d = head
 * </pre>
 *
 * is a state the program reaches at the head after {@code d} steps from checkpoint to checkpoint. Each model is
 * blocked to get a different state next. Only the integer program variables are read.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
final class ReachableStateSampler {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final PcTransitionSystem<CallNode<IPredicate>> mSystem;
	private final IndexedConstantVars mConstants;
	private final List<IProgramVar> mVars = new ArrayList<>();

	/**
	 * @param constants
	 *            constants for the unrolling, sharing the declared constants with the other queries of the script
	 */
	ReachableStateSampler(final ILogger logger, final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final PcTransitionSystem<CallNode<IPredicate>> system,
			final IndexedConstantVars constants) {
		mLogger = logger;
		mServices = services;
		mMgdScript = mgdScript;
		mSystem = system;
		mConstants = constants;
		for (final IProgramVar pv : system.getVars()) {
			if (SampleCandidates.isSampled(pv.getTermVariable())) {
				mVars.add(pv);
			}
		}
	}

	/**
	 * @param maxDepth
	 *            the largest number of steps
	 * @param perDepth
	 *            how many states are sampled per head node and depth at most
	 * @return how many new points went into {@code store}
	 */
	int sample(final int maxDepth, final int perDepth, final SampleCandidates store) {
		if (mVars.isEmpty() || mSystem.getHeadNodes().isEmpty()) {
			return 0;
		}
		int added = 0;
		mMgdScript.lock(this);
		try {
			final Script script = mMgdScript.getScript();
			// Everything that declares a constant has to happen before the push, see IndexedConstantVars.
			final List<Term> steps = new ArrayList<>();
			for (int j = 0; j < maxDepth; j++) {
				steps.add(mSystem.step(j, mConstants, mMgdScript));
			}
			final Term init = SmtUtils.binaryEquality(script, mConstants.pc(0),
					mSystem.pcValue(script, PcTransitionSystem.INIT));
			for (int depth = 1; depth <= maxDepth; depth++) {
				final List<Term> state = new ArrayList<>();
				for (final IProgramVar pv : mVars) {
					state.add(mConstants.var(pv, depth));
				}
				for (final Map.Entry<CallNode<IPredicate>, Integer> head : mSystem.getHeadNodes().entrySet()) {
					if (!mServices.getProgressMonitorService().continueProcessing()) {
						return added;
					}
					final Outcome outcome = sampleAt(head, depth, steps, init, state, perDepth, store);
					added += outcome.added();
					if (outcome.lastAnswer() == LBool.UNKNOWN) {
						mLogger.info("InvariantSupplier: the solver could not decide a sampling query at depth %d, "
								+ "sampling stops", depth);
						return added;
					}
				}
			}
		} finally {
			mMgdScript.unlock(this);
		}
		return added;
	}

	/**
	 * @param lastAnswer
	 *            the answer of the last query: UNSAT once no other state is left, UNKNOWN if the solver gave up
	 * @param added
	 *            how many new points went into the store
	 */
	private record Outcome(LBool lastAnswer, int added) {
	}

	private Outcome sampleAt(final Map.Entry<CallNode<IPredicate>, Integer> head, final int depth,
			final List<Term> steps, final Term init, final List<Term> state, final int perDepth,
			final SampleCandidates store) {
		final Script script = mMgdScript.getScript();
		int added = 0;
		mMgdScript.push(this, 1);
		try {
			mMgdScript.assertTerm(this, init);
			for (int j = 0; j < depth; j++) {
				mMgdScript.assertTerm(this, steps.get(j));
			}
			mMgdScript.assertTerm(this, SmtUtils.binaryEquality(script, mConstants.pc(depth),
					mSystem.pcValue(script, head.getValue())));
			LBool answer = LBool.UNSAT;
			for (int sample = 0; sample < perDepth; sample++) {
				answer = mMgdScript.checkSat(this);
				if (answer != LBool.SAT) {
					return new Outcome(answer, added);
				}
				final Map<Term, Term> values = SmtUtils.getValues(script, state);
				final Map<TermVariable, Rational> point = new LinkedHashMap<>();
				final List<Term> sameState = new ArrayList<>();
				for (int i = 0; i < mVars.size(); i++) {
					final Term value = values.get(state.get(i));
					final Rational rational = value == null ? null : SmtUtils.tryToConvertToLiteral(value);
					if (rational == null) {
						continue;
					}
					point.put(mVars.get(i).getTermVariable(), rational);
					sameState.add(SmtUtils.binaryEquality(script, state.get(i), value));
				}
				if (store.add(InvariantSupplier.locationOf(head.getKey().getState()), point)) {
					added++;
				}
				if (sameState.isEmpty()) {
					return new Outcome(answer, added);
				}
				mMgdScript.assertTerm(this, SmtUtils.not(script, SmtUtils.and(script, sameState)));
			}
			return new Outcome(answer, added);
		} finally {
			mMgdScript.pop(this, 1);
		}
	}
}
