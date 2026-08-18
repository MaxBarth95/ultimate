/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.CheckpointGraphFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.CheckpointGraphFormulaBuilder.Checkpoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.CheckpointGraphFormulaBuilder.CheckpointGraph;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

/**
 * Bounded k-induction on a nested word automaton (path program or abstraction) that represents a program with any
 * number of non-nested loops. Reuses the same {@link CheckpointGraphFormulaBuilder} checkpoint graph
 * {@link de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.InterpolationBasedModelChecking
 * IMC} is built on (program entry / every loop head / accepting-or-error states, connected by all-loop-free-paths
 * edge formulas, plus one loop-body formula per loop head), and the same per-path/per-loop-head phase structure
 * ({@link #runPath}): earlier loop heads on a path are frozen at whatever iteration count their own phase proved
 * inductive, later loop heads are taken exactly one mandatory pass.
 * <p>
 * Unlike IMC, k-induction never needs an interpolating solver - only plain SAT/UNSAT checks - so this class
 * operates directly on the worker's own {@link ManagedScript} (no second, dedicated "interpolation" script), and is
 * consequently not restricted to an SMTInterpol-backed solver mode the way IMC is.
 * <p>
 * For each loop head on a path, at increasing {@code k = 1..MAX_K}, two independent checks are made:
 * <ul>
 * <li><b>Base case</b>: is a violation reachable within {@code k} concrete iterations from the (possibly already
 * partially fixed) path prefix? A SAT result here is a genuine, concrete witness - unconditionally sound
 * {@code UNSAFE}, exactly as in IMC.
 * <li><b>Step case</b> ({@link #checkStepCase}): starting from a free, unconstrained loop-head state (not tied to
 * any prefix), is "no violation" inductive after {@code k} iterations? An UNSAT result here, combined with the base
 * case's UNSAT for the same {@code k}, proves the loop head safe for <em>all</em> iteration counts.
 * </ul>
 * As with IMC, a per-path {@code SAFE} verdict is a bounded/heuristic argument (it does not prove safety for
 * arbitrary joint iteration counts across multiple loop heads on the same path simultaneously), while an
 * {@code UNSAFE} verdict is unconditionally sound.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class KInduction<LETTER extends IAction, STATE> {

	/**
	 * Upper bound on how many times the loop body is unwound while searching for an inductive step. Placeholder
	 * constant, matching {@code InterpolationBasedModelChecking}; not yet wired through a preference.
	 */
	private static final int MAX_K = 200000;

	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final ManagedScript mWorkerMgdScript;
	private final KILock mKILock = new KILock();

	// TODO: on SAT, a concrete witness path is not yet extracted; left unset. See run(). Same gap as IMC's own
	// mCounterexample.
	NestedRun<LETTER, STATE> mCounterexample;

	private final CfgSmtToolkit mCsToolkit;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private boolean mSolverReturnedUnknown;
	private boolean mSafe;

	// Mirrors IMC's own worker-thread integration parameters, kept for structural consistency between the two
	// algorithms (and as a hook for future preference-driven configuration, e.g. bounding MAX_K); not otherwise
	// used, since k-induction needs no dedicated solver-mode selection.
	TaCheckAndRefinementPreferences<?> mPrefs;
	TaskIdentifier mTaskIdentifier;
	private final KInductionWorkerThread<?, ?> mKInductionWorkerThread;
	private final TAPreferences mPref;

	private final IInvariantSupplier<STATE> mInvariantSupplier;

	// Shared indexed-constant cache, reused across every push/pop-bracketed SAT query this instance ever issues -
	// safe because scopes are always cleanly popped between queries, matching IMC's own mIndexedConstantsWorkerScript.
	private final Map<String, Term> mIndexedConstantsWorkerScript = new HashMap<>();

	public KInduction(final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences<?> prefs, final CfgSmtToolkit csToolkit,
			final INestedWordAutomaton<LETTER, STATE> abstraction, final TaskIdentifier taskIdentifier,
			final KInductionWorkerThread<?, ?> kInductionWorkerThread, final TAPreferences preferences,
			final IInvariantSupplier<STATE> invariantSupplier) throws AutomataLibraryException, InterruptedException {
		mAbstraction = abstraction;
		mCsToolkit = csToolkit;
		mWorkerMgdScript = csToolkit.getManagedScript();
		mLogger = logger;
		mServices = services;
		mTaskIdentifier = taskIdentifier;
		mPrefs = prefs;
		mKInductionWorkerThread = kInductionWorkerThread;
		mPref = preferences;
		mInvariantSupplier = invariantSupplier;
		run();
	}

	/**
	 * Result of checking one INIT-to-FINAL path through the checkpoint graph (see {@link #runPath}).
	 */
	private enum PathVerdict {
		SAFE, UNSAFE, UNKNOWN
	}

	private void run() throws AutomataLibraryException {
		mWorkerMgdScript.lock(mKILock);
		mLogger.info("KInduction: starting k-induction (MAX_K=%d)", MAX_K);

		final CheckpointGraph<STATE> graph =
				new CheckpointGraphFormulaBuilder<>(mServices, mLogger, mWorkerMgdScript, mAbstraction).build();
		final List<List<Checkpoint<STATE>>> paths = graph.enumeratePaths();
		mLogger.info("KInduction: checkpoint graph ready (%d loop head(s)), %d path(s) to check",
				graph.getLoopHeads().size(), paths.size());

		boolean unsafe = false;
		boolean unknown = false;
		for (final List<Checkpoint<STATE>> path : paths) {
			mLogger.info("KInduction: checking path %s", path);
			final PathVerdict verdict = runPath(graph, path);
			mLogger.info("KInduction: path %s - verdict %s", path, verdict);
			if (verdict == PathVerdict.UNSAFE) {
				unsafe = true;
				break;
			}
			if (verdict == PathVerdict.UNKNOWN) {
				unknown = true;
			}
		}

		mSafe = !unsafe && !unknown;
		mSolverReturnedUnknown = !unsafe && unknown;

		mWorkerMgdScript.unlock(mKILock);
		mLogger.info("is safe " + (mSafe && !mSolverReturnedUnknown));
		mLogger.info("solver returned unknown: " + mSolverReturnedUnknown);
	}

	/**
	 * Checks one INIT-to-FINAL path through the checkpoint graph. If the path has no loop head at all, this is a
	 * single plain SAT check on its one edge formula. Otherwise the loop heads on the path are processed in order,
	 * one phase per loop head: phase {@code p} sweeps {@code k = 1..MAX_K} for loop head {@code p}, with every
	 * earlier loop head on the path frozen at its own stabilized iteration count ({@code frozenPrefix}, grown across
	 * phases) and every later loop head on the path taken exactly one mandatory pass ({@link #buildTail}) - the same
	 * phase structure {@code InterpolationBasedModelChecking} uses, just validated by base/step SAT checks
	 * ({@link #checkStepCase}) instead of interpolant-sequence stabilization.
	 */
	private PathVerdict runPath(final CheckpointGraph<STATE> graph, final List<Checkpoint<STATE>> path) {
		final List<STATE> loopHeadsOnPath = new ArrayList<>();
		for (final Checkpoint<STATE> checkpoint : path) {
			if (checkpoint.isLoopHead()) {
				loopHeadsOnPath.add(checkpoint.getLoopHead());
			}
		}

		if (loopHeadsOnPath.isEmpty()) {
			final List<UnmodifiableTransFormula> regions = List.of(graph.getEdge(Checkpoint.init(), Checkpoint.fin()));
			mWorkerMgdScript.push(mKILock, 1);
			assertRegionSequence(regions, 0);
			final LBool sat = mWorkerMgdScript.checkSat(mKILock);
			mWorkerMgdScript.pop(mKILock, 1);
			if (sat == LBool.SAT) {
				return PathVerdict.UNSAFE;
			}
			return sat == LBool.UNKNOWN ? PathVerdict.UNKNOWN : PathVerdict.SAFE;
		}

		final List<UnmodifiableTransFormula> frozenPrefix = new ArrayList<>();
		frozenPrefix.add(graph.getEdge(Checkpoint.init(), Checkpoint.loopHead(loopHeadsOnPath.get(0))));

		for (int p = 0; p < loopHeadsOnPath.size(); p++) {
			final STATE loopHead = loopHeadsOnPath.get(p);
			final List<UnmodifiableTransFormula> tail = buildTail(graph, loopHeadsOnPath, p);
			final UnmodifiableTransFormula loopBody = graph.getLoopBody(loopHead);

			boolean inductive = false;
			for (int k = 1; k <= MAX_K; k++) {
				final List<UnmodifiableTransFormula> baseRegions = new ArrayList<>(frozenPrefix);
				baseRegions.addAll(Collections.nCopies(k, loopBody));
				baseRegions.addAll(tail);

				mWorkerMgdScript.push(mKILock, 1);
				assertRegionSequence(baseRegions, 0);
				final LBool baseSat = mWorkerMgdScript.checkSat(mKILock);
				mWorkerMgdScript.pop(mKILock, 1);
				mLogger.info("KInduction: path %s, loop head %s, k=%d - base case: %s", path, loopHead, k, baseSat);

				if (baseSat == LBool.SAT) {
					return PathVerdict.UNSAFE;
				}
				if (baseSat == LBool.UNKNOWN) {
					return PathVerdict.UNKNOWN;
				}

				final LBool stepSat = checkStepCase(loopHead, loopBody, tail, k);
				mLogger.info("KInduction: path %s, loop head %s, k=%d - step case: %s", path, loopHead, k, stepSat);

				if (stepSat == LBool.UNKNOWN) {
					return PathVerdict.UNKNOWN;
				}
				if (stepSat == LBool.UNSAT) {
					frozenPrefix.addAll(Collections.nCopies(k, loopBody));
					final Checkpoint<STATE> next =
							p + 1 < loopHeadsOnPath.size() ? Checkpoint.loopHead(loopHeadsOnPath.get(p + 1))
									: Checkpoint.fin();
					frozenPrefix.add(graph.getEdge(Checkpoint.loopHead(loopHead), next));
					inductive = true;
					break;
				}
				// stepSat == SAT: not yet inductive at this k, grow k and retry both checks.
			}
			if (!inductive) {
				mLogger.info("KInduction: path %s, loop head %s - reached MAX_K=%d without an inductive step", path,
						loopHead, MAX_K);
				return PathVerdict.UNKNOWN;
			}
		}
		return PathVerdict.SAFE;
	}

	/**
	 * The fixed continuation of {@code path} after phase {@code phaseIndex}'s loop head: one mandatory pass through
	 * every later loop head on the path, followed by the edge into FINAL. Identical in shape to
	 * {@code InterpolationBasedModelChecking#buildTail}.
	 */
	private List<UnmodifiableTransFormula> buildTail(final CheckpointGraph<STATE> graph,
			final List<STATE> loopHeadsOnPath, final int phaseIndex) {
		final List<UnmodifiableTransFormula> tail = new ArrayList<>();
		STATE current = loopHeadsOnPath.get(phaseIndex);
		for (int q = phaseIndex + 1; q < loopHeadsOnPath.size(); q++) {
			final STATE next = loopHeadsOnPath.get(q);
			tail.add(graph.getEdge(Checkpoint.loopHead(current), Checkpoint.loopHead(next)));
			tail.add(graph.getLoopBody(next));
			current = next;
		}
		tail.add(graph.getEdge(Checkpoint.loopHead(current), Checkpoint.fin()));
		return tail;
	}

	/**
	 * Checks whether "no violation reachable" is inductive at {@code k} for {@code loopHead}: starting from a free,
	 * unconstrained loop-head state at index {@code 0} (deliberately not tied to {@code init}, unlike the base
	 * case's concrete {@code frozenPrefix}), {@code k} copies of {@code loopBody} are chained, asserting at each of
	 * the {@code k} resulting intermediate loop-head states ({@code assertNoViolationHypothesis}) that {@code tail}
	 * - the mandatory continuation to FINAL, composed into one relation via
	 * {@link TransFormulaUtils#sequentialComposition} - is not satisfiable from there. "Not satisfiable from a free
	 * state" cannot be expressed as a plain conjunct the way the base case's fully concrete chain can (there is no
	 * single witness value for {@code tail}'s own out/aux vars that works for every model of the free state), so it
	 * is asserted as an explicit universal quantifier over exactly those variables. One further copy of
	 * {@code loopBody} is then chained and {@code tail} is asserted existentially - exactly like the base case's own
	 * final region - from the resulting {@code (k+1)}th state.
	 * <p>
	 * If {@link #mInvariantSupplier} has an invariant for {@code loopHead}, it is asserted as an extra hypothesis at
	 * every one of the {@code k+1} loop-head states (indices {@code 0..k}): sound because a real invariant already
	 * over-approximates everything reachable at {@code loopHead}, so assuming it without re-proving it can only
	 * prune this search, never introduce unsoundness.
	 *
	 * @return {@link LBool#UNSAT} if the step is inductive at {@code k}; {@link LBool#SAT} if not yet inductive at
	 *         this {@code k} (try a larger {@code k}); {@link LBool#UNKNOWN} if the solver gave up.
	 */
	private LBool checkStepCase(final STATE loopHead, final UnmodifiableTransFormula loopBody,
			final List<UnmodifiableTransFormula> tail, final int k) {
		final UnmodifiableTransFormula tailRelation = tail.size() == 1 ? tail.get(0)
				: TransFormulaUtils.sequentialComposition(mLogger, mServices, mWorkerMgdScript, false, false, false,
						SimplificationTechnique.NONE, tail);

		mWorkerMgdScript.push(mKILock, 1);

		assertInvariantHypothesis(loopHead, loopBody, 0);
		for (int j = 1; j <= k; j++) {
			assertRegionIndexed(loopBody, j - 1, j);
			assertInvariantHypothesis(loopHead, loopBody, j);
			assertNoViolationHypothesis(tailRelation, j);
		}
		assertRegionIndexed(loopBody, k, k + 1);
		assertRegionIndexed(tailRelation, k + 1, k + 2);

		final LBool result = mWorkerMgdScript.checkSat(mKILock);
		mWorkerMgdScript.pop(mKILock, 1);
		return result;
	}

	/**
	 * Asserts {@code region}[{@code idxInVar} -> {@code idxOutVar}] via the same
	 * {@link PredicateUtils#formulaWithIndexedVars} SSA-indexing machinery
	 * {@code InterpolationBasedModelChecking#assertRegionSequenceNamed} uses (indexing both in- and out-vars via a
	 * shared indexed-constant cache, so consecutive regions' matching vars land on the same constant automatically),
	 * minus the {@code :named} partitioning IMC needs for interpolation - k-induction never interpolates.
	 */
	private void assertRegionIndexed(final UnmodifiableTransFormula region, final int idxInVar, final int idxOutVar) {
		final Set<IProgramVar> assignedVars = new HashSet<>();
		final Term ssaFormula = PredicateUtils.formulaWithIndexedVars(region, idxInVar, idxOutVar, assignedVars,
				mIndexedConstantsWorkerScript, mWorkerMgdScript.getScript());
		mWorkerMgdScript.assertTerm(mKILock, ssaFormula);
	}

	private void assertRegionSequence(final List<UnmodifiableTransFormula> regions, final int startIndex) {
		for (int s = 0; s < regions.size(); s++) {
			assertRegionIndexed(regions.get(s), startIndex + s, startIndex + s + 1);
		}
	}

	/**
	 * Asserts {@code forall (tail's own out/aux vars). !tail[inVars := index idx]} - "no violation is reachable from
	 * the loop-head state at index {@code idx}." Only {@code tailRelation}'s inVars are substituted (to indexed
	 * constants, tying it into the chain); its out/aux vars are left as their original {@link TermVariable}s so they
	 * can be universally bound directly, mirroring exactly which vars {@code tailRelation} itself existentially
	 * quantifies when asserted normally (see {@link #assertRegionIndexed}).
	 */
	private void assertNoViolationHypothesis(final UnmodifiableTransFormula tailRelation, final int idx) {
		final Map<Term, Term> substitution = new HashMap<>();
		for (final IProgramVar pv : tailRelation.getInVars().keySet()) {
			final Term constant = pv.isOldvar() ? pv.getDefaultConstant() : PredicateUtils.getIndexedConstant(pv, idx,
					mIndexedConstantsWorkerScript, mWorkerMgdScript.getScript());
			substitution.put(tailRelation.getInVars().get(pv), constant);
		}
		final Term instantiated = PureSubstitution.apply(mWorkerMgdScript, substitution, tailRelation.getFormula());

		final Set<TermVariable> toQuantify = new HashSet<>(tailRelation.getOutVars().values());
		toQuantify.addAll(tailRelation.getAuxVars());
		final Term negation = SmtUtils.not(mWorkerMgdScript.getScript(), instantiated);
		final Term noViolation = toQuantify.isEmpty() ? negation
				: SmtUtils.quantifier(mWorkerMgdScript.getScript(), QuantifiedFormula.FORALL, toQuantify, negation);
		mWorkerMgdScript.assertTerm(mKILock, noViolation);
	}

	/**
	 * Asserts {@link #mInvariantSupplier}'s invariant for {@code loopHead} (if any), instantiated at index
	 * {@code idx} by substituting each of {@code loopBody}'s own inVars - i.e. {@code loopHead}'s live variables -
	 * from its {@link IProgramVar#getTermVariable()} form (the convention {@link IInvariantSupplier} documents) to
	 * the matching indexed constant.
	 */
	private void assertInvariantHypothesis(final STATE loopHead, final UnmodifiableTransFormula loopBody,
			final int idx) {
		final Optional<Term> invariant = mInvariantSupplier.getInvariant(loopHead, mWorkerMgdScript);
		if (invariant.isEmpty()) {
			return;
		}
		final Map<Term, Term> substitution = new HashMap<>();
		for (final IProgramVar pv : loopBody.getInVars().keySet()) {
			final Term constant = pv.isOldvar() ? pv.getDefaultConstant() : PredicateUtils.getIndexedConstant(pv, idx,
					mIndexedConstantsWorkerScript, mWorkerMgdScript.getScript());
			substitution.put(pv.getTermVariable(), constant);
		}
		mWorkerMgdScript.assertTerm(mKILock, PureSubstitution.apply(mWorkerMgdScript, substitution, invariant.get()));
	}

	public boolean isSafe() {
		return mSafe;
	}

	public boolean wasOverapproximated() {
		return mSolverReturnedUnknown;
	}

	public boolean wasUnkown() {
		return mSolverReturnedUnknown;
	}

	public NestedRun<LETTER, STATE> getCounterexample() {
		assert !mSafe;
		return mCounterexample;
	}

	/**
	 * Package private class used by KInduction to lock the {@link ManagedScript}.
	 */
	static class KILock {
	}
}
