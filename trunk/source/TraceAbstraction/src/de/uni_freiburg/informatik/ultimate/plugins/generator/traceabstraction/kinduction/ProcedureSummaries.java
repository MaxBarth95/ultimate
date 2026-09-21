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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.LoopTreeFormulaBuilder.Checkpoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.LoopTreeFormulaBuilder.LoopTree;

/**
 * Resolves every procedure call of a nested word automaton into a <b>virtual call edge</b>, so that the
 * entry procedure's {@link LoopTreeFormulaBuilder} graph - and therefore the {@link PcTransitionSystem} built
 * from it - contains no call and no return transition, and no state of any callee.
 * <p>
 * Why this is needed rather than convenient: a flat graph has no call stack. Putting a call and a return into it
 * as ordinary edges makes a callee that is called from two sites look like a <em>loop</em> (site1 -&gt; entry,
 * exit -&gt; after-site1, ... -&gt; site2 -&gt; entry) and admits paths that enter at one call site and return to
 * another, splicing away everything in between. On top of that, a call's transition formula is only the parameter
 * assignment and a return's only the assignment of the result, so the scoping of oldvars, modifiable globals and
 * the callee's locals would be wrong as well.
 *
 * <h2>What is built</h2>
 *
 * Bottom-up along {@link ProcedureCallGraph#getProceduresCalleeFirst()} (which rejects recursion up front), for
 * every procedure reachable through calls from an entry procedure:
 * <ul>
 * <li>a <b>summary edge</b> per call transition and per exit state of the callee: {@code callSite -> post-return
 * state}, with the callee's entry-to-exit formula composed with the call and the return by
 * {@link ProcedureCallGraph#computeVirtualEdge},
 * <li>an <b>error edge</b> per call transition and per error state reachable inside the callee:
 * {@code callSite -> that error state}, with
 * {@link TransFormulaUtils#sequentialCompositionWithPendingCall}. The error state itself becomes a state (and a
 * final state) of the caller's scope, sealed so that its own transitions are not edges there, see
 * {@link LoopTreeFormulaBuilder}'s sealed-state constructor. Error states are carried up this way through any
 * number of levels, so an error deep in the call tree is a FINAL checkpoint of the entry procedure's graph.
 * </ul>
 * Every formula is built for <b>one</b> call transition and <b>one</b> exit resp. error state, never for the
 * union of all of them: the union would let a path that reaches one exit leave through another exit's return
 * transition, which the abstraction does not admit, and k-induction would answer UNSAFE on a path that no
 * counterexample can realise.
 *
 * <h2>What is not supported</h2>
 *
 * A callee whose own graph contains a loop has no single loop-free entry-to-exit formula and therefore no
 * summary. That is refused with an {@link UnsupportedOperationException} naming the procedure, rather than
 * approximated: an under-approximation could prove a program safe that is not.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class ProcedureSummaries<LETTER extends IAction, STATE> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CfgSmtToolkit mCsToolkit;
	private final ManagedScript mMgdScript;
	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;

	private final Map<String, Set<STATE>> mStatesByProcedure;
	private final Map<String, ScopeData> mScopeData = new LinkedHashMap<>();

	private final Set<STATE> mRootScopeStates = new LinkedHashSet<>();
	private final Set<STATE> mRootInitStates = new LinkedHashSet<>();
	private final Set<STATE> mRootFinalStates = new LinkedHashSet<>();
	private final Set<STATE> mRootSealedStates = new LinkedHashSet<>();
	private final Map<STATE, Map<STATE, UnmodifiableTransFormula>> mRootVirtualCallEdges = new LinkedHashMap<>();

	private int mNumBuilds;

	/** Everything one procedure's own checkpoint graph is built from, once its callees are done. */
	private final class ScopeData {
		private final String mProcedure;
		/** The procedure's own states plus the error states imported from its callees. */
		private final Set<STATE> mScopeStates = new LinkedHashSet<>();
		/** The imported error states: dead ends here, reached only through a virtual error edge. */
		private final Set<STATE> mSealed = new LinkedHashSet<>();
		/** This procedure's own accepting states plus the imported ones. */
		private final Set<STATE> mErrorStates = new LinkedHashSet<>();
		private final Map<STATE, Map<STATE, UnmodifiableTransFormula>> mVirtualEdges;

		private ScopeData(final String procedure, final Map<STATE, Map<STATE, UnmodifiableTransFormula>> edges,
				final Set<STATE> imported) {
			mProcedure = procedure;
			mVirtualEdges = edges;
			mScopeStates.addAll(ownStates(procedure));
			mScopeStates.addAll(imported);
			mSealed.addAll(imported);
			mErrorStates.addAll(ProcedureCallGraph.intersect(mAbstraction.getFinalStates(), ownStates(procedure)));
			mErrorStates.addAll(imported);
		}
	}

	public ProcedureSummaries(final IUltimateServiceProvider services, final ILogger logger,
			final CfgSmtToolkit csToolkit, final ManagedScript mgdScript,
			final INestedWordAutomaton<LETTER, STATE> abstraction) {
		mServices = services;
		mLogger = logger;
		mCsToolkit = csToolkit;
		mMgdScript = mgdScript;
		mAbstraction = abstraction;
		mStatesByProcedure = ProcedureCallGraph.groupStatesByProcedure(abstraction.getStates());

		final ProcedureCallGraph callGraph = new ProcedureCallGraph(logger, abstraction);
		final Set<String> entryProcedures = callGraph.getEntryProcedures();
		final Set<String> reachable = callReachable(callGraph, entryProcedures);
		final List<String> order = new ArrayList<>();
		for (final String procedure : callGraph.getProceduresCalleeFirst()) {
			if (reachable.contains(procedure)) {
				order.add(procedure);
			}
		}
		mLogger.info("KInduction: call graph ready, %d of %d procedure(s) reachable, processing order %s",
				order.size(), mStatesByProcedure.size(), order);

		for (final String procedure : order) {
			final Set<STATE> imported = new LinkedHashSet<>();
			final Map<STATE, Map<STATE, UnmodifiableTransFormula>> edges = buildVirtualEdges(procedure, imported);
			mScopeData.put(procedure, new ScopeData(procedure, edges, imported));
		}

		for (final String entry : entryProcedures) {
			final ScopeData data = mScopeData.get(entry);
			if (data == null) {
				throw new AssertionError("entry procedure " + entry + " was not processed");
			}
			mRootScopeStates.addAll(data.mScopeStates);
			mRootSealedStates.addAll(data.mSealed);
			mRootFinalStates.addAll(data.mErrorStates);
			mRootVirtualCallEdges.putAll(data.mVirtualEdges);
		}
		mRootInitStates.addAll(ProcedureCallGraph.intersect(mAbstraction.getInitialStates(), mRootScopeStates));
		mLogger.info(
				"KInduction: resolved %d call site(s) into virtual call edges (%d checkpoint graph(s) built); entry "
						+ "scope has %d state(s), %d error state(s), of which %d inside a callee",
				mRootVirtualCallEdges.size(), mNumBuilds, mRootScopeStates.size(), mRootFinalStates.size(),
				mRootSealedStates.size());
	}

	// ----------------------------------------------------------------------------------------------------------
	// Results, to be handed to LoopTreeFormulaBuilder's scoped constructor
	// ----------------------------------------------------------------------------------------------------------

	/** The entry procedures' states plus every callee error state a virtual error edge points at. */
	public Set<STATE> getScopeStates() {
		return Collections.unmodifiableSet(mRootScopeStates);
	}

	public Set<STATE> getInitStates() {
		return Collections.unmodifiableSet(mRootInitStates);
	}

	/** The entry procedures' own accepting states plus the imported ones, see {@link #getPendingErrorTargets()}. */
	public Set<STATE> getFinalStates() {
		return Collections.unmodifiableSet(mRootFinalStates);
	}

	public Map<STATE, Map<STATE, UnmodifiableTransFormula>> getVirtualCallEdges() {
		return Collections.unmodifiableMap(mRootVirtualCallEdges);
	}

	/**
	 * The error states that lie inside a callee and are reached through a virtual error edge, i.e. with the call
	 * still pending. They are sealed in the entry procedure's graph, and a counterexample that ends in one of them
	 * ends with an unmatched call, see {@link KInductionCounterexampleBuilder}.
	 */
	public Set<STATE> getPendingErrorTargets() {
		return Collections.unmodifiableSet(mRootSealedStates);
	}

	// ----------------------------------------------------------------------------------------------------------
	// Construction
	// ----------------------------------------------------------------------------------------------------------

	private static Set<String> callReachable(final ProcedureCallGraph callGraph, final Set<String> entries) {
		final Set<String> visited = new LinkedHashSet<>(entries);
		final Deque<String> worklist = new ArrayDeque<>(entries);
		while (!worklist.isEmpty()) {
			for (final String callee : callGraph.getCallees(worklist.poll())) {
				if (visited.add(callee)) {
					worklist.add(callee);
				}
			}
		}
		return visited;
	}

	private Set<STATE> ownStates(final String procedure) {
		final Set<STATE> result = mStatesByProcedure.get(procedure);
		if (result == null || result.isEmpty()) {
			throw new UnsupportedOperationException("procedure " + procedure + " is called but the abstraction has "
					+ "no state of it, so its body cannot be summarized");
		}
		return result;
	}

	/**
	 * Every virtual call edge of {@code caller}: one per (call transition, exit state of the callee) pair for the
	 * normal return, and one per (call transition, error state inside the callee) pair for a violation that never
	 * returns. Fills {@code imported} with the error states the edges point at.
	 */
	private Map<STATE, Map<STATE, UnmodifiableTransFormula>> buildVirtualEdges(final String caller,
			final Set<STATE> imported) {
		final Map<STATE, Map<STATE, List<UnmodifiableTransFormula>>> alternatives = new LinkedHashMap<>();
		for (final STATE callSite : ownStates(caller)) {
			for (final OutgoingCallTransition<LETTER, STATE> call : mAbstraction.callSuccessors(callSite)) {
				final ICallAction callAction = asCallAction(call.getLetter());
				final String callee = call.getLetter().getSucceedingProcedure();
				final ScopeData calleeData = mScopeData.get(callee);
				if (calleeData == null) {
					throw new AssertionError("callee " + callee + " of " + caller
							+ " was not processed before its caller, although ProcedureCallGraph ordered them");
				}
				final Set<STATE> entry = Collections.singleton(call.getSucc());
				final Set<STATE> reachable = reachableInScope(calleeData, entry);

				int edges = 0;
				for (final STATE exit : ProcedureCallGraph.computeExitStates(mAbstraction, ownStates(callee),
						Collections.singleton(callSite))) {
					if (!reachable.contains(exit)) {
						continue;
					}
					final UnmodifiableTransFormula summary = formulaBetween(calleeData, entry, exit);
					if (summary == null) {
						continue;
					}
					for (final OutgoingReturnTransition<LETTER, STATE> ret : mAbstraction
							.returnSuccessorsGivenHier(exit, callSite)) {
						final UnmodifiableTransFormula edge = ProcedureCallGraph.computeVirtualEdge(mServices,
								mLogger, mCsToolkit, mMgdScript, callAction, callee, summary,
								asReturnAction(ret.getLetter()).getAssignmentOfReturn());
						addAlternative(alternatives, callSite, ret.getSucc(), edge);
						edges++;
					}
				}
				for (final STATE error : calleeData.mErrorStates) {
					if (!reachable.contains(error)) {
						continue;
					}
					final UnmodifiableTransFormula toError = formulaBetween(calleeData, entry, error);
					if (toError == null) {
						continue;
					}
					addAlternative(alternatives, callSite, error,
							pendingCallToError(caller, callAction, callee, error, toError));
					imported.add(error);
					edges++;
				}
				if (edges == 0) {
					// Legitimate: a call to a procedure that never returns (abort, exit) and contains no reachable
					// error is a dead end. Logged because it silently removes the call site from the graph.
					mLogger.info("KInduction: call %s -> %s at %s has no virtual edge: the callee neither returns "
							+ "nor reaches an error on any path from %s", caller, callee, callSite, call.getSucc());
				}
			}
		}

		final Map<STATE, Map<STATE, UnmodifiableTransFormula>> result = new LinkedHashMap<>();
		for (final Map.Entry<STATE, Map<STATE, List<UnmodifiableTransFormula>>> from : alternatives.entrySet()) {
			final Map<STATE, UnmodifiableTransFormula> combined = new LinkedHashMap<>();
			for (final Map.Entry<STATE, List<UnmodifiableTransFormula>> to : from.getValue().entrySet()) {
				// Several call transitions, exits or returns can join the same pair of states; their union is the
				// edge, exactly as for the alternatives of an ordinary checkpoint edge.
				combined.put(to.getKey(),
						LoopTreeFormulaBuilder.combineAlternatives(mLogger, mServices, mMgdScript, to.getValue()));
			}
			result.put(from.getKey(), combined);
		}
		return result;
	}

	private void addAlternative(final Map<STATE, Map<STATE, List<UnmodifiableTransFormula>>> alternatives,
			final STATE from, final STATE to, final UnmodifiableTransFormula formula) {
		alternatives.computeIfAbsent(from, k -> new LinkedHashMap<>()).computeIfAbsent(to, k -> new ArrayList<>())
				.add(formula);
	}

	/**
	 * The formula of every path through {@code data}'s procedure from {@code inits} to {@code target}, or
	 * {@code null} if there is none. Throws if that procedure's graph has a loop: there is then no single
	 * loop-free formula for it.
	 */
	private UnmodifiableTransFormula formulaBetween(final ScopeData data, final Set<STATE> inits,
			final STATE target) {
		mNumBuilds++;
		final LoopTree<STATE> tree = new LoopTreeFormulaBuilder<>(mServices, mLogger, mMgdScript, mAbstraction,
				data.mScopeStates, inits, Collections.singleton(target), data.mVirtualEdges, data.mSealed).build();
		if (!tree.getLoops().isEmpty()) {
			final List<Set<STATE>> heads = new ArrayList<>();
			for (final LoopTreeFormulaBuilder.Scope<STATE> loop : tree.getLoops()) {
				heads.add(loop.getHeads());
			}
			throw new UnsupportedOperationException("procedure " + data.mProcedure + " contains " + heads.size()
					+ " loop(s) (heads " + heads + "), so there is no single loop-free formula for its body and it "
					+ "cannot be summarized at its call sites. k-induction supports loops only in the procedure it "
					+ "analyses; inline " + data.mProcedure + ", or teach this class to unfold a callee per call "
					+ "site.");
		}
		return tree.getRoot().getEdge(Checkpoint.init(), Checkpoint.fin());
	}

	/**
	 * The formula of a call that never returns because the callee (or something it calls) reaches the error state
	 * {@code error}. The call stays pending, which is what
	 * {@link TransFormulaUtils#sequentialCompositionWithPendingCall} describes; {@code error} may lie deeper than
	 * the direct callee, so the procedure at the end is the one {@code error} belongs to.
	 */
	private UnmodifiableTransFormula pendingCallToError(final String caller, final ICallAction callAction,
			final String callee, final STATE error, final UnmodifiableTransFormula toError) {
		final String procAtEnd = ProcedureCallGraph.procedureOf(error);
		final UnmodifiableTransFormula oldVarsAssignment =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(callee);
		final UnmodifiableTransFormula globalVarsAssignment =
				mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(callee);
		final Set<IProgramNonOldVar> modifiableGlobalsAtEnd =
				mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(procAtEnd);
		return TransFormulaUtils.sequentialCompositionWithPendingCall(mMgdScript, false, false, false,
				Collections.emptyList(), callAction.getLocalVarsAssignment(), oldVarsAssignment, globalVarsAssignment,
				toError, mLogger, mServices, modifiableGlobalsAtEnd, SimplificationTechnique.NONE,
				mCsToolkit.getSymbolTable(), caller, caller, callee, procAtEnd,
				mCsToolkit.getModifiableGlobalsTable());
	}

	/**
	 * The states of {@code data}'s scope reachable from {@code inits} over the same edges
	 * {@link LoopTreeFormulaBuilder} would use (internal transitions and virtual call edges, nothing else). Only
	 * used to skip exit and error states that no path can reach, so that no checkpoint graph is built for them.
	 */
	private Set<STATE> reachableInScope(final ScopeData data, final Set<STATE> inits) {
		final Set<STATE> visited = new LinkedHashSet<>(inits);
		final Deque<STATE> worklist = new ArrayDeque<>(inits);
		while (!worklist.isEmpty()) {
			final STATE state = worklist.poll();
			if (data.mSealed.contains(state)) {
				continue;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(state)) {
				if (data.mScopeStates.contains(t.getSucc()) && visited.add(t.getSucc())) {
					worklist.add(t.getSucc());
				}
			}
			for (final STATE succ : data.mVirtualEdges.getOrDefault(state, Collections.emptyMap()).keySet()) {
				if (visited.add(succ)) {
					worklist.add(succ);
				}
			}
		}
		return visited;
	}

	private static ICallAction asCallAction(final IAction letter) {
		if (!(letter instanceof ICallAction)) {
			throw new UnsupportedOperationException("the call letter " + letter + " is a "
					+ letter.getClass().getSimpleName() + ", not an ICallAction, so it has no local variable "
					+ "assignment and the call cannot be summarized");
		}
		return (ICallAction) letter;
	}

	private static IReturnAction asReturnAction(final IAction letter) {
		if (!(letter instanceof IReturnAction)) {
			throw new UnsupportedOperationException("the return letter " + letter + " is a "
					+ letter.getClass().getSimpleName() + ", not an IReturnAction, so it has no assignment of the "
					+ "return value and the call cannot be summarized");
		}
		return (IReturnAction) letter;
	}
}
