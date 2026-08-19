package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.CheckpointGraphFormulaBuilder.Checkpoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.CheckpointGraphFormulaBuilder.CheckpointGraph;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.InterpolationBasedModelChecking.PathResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.InterpolationBasedModelChecking.PathVerdict;

/**
 * Drives IMC across an entire non-recursive call graph. {@link ProcedureCallGraph} gives the processing order
 * (every callee fully processed - and, if it needs one, already holding a summary - before any of its callers) and
 * rejects recursion up front, since a virtual call edge (see {@link CheckpointGraphFormulaBuilder}'s class javadoc)
 * needs its callee's summary to already exist, which is undefined for a cycle.
 * <p>
 * For each procedure this builds up to two checkpoint graphs, both scoped to that procedure's own states (via
 * {@link CheckpointGraphFormulaBuilder}'s scoped constructor) and both with call sites already resolved into
 * virtual edges pointing at callees' already-computed summaries:
 * <ul>
 * <li>an <b>error graph</b> (FINAL = this procedure's own accepting/error states) - checked exactly like a whole,
 * non-interprocedural program used to be. A bug found here is real regardless of who calls this procedure, so it
 * short-circuits the entire orchestration immediately, without waiting for every procedure to be processed.
 * <li>an <b>exit graph</b> (FINAL = this procedure's own normal-return states - states with an outgoing return
 * transition to one of this procedure's known callers), for every procedure that isn't an entry procedure. Every
 * SAFE path's already-proven region chain (see {@link PathResult#provenRegionChain}) is composed into that path's
 * effect and all such paths are disjoined into this procedure's summary, which becomes the virtual edge at every
 * call site targeting it once its callers are processed.
 * </ul>
 * An {@code UNKNOWN} exit path's contribution is simply dropped from the summary (documented at the call site
 * below) rather than treated as an error - this can only make a summary an under-approximation of the real
 * procedure, never an over-approximation, so it can turn a discoverable {@code UNSAFE} in a caller into
 * {@code UNKNOWN} but can never turn a real bug into a false {@code SAFE}.
 */
final class InterproceduralImcOrchestrator<LETTER extends IAction, STATE> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CfgSmtToolkit mCsToolkit;
	private final ManagedScript mWorkerMgdScript;
	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final PathChecker<STATE> mPathChecker;

	@FunctionalInterface
	interface PathChecker<STATE> {
		PathResult check(CheckpointGraph<STATE> graph, List<Checkpoint<STATE>> path);
	}

	InterproceduralImcOrchestrator(final IUltimateServiceProvider services, final ILogger logger,
			final CfgSmtToolkit csToolkit, final ManagedScript workerMgdScript,
			final INestedWordAutomaton<LETTER, STATE> abstraction, final PathChecker<STATE> pathChecker) {
		mServices = services;
		mLogger = logger;
		mCsToolkit = csToolkit;
		mWorkerMgdScript = workerMgdScript;
		mAbstraction = abstraction;
		mPathChecker = pathChecker;
	}

	PathVerdict run() throws AutomataLibraryException {
		final ProcedureCallGraph callGraph = new ProcedureCallGraph(mLogger, mAbstraction);
		final List<String> proceduresCalleeFirst = callGraph.getProceduresCalleeFirst();
		mLogger.info("IMC: call graph ready, %d procedure(s), processing order %s", proceduresCalleeFirst.size(),
				proceduresCalleeFirst);

		final Map<String, Set<STATE>> statesByProcedure = groupStatesByProcedure();
		final Map<String, Set<STATE>> callTargetsByProcedure = new HashMap<>();
		final Map<String, Set<STATE>> callSitesByCallee = new HashMap<>();
		for (final STATE state : mAbstraction.getStates()) {
			for (final OutgoingCallTransition<LETTER, STATE> t : mAbstraction.callSuccessors(state)) {
				final String callee = t.getLetter().getSucceedingProcedure();
				callTargetsByProcedure.computeIfAbsent(callee, k -> new HashSet<>()).add(t.getSucc());
				callSitesByCallee.computeIfAbsent(callee, k -> new HashSet<>()).add(state);
			}
		}

		final Map<String, UnmodifiableTransFormula> summaries = new HashMap<>();
		boolean unknown = false;

		for (final String procedure : proceduresCalleeFirst) {
			final Set<STATE> scopeStates = statesByProcedure.getOrDefault(procedure, Set.of());
			final boolean isEntry = callGraph.getEntryProcedures().contains(procedure);
			final Set<STATE> initStates =
					isEntry ? intersect(mAbstraction.getInitialStates(), scopeStates)
							: callTargetsByProcedure.getOrDefault(procedure, Set.of());
			final Map<STATE, Map<STATE, UnmodifiableTransFormula>> virtualCallEdges =
					buildVirtualCallEdges(scopeStates, statesByProcedure, summaries);

			mLogger.info("IMC: checking procedure %s (%d state(s), entry=%s)", procedure, scopeStates.size(), isEntry);

			final Set<STATE> errorStates = intersect(mAbstraction.getFinalStates(), scopeStates);
			final CheckpointGraph<STATE> errorGraph = new CheckpointGraphFormulaBuilder<LETTER, STATE>(mServices,
					mLogger, mWorkerMgdScript, mAbstraction, scopeStates, initStates, errorStates, virtualCallEdges)
							.build();
			final PathVerdict errorVerdict = checkAllPaths(errorGraph, null);
			if (errorVerdict == PathVerdict.UNSAFE) {
				return PathVerdict.UNSAFE;
			}
			if (errorVerdict == PathVerdict.UNKNOWN) {
				unknown = true;
			}

			if (isEntry) {
				// Nothing calls an entry procedure, so it never needs a summary.
				continue;
			}

			final Set<STATE> exitStates =
					computeExitStates(scopeStates, callSitesByCallee.getOrDefault(procedure, Set.of()));
			final CheckpointGraph<STATE> exitGraph = new CheckpointGraphFormulaBuilder<LETTER, STATE>(mServices,
					mLogger, mWorkerMgdScript, mAbstraction, scopeStates, initStates, exitStates, virtualCallEdges)
							.build();
			final List<List<UnmodifiableTransFormula>> safeChains = new ArrayList<>();
			final PathVerdict exitVerdict = checkAllPaths(exitGraph, safeChains);
			if (exitVerdict == PathVerdict.UNSAFE) {
				return PathVerdict.UNSAFE;
			}
			if (exitVerdict == PathVerdict.UNKNOWN) {
				// An UNKNOWN exit path's contribution is simply dropped, not an error: this can only make the
				// summary an under-approximation of the real procedure (never an over-approximation), so at worst
				// a caller's own search misses a bug reachable only via that specific return - but `unknown` is
				// already latched here, so the overall result can never come back SAFE when that happens. See the
				// class javadoc.
				unknown = true;
			}

			final List<UnmodifiableTransFormula> perPathEffects = new ArrayList<>();
			for (final List<UnmodifiableTransFormula> chain : safeChains) {
				perPathEffects.add(TransFormulaUtils.sequentialComposition(mLogger, mServices, mWorkerMgdScript, false,
						false, false, SimplificationTechnique.NONE, chain));
			}
			final UnmodifiableTransFormula summary =
					CheckpointGraphFormulaBuilder.combineAlternatives(mLogger, mServices, mWorkerMgdScript, perPathEffects);
			if (summary != null) {
				summaries.put(procedure, summary);
			}
			mLogger.info("IMC: procedure %s summary %s", procedure, summary == null ? "none (no proven-safe exit path)"
					: "built from " + safeChains.size() + " proven-safe path(s)");
		}
		return unknown ? PathVerdict.UNKNOWN : PathVerdict.SAFE;
	}

	/**
	 * Checks every INIT-to-FINAL path of {@code graph} via {@link #mPathChecker}. {@code UNSAFE} on any path
	 * short-circuits immediately (mirrors {@link InterpolationBasedModelChecking}'s original whole-program loop).
	 * If {@code collectSafeChainsInto} is non-null, every {@code SAFE} path's proven region chain is appended to it
	 * (used to build a procedure's exit summary); pass {@code null} when the caller only cares about the verdict
	 * (the error-graph case, where no summary is being built).
	 */
	private PathVerdict checkAllPaths(final CheckpointGraph<STATE> graph,
			final List<List<UnmodifiableTransFormula>> collectSafeChainsInto) {
		boolean unsafe = false;
		boolean unknown = false;
		for (final List<Checkpoint<STATE>> path : graph.enumeratePaths()) {
			mLogger.info("IMC: checking path %s", path);
			final PathResult result = mPathChecker.check(graph, path);
			mLogger.info("IMC: path %s - verdict %s", path, result.verdict);
			if (result.verdict == PathVerdict.UNSAFE) {
				unsafe = true;
				break;
			}
			if (result.verdict == PathVerdict.UNKNOWN) {
				unknown = true;
				continue;
			}
			if (collectSafeChainsInto != null) {
				collectSafeChainsInto.add(result.provenRegionChain);
			}
		}
		if (unsafe) {
			return PathVerdict.UNSAFE;
		}
		return unknown ? PathVerdict.UNKNOWN : PathVerdict.SAFE;
	}

	/**
	 * One virtual call edge per call site in {@code callerScope} whose callee already has a summary (callees
	 * without one - not yet processed, impossible once {@link ProcedureCallGraph} has run, or with no proven-safe
	 * exit path - simply contribute no edge, the same "no edge" semantics
	 * {@link CheckpointGraphFormulaBuilder#computeEdge} already uses everywhere else). Built via
	 * {@link TransFormulaUtils#sequentialCompositionWithCallAndReturn}, the same primitive already used elsewhere
	 * in this codebase (e.g. {@code IcfgEdgeBuilder}) for exactly this call-TF/oldvars/globals/procedure-TF/return-TF
	 * composition.
	 */
	private Map<STATE, Map<STATE, UnmodifiableTransFormula>> buildVirtualCallEdges(final Set<STATE> callerScope,
			final Map<String, Set<STATE>> statesByProcedure, final Map<String, UnmodifiableTransFormula> summaries) {
		final Map<STATE, Map<STATE, UnmodifiableTransFormula>> result = new HashMap<>();
		for (final STATE callSite : callerScope) {
			for (final OutgoingCallTransition<LETTER, STATE> callTrans : mAbstraction.callSuccessors(callSite)) {
				final String callee = callTrans.getLetter().getSucceedingProcedure();
				final UnmodifiableTransFormula calleeSummary = summaries.get(callee);
				if (calleeSummary == null) {
					continue;
				}
				final ICallAction callAction = (ICallAction) callTrans.getLetter();
				for (final STATE calleeState : statesByProcedure.getOrDefault(callee, Set.of())) {
					for (final OutgoingReturnTransition<LETTER, STATE> returnTrans : mAbstraction
							.returnSuccessorsGivenHier(calleeState, callSite)) {
						final IReturnAction returnAction = (IReturnAction) returnTrans.getLetter();
						final UnmodifiableTransFormula virtualEdge = computeVirtualEdge(callAction, callee,
								calleeSummary, returnAction.getAssignmentOfReturn());
						final Map<STATE, UnmodifiableTransFormula> fromHere =
								result.computeIfAbsent(callSite, k -> new HashMap<>());
						final UnmodifiableTransFormula existing = fromHere.putIfAbsent(returnTrans.getSucc(), virtualEdge);
						assert existing == null || existing.equals(virtualEdge) : "Inconsistent return TransFormula "
								+ "for the same call/post-call pair at call site " + callSite;
					}
				}
			}
		}
		return result;
	}

	private UnmodifiableTransFormula computeVirtualEdge(final ICallAction callAction, final String callee,
			final UnmodifiableTransFormula calleeSummary, final UnmodifiableTransFormula returnTf) {
		final UnmodifiableTransFormula oldVarsAssignment =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(callee);
		final UnmodifiableTransFormula globalVarsAssignment =
				mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(callee);
		final Set<IProgramNonOldVar> modifiableGlobals = mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(callee);
		return TransFormulaUtils.sequentialCompositionWithCallAndReturn(mWorkerMgdScript, false, false, false,
				callAction.getLocalVarsAssignment(), oldVarsAssignment, globalVarsAssignment, calleeSummary, returnTf,
				mLogger, mServices, SimplificationTechnique.NONE, mCsToolkit.getSymbolTable(), modifiableGlobals);
	}

	/**
	 * States in {@code scopeStates} with an outgoing return transition to at least one of {@code callSites} - a
	 * procedure's own normal-return points, call-site-agnostic (reused as the FINAL set for every caller's virtual
	 * edge into this procedure). {@code callSites} is every call site anywhere in the automaton that is known (from
	 * {@link ProcedureCallGraph}) to call this procedure, so this is sound and complete without needing to query the
	 * automaton for "any return transition regardless of hier", which its API does not expose directly.
	 */
	private Set<STATE> computeExitStates(final Set<STATE> scopeStates, final Set<STATE> callSites) {
		final Set<STATE> result = new HashSet<>();
		for (final STATE state : scopeStates) {
			for (final STATE callSite : callSites) {
				if (mAbstraction.returnSuccessorsGivenHier(state, callSite).iterator().hasNext()) {
					result.add(state);
					break;
				}
			}
		}
		return result;
	}

	private Map<String, Set<STATE>> groupStatesByProcedure() {
		final Map<String, Set<STATE>> result = new HashMap<>();
		for (final STATE state : mAbstraction.getStates()) {
			result.computeIfAbsent(ProcedureCallGraph.procedureOf(state), k -> new HashSet<>()).add(state);
		}
		return result;
	}

	private static <STATE> Set<STATE> intersect(final Iterable<STATE> a, final Set<STATE> b) {
		final Set<STATE> result = new HashSet<>();
		for (final STATE s : a) {
			if (b.contains(s)) {
				result.add(s);
			}
		}
		return result;
	}
}
