package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Builds the procedure call graph of a nested word automaton (nodes = procedure names, edges = "caller calls
 * callee", derived from the automaton's call transitions) and rejects recursion up front:
 * {@link #getProceduresCalleeFirst()} throws {@link UnsupportedOperationException} if any procedure is
 * (transitively, possibly mutually) reachable from itself via a call, naming the offending call and the full
 * cycle - mirroring {@link LoopTreeFormulaBuilder}'s existing non-nesting-loop check, which fails the same way
 * before any formula-building starts. This is not merely a scope limitation: {@link LoopTreeFormulaBuilder}'s
 * virtual call edges (see its class javadoc) need their callee's summary to already exist as a finished formula,
 * which is undefined for a cycle in the call graph.
 * <p>
 * On a non-recursive call graph, {@link #getProceduresCalleeFirst()} also gives the processing order every
 * interprocedural consumer needs: every callee fully processed (and thus already holding a summary, if it needs
 * one) before any of its callers. Both {@code InterproceduralImcOrchestrator} and {@link ProcedureSummaries} use
 * it that way, which is also why the small per-procedure helpers they share (state grouping, exit states, the
 * call/summary/return composition) live here rather than in one of them.
 */
public final class ProcedureCallGraph {

	private final ILogger mLogger;
	private final Set<String> mProcedures = new LinkedHashSet<>();
	private final Set<String> mEntryProcedures = new LinkedHashSet<>();
	private final HashRelation<String, String> mCalls = new HashRelation<>();

	public <LETTER extends IAction, STATE> ProcedureCallGraph(final ILogger logger,
			final INestedWordAutomaton<LETTER, STATE> abstraction) {
		mLogger = logger;
		for (final STATE state : abstraction.getStates()) {
			mProcedures.add(procedureOf(state));
		}
		for (final STATE init : abstraction.getInitialStates()) {
			mEntryProcedures.add(procedureOf(init));
		}
		for (final STATE state : abstraction.getStates()) {
			for (final OutgoingCallTransition<LETTER, STATE> t : abstraction.callSuccessors(state)) {
				mCalls.addPair(t.getLetter().getPrecedingProcedure(), t.getLetter().getSucceedingProcedure());
			}
		}
	}

	/**
	 * The procedure a state belongs to. Only an {@link ISLPredicate} names a program point and therefore a
	 * procedure; anything else is refused here rather than further down as a {@link ClassCastException}.
	 */
	public static <STATE> String procedureOf(final STATE state) {
		if (!(state instanceof ISLPredicate)) {
			throw new UnsupportedOperationException("abstraction state " + state + " is a "
					+ state.getClass().getSimpleName() + ", not an ISLPredicate, so it has no program point and no "
					+ "procedure; an interprocedural analysis cannot scope it");
		}
		return ((ISLPredicate) state).getProgramPoint().getProcedure();
	}

	public Set<String> getEntryProcedures() {
		return mEntryProcedures;
	}

	/** Every procedure that {@code caller} calls directly. */
	public Set<String> getCallees(final String caller) {
		return mCalls.getImage(caller);
	}

	/**
	 * Every procedure, in an order where every callee occurs before every one of its callers. Throws if the call
	 * graph is recursive (a procedure transitively/mutually calls itself) - checked here, up front, before any
	 * checkpoint graph is built.
	 */
	public List<String> getProceduresCalleeFirst() {
		final DefaultSccComputation<String> sccComputation = new DefaultSccComputation<>(mLogger,
				node -> mCalls.getImage(node).iterator(), mProcedures.size(), mProcedures);

		for (final StronglyConnectedComponent<String> ball : sccComputation.getBalls()) {
			final Set<String> cycle = ball.getNodes();
			String caller = null;
			String callee = null;
			outer: for (final String c : cycle) {
				for (final String d : mCalls.getImage(c)) {
					if (cycle.contains(d)) {
						caller = c;
						callee = d;
						break outer;
					}
				}
			}
			throw new UnsupportedOperationException("Recursion is not supported: procedure " + callee
					+ " is (transitively) reachable from itself via a call from " + caller
					+ "; the full recursive call cycle is " + cycle);
		}

		final List<String> result = new ArrayList<>();
		for (final StronglyConnectedComponent<String> comp : sccComputation.getSCCs()) {
			result.add(comp.getNodes().iterator().next());
		}
		return result;
	}

	// ----------------------------------------------------------------------------------------------------------
	// Helpers shared by the interprocedural consumers
	// ----------------------------------------------------------------------------------------------------------

	/** The states of the abstraction, grouped by the procedure they belong to. */
	public static <STATE> Map<String, Set<STATE>> groupStatesByProcedure(final Iterable<STATE> states) {
		final Map<String, Set<STATE>> result = new LinkedHashMap<>();
		for (final STATE state : states) {
			result.computeIfAbsent(procedureOf(state), k -> new LinkedHashSet<>()).add(state);
		}
		return result;
	}

	/**
	 * States in {@code scopeStates} with an outgoing return transition to at least one of {@code callSites} - a
	 * procedure's own normal-return points, call-site-agnostic (reused as the FINAL set for every caller's virtual
	 * edge into this procedure). {@code callSites} is every call site anywhere in the automaton that is known to
	 * call this procedure, so this is sound and complete without needing to query the automaton for "any return
	 * transition regardless of hier", which its API does not expose directly.
	 */
	public static <LETTER extends IAction, STATE> Set<STATE> computeExitStates(
			final INestedWordAutomaton<LETTER, STATE> abstraction, final Set<STATE> scopeStates,
			final Set<STATE> callSites) {
		final Set<STATE> result = new LinkedHashSet<>();
		for (final STATE state : scopeStates) {
			for (final STATE callSite : callSites) {
				if (abstraction.returnSuccessorsGivenHier(state, callSite).iterator().hasNext()) {
					result.add(state);
					break;
				}
			}
		}
		return result;
	}

	/** The elements of {@code a} that are also in {@code b}. */
	public static <STATE> Set<STATE> intersect(final Iterable<STATE> a, final Set<STATE> b) {
		final Set<STATE> result = new LinkedHashSet<>();
		for (final STATE s : a) {
			if (b.contains(s)) {
				result.add(s);
			}
		}
		return result;
	}

	/**
	 * The formula of a virtual call edge: the whole call-to-return span of one call site, i.e. the parameter
	 * assignment of the call, the callee's summary and the assignment of the return, composed by
	 * {@link TransFormulaUtils#sequentialCompositionWithCallAndReturn} - the primitive that gets the scoping of
	 * oldvars, modifiable globals and the callee's locals right, and the same one the rest of this codebase (e.g.
	 * {@code IcfgEdgeBuilder}) uses for this composition.
	 */
	public static UnmodifiableTransFormula computeVirtualEdge(final IUltimateServiceProvider services,
			final ILogger logger, final CfgSmtToolkit csToolkit, final ManagedScript mgdScript,
			final ICallAction callAction, final String callee, final UnmodifiableTransFormula calleeSummary,
			final UnmodifiableTransFormula returnTf) {
		final UnmodifiableTransFormula oldVarsAssignment =
				csToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(callee);
		final UnmodifiableTransFormula globalVarsAssignment =
				csToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(callee);
		final Set<IProgramNonOldVar> modifiableGlobals =
				csToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(callee);
		return TransFormulaUtils.sequentialCompositionWithCallAndReturn(mgdScript, false, false, false,
				callAction.getLocalVarsAssignment(), oldVarsAssignment, globalVarsAssignment, calleeSummary, returnTf,
				logger, services, SimplificationTechnique.NONE, csToolkit.getSymbolTable(), modifiableGlobals);
	}
}
