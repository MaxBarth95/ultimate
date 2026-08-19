package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Builds the procedure call graph of a nested word automaton (nodes = procedure names, edges = "caller calls
 * callee", derived from the automaton's call transitions) and rejects recursion up front: {@link #getProceduresCalleeFirst()}
 * throws {@link UnsupportedOperationException} if any procedure is (transitively, possibly mutually) reachable from
 * itself via a call, naming the offending call and the full cycle - mirroring
 * {@link CheckpointGraphFormulaBuilder}'s existing non-nesting-loop check, which fails the same way before any
 * formula-building starts. This is not merely a scope limitation: {@link CheckpointGraphFormulaBuilder}'s virtual
 * call edges (see its class javadoc) need their callee's summary to already exist as a finished formula, which is
 * undefined for a cycle in the call graph.
 * <p>
 * On a non-recursive call graph, {@link #getProceduresCalleeFirst()} also gives the processing order
 * {@link InterproceduralImcOrchestrator} needs: every callee fully processed (and thus already holding a summary,
 * if it needs one) before any of its callers.
 */
final class ProcedureCallGraph {

	private final ILogger mLogger;
	private final Set<String> mProcedures = new LinkedHashSet<>();
	private final Set<String> mEntryProcedures = new LinkedHashSet<>();
	private final HashRelation<String, String> mCalls = new HashRelation<>();

	<LETTER extends IAction, STATE> ProcedureCallGraph(final ILogger logger,
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

	static <STATE> String procedureOf(final STATE state) {
		return ((ISLPredicate) state).getProgramPoint().getProcedure();
	}

	Set<String> getEntryProcedures() {
		return mEntryProcedures;
	}

	/**
	 * Every procedure, in an order where every callee occurs before every one of its callers. Throws if the call
	 * graph is recursive (a procedure transitively/mutually calls itself) - checked here, up front, before
	 * {@link InterproceduralImcOrchestrator} builds any checkpoint graph.
	 */
	List<String> getProceduresCalleeFirst() {
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
			throw new UnsupportedOperationException("InterpolationBasedModelChecking currently supports only "
					+ "non-recursive programs, but procedure " + callee + " is (transitively) reachable from "
					+ "itself via a call from " + caller + "; the full recursive call cycle is " + cycle);
		}

		final List<String> result = new ArrayList<>();
		for (final StronglyConnectedComponent<String> comp : sccComputation.getSCCs()) {
			result.add(comp.getNodes().iterator().next());
		}
		return result;
	}
}
