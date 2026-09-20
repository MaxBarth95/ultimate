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
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.GenericLabeledGraph;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.PathExpressionComputer;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Concatenation;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.EmptySet;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegexVisitor;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Union;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Given a nested word automaton, builds every {@link UnmodifiableTransFormula} that k-induction (and IMC) needs, for
 * programs with no loop, any number of sequential loops, and arbitrarily <b>nested</b> loops.
 * <p>
 * The result is a {@link LoopTree}: a tree of {@link Scope}s. The root scope is the whole program, every other scope
 * is one loop. Inside a scope, the nodes are <em>checkpoints</em> (see {@link Checkpoint}): the scope's start, the
 * heads of its directly nested loops, its end (a loop's own head, reached again after one iteration), the
 * error/accepting states ({@code FINAL}) and every state the scope can leave to ({@code ESCAPE}, e.g. a
 * {@code break} out of a loop). The edges are formulas summarizing <b>all</b> loop-free paths between two
 * checkpoints, so the requested parts are:
 * <ul>
 * <li>part before / after a loop: the root scope's edges {@code INIT -> loopHead} and {@code loopHead -> FINAL} (for
 * a nested loop: the same edges in its enclosing loop's scope),
 * <li>loop entry: {@link Scope#getEntry()}, the union of the transitions that go from the head into the loop,
 * <li>loop exit: {@link Scope#getExit()}, the union of the transitions that leave the loop from its head,
 * <li>loop body: {@link Scope#getBody()} for a loop without inner loops (one iteration, head back to head, including
 * the entry transition). A loop with inner loops has no single loop-free body formula; its body is the checkpoint
 * graph of its scope ({@link Scope#getEdge}), where each inner loop appears as a checkpoint,
 * <li>no loop at all: the root scope's edge {@code INIT -> FINAL} is the whole program.
 * </ul>
 * <p>
 * Loops are found structurally (strongly connected components, recursively with the head removed), so no annotation
 * is required. The head of a loop is the unique state through which the loop is entered; a loop with several entry
 * states (irreducible control flow) is rejected. Several entry and exit transitions per head are supported.
 * <p>
 * Call and return transitions are treated like internal transitions, with {@code letter.getTransformula()} as their
 * formula. This is only sound because procedures are inlined, i.e. a return always belongs to the one call it
 * follows. Optionally, a scope-restricted mode with precomputed "virtual" call edges (one formula for a whole
 * call-to-return span) is supported, see the second constructor.
 *
 * <h2>How to use</h2>
 *
 * Construct the builder, call {@link #build()} once, and read the formulas off the scopes of the resulting
 * {@link LoopTree}. All formulas live in the {@link ManagedScript} passed to the constructor. That script must
 * <b>not</b> be locked while {@link #build()} runs: composing transition formulas declares constants for their aux
 * vars and therefore acquires the lock itself. Lock the script afterwards, once all formulas exist, to use them in a
 * solver. Every {@code getEdge} returns {@code null} if there is no such path, which is normal and not an error.
 *
 * <pre>{@code
 * final LoopTreeFormulaBuilder<LETTER, STATE> builder =
 * 		new LoopTreeFormulaBuilder<>(services, logger, mgdScript, nwa);
 * final LoopTree<STATE> tree = builder.build();
 * final Scope<STATE> root = tree.getRoot();
 * }</pre>
 *
 * <b>No loop.</b> The whole program is one formula:
 *
 * <pre>{@code
 * final UnmodifiableTransFormula program = root.getEdge(Checkpoint.init(), Checkpoint.fin());
 * }</pre>
 *
 * <b>Sequential loops.</b> The parts before and after each loop are edges of the root scope, the loop itself is a
 * child scope. The part between two loops {@code a} and {@code b} is
 * {@code root.getEdge(Checkpoint.loopHead(a), Checkpoint.loopHead(b))}, and {@code root.enumeratePaths()} lists all
 * checkpoint sequences from the program start to an error state, e.g. {@code [INIT, loopHead(a), loopHead(b), FINAL]}.
 *
 * <pre>{@code
 * for (final STATE head : root.getLoopHeads()) {
 * 	final Scope<STATE> loop = root.getChild(head);
 * 	final Checkpoint<STATE> headCp = Checkpoint.loopHead(head);
 * 	final UnmodifiableTransFormula before = root.getEdge(Checkpoint.init(), headCp);
 * 	final UnmodifiableTransFormula after = root.getEdge(headCp, Checkpoint.fin());
 * 	final UnmodifiableTransFormula entry = loop.getEntry(); // head into the loop
 * 	final UnmodifiableTransFormula exit = loop.getExit(); // head out of the loop
 * 	final UnmodifiableTransFormula body = loop.getBody(); // one iteration, head to head
 * }
 * }</pre>
 *
 * The edges leaving {@code Checkpoint.init()} inside a loop scope include the entry transition, so
 * {@code getBody()} already contains the loop condition; {@code getEntry()} gives the entry transition on its own.
 * <p>
 * <b>Nested loops.</b> {@code tree.getLoops()} lists all loops, outer loops before the loops nested in them. A loop
 * without inner loops (see {@link Scope#isLeaf()}) has a single body formula. For a loop with inner loops
 * {@code getBody()} throws an {@link UnsupportedOperationException}; use the checkpoint graph of its scope instead,
 * in which every inner loop is a checkpoint:
 *
 * <pre>{@code
 * for (final Scope<STATE> loop : tree.getLoops()) {
 * 	if (loop.isLeaf()) {
 * 		final UnmodifiableTransFormula body = loop.getBody();
 * 	} else {
 * 		final Checkpoint<STATE> inner = Checkpoint.loopHead(loop.getChildren().get(0).getHead());
 * 		loop.getEdge(Checkpoint.init(), inner); // start of this loop's body to the inner loop head
 * 		loop.getEdge(inner, Checkpoint.end()); // inner loop head back to this loop's head
 * 		loop.getEdge(inner, Checkpoint.fin()); // inner loop head to an error state
 * 		loop.getEdge(inner, Checkpoint.escape(state)); // inner loop head to a state outside this loop (break)
 * 	}
 * }
 * }</pre>
 *
 * To restrict the builder to a single procedure, use the second constructor with explicit scope, initial and final
 * states.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class LoopTreeFormulaBuilder<LETTER extends IAction, STATE> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final Set<STATE> mScopeStates;
	private final Set<STATE> mInitStates;
	private final Collection<STATE> mFinalStates;
	private final Map<STATE, Map<STATE, UnmodifiableTransFormula>> mVirtualCallEdges;
	private final Map<LETTER, UnmodifiableTransFormula> mLetterCache = new HashMap<>();

	private final Map<STATE, List<Pair<Edge<LETTER>, STATE>>> mSuccessors = new HashMap<>();
	private final Map<STATE, Set<STATE>> mPredecessors = new HashMap<>();
	private List<STATE> mCallSites;

	/**
	 * Whole-automaton constructor: no scoping, no virtual call edges.
	 */
	public LoopTreeFormulaBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final INestedWordAutomaton<LETTER, STATE> abstraction) {
		this(services, logger, mgdScript, abstraction, abstraction.getStates(), abstraction.getInitialStates(),
				abstraction.getFinalStates(), Collections.emptyMap());
	}

	/**
	 * Scoped constructor, e.g. for a single procedure's body. Only states in {@code scopeStates} are considered;
	 * {@code virtualCallEdges} adds one precomputed edge per call site (call state, post-return state, formula).
	 */
	public LoopTreeFormulaBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final INestedWordAutomaton<LETTER, STATE> abstraction,
			final Set<STATE> scopeStates, final Set<STATE> initStates, final Collection<STATE> finalStates,
			final Map<STATE, Map<STATE, UnmodifiableTransFormula>> virtualCallEdges) {
		mServices = services;
		mLogger = logger;
		mMgdScript = mgdScript;
		mAbstraction = abstraction;
		mScopeStates = scopeStates;
		mInitStates = initStates;
		mFinalStates = finalStates;
		mVirtualCallEdges = virtualCallEdges;
	}

	/**
	 * Builds the loop tree. All formulas are native to the {@link ManagedScript} passed to the constructor.
	 */
	public LoopTree<STATE> build() {
		rejectRecursion();
		final Set<STATE> reachable = computeReachable();
		for (final STATE state : reachable) {
			for (final Pair<Edge<LETTER>, STATE> t : successors(state)) {
				mPredecessors.computeIfAbsent(t.getSecond(), k -> new LinkedHashSet<>()).add(state);
			}
		}
		final Scope<STATE> root = buildScope(null, reachable, 0);
		final LoopTree<STATE> tree = new LoopTree<>(root);
		mLogger.info("LoopTree: built tree with %d loop(s), maximal nesting depth %d", tree.getLoops().size(),
				tree.getMaxDepth());
		return tree;
	}

	// ------------------------------------------------------------------------------------------------------------
	// Flat graph
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * Call and return transitions are treated as plain edges, which is only sound if procedures can be inlined, i.e.
	 * without recursion. Throws {@link UnsupportedOperationException} if some procedure can call itself.
	 */
	private void rejectRecursion() {
		final Map<String, Set<String>> calls = new LinkedHashMap<>();
		for (final STATE state : mScopeStates) {
			for (final OutgoingCallTransition<LETTER, STATE> t : mAbstraction.callSuccessors(state)) {
				calls.computeIfAbsent(t.getLetter().getPrecedingProcedure(), k -> new LinkedHashSet<>())
						.add(t.getLetter().getSucceedingProcedure());
			}
		}
		final Set<String> done = new HashSet<>();
		for (final String procedure : calls.keySet()) {
			findCycle(procedure, calls, done, new ArrayList<>());
		}
	}

	private static void findCycle(final String procedure, final Map<String, Set<String>> calls,
			final Set<String> done, final List<String> path) {
		if (path.contains(procedure)) {
			throw new UnsupportedOperationException("Recursion is not supported (procedures must be inlinable), call cycle: "
					+ path.subList(path.indexOf(procedure), path.size()) + " -> " + procedure);
		}
		if (!done.add(procedure)) {
			return;
		}
		path.add(procedure);
		for (final String callee : calls.getOrDefault(procedure, Collections.emptySet())) {
			findCycle(callee, calls, done, path);
		}
		path.remove(path.size() - 1);
	}

	private Set<STATE> computeReachable() {
		final Set<STATE> visited = new LinkedHashSet<>();
		final Deque<STATE> worklist = new ArrayDeque<>();
		for (final STATE init : mInitStates) {
			if (mScopeStates.contains(init) && visited.add(init)) {
				worklist.add(init);
			}
		}
		while (!worklist.isEmpty()) {
			final STATE state = worklist.poll();
			for (final Pair<Edge<LETTER>, STATE> t : successors(state)) {
				if (visited.add(t.getSecond())) {
					worklist.add(t.getSecond());
				}
			}
		}
		return visited;
	}

	/**
	 * Every way to leave {@code state} inside the scope: internal, call and return transitions (all treated as plain
	 * edges, see the class javadoc), plus precomputed virtual call edges. Memoized.
	 */
	private List<Pair<Edge<LETTER>, STATE>> successors(final STATE state) {
		final List<Pair<Edge<LETTER>, STATE>> cached = mSuccessors.get(state);
		if (cached != null) {
			return cached;
		}
		final List<Pair<Edge<LETTER>, STATE>> result = new ArrayList<>();
		final Set<Pair<LETTER, STATE>> seen = new HashSet<>();
		for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(state)) {
			addReal(result, seen, t.getLetter(), t.getSucc());
		}
		for (final OutgoingCallTransition<LETTER, STATE> t : mAbstraction.callSuccessors(state)) {
			addReal(result, seen, t.getLetter(), t.getSucc());
		}
		// A return needs its hierarchical predecessor; try every call site (unique after inlining, dedupe on
		// (letter, successor) otherwise).
		for (final STATE hier : getCallSites()) {
			for (final OutgoingReturnTransition<LETTER, STATE> t : mAbstraction.returnSuccessorsGivenHier(state,
					hier)) {
				addReal(result, seen, t.getLetter(), t.getSucc());
			}
		}
		final Map<STATE, UnmodifiableTransFormula> virtualFromHere = mVirtualCallEdges.get(state);
		if (virtualFromHere != null) {
			for (final Map.Entry<STATE, UnmodifiableTransFormula> entry : virtualFromHere.entrySet()) {
				result.add(new Pair<>(Edge.virtual(entry.getValue()), entry.getKey()));
			}
		}
		mSuccessors.put(state, result);
		return result;
	}

	private void addReal(final List<Pair<Edge<LETTER>, STATE>> result, final Set<Pair<LETTER, STATE>> seen,
			final LETTER letter, final STATE succ) {
		if (mScopeStates.contains(succ) && seen.add(new Pair<>(letter, succ))) {
			result.add(new Pair<>(Edge.real(letter), succ));
		}
	}

	private List<STATE> getCallSites() {
		if (mCallSites == null) {
			mCallSites = new ArrayList<>();
			for (final STATE state : mScopeStates) {
				if (mAbstraction.callSuccessors(state).iterator().hasNext()) {
					mCallSites.add(state);
				}
			}
		}
		return mCallSites;
	}

	private List<STATE> neighbors(final STATE state, final Set<STATE> within) {
		final List<STATE> result = new ArrayList<>();
		for (final Pair<Edge<LETTER>, STATE> t : successors(state)) {
			if (within.contains(t.getSecond()) && !result.contains(t.getSecond())) {
				result.add(t.getSecond());
			}
		}
		return result;
	}

	// ------------------------------------------------------------------------------------------------------------
	// Loop structure
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * Non-trivial strongly connected components (more than one state, or a self loop) of the subgraph induced by
	 * {@code nodes}. Iterative Tarjan, so deep programs cannot overflow the stack.
	 */
	private List<Set<STATE>> nontrivialSccs(final Set<STATE> nodes) {
		final List<Set<STATE>> result = new ArrayList<>();
		final Map<STATE, Integer> index = new HashMap<>();
		final Map<STATE, Integer> lowLink = new HashMap<>();
		final Deque<STATE> sccStack = new ArrayDeque<>();
		final Set<STATE> onStack = new HashSet<>();
		int counter = 0;
		for (final STATE start : nodes) {
			if (index.containsKey(start)) {
				continue;
			}
			final Deque<STATE> dfsNodes = new ArrayDeque<>();
			final Deque<Iterator<STATE>> dfsIterators = new ArrayDeque<>();
			index.put(start, counter);
			lowLink.put(start, counter);
			counter++;
			sccStack.push(start);
			onStack.add(start);
			dfsNodes.push(start);
			dfsIterators.push(neighbors(start, nodes).iterator());
			while (!dfsNodes.isEmpty()) {
				final STATE node = dfsNodes.peek();
				final Iterator<STATE> it = dfsIterators.peek();
				if (it.hasNext()) {
					final STATE next = it.next();
					if (!index.containsKey(next)) {
						index.put(next, counter);
						lowLink.put(next, counter);
						counter++;
						sccStack.push(next);
						onStack.add(next);
						dfsNodes.push(next);
						dfsIterators.push(neighbors(next, nodes).iterator());
					} else if (onStack.contains(next)) {
						lowLink.put(node, Math.min(lowLink.get(node), index.get(next)));
					}
					continue;
				}
				dfsNodes.pop();
				dfsIterators.pop();
				if (!dfsNodes.isEmpty()) {
					final STATE parent = dfsNodes.peek();
					lowLink.put(parent, Math.min(lowLink.get(parent), lowLink.get(node)));
				}
				if (lowLink.get(node).equals(index.get(node))) {
					final Set<STATE> scc = new LinkedHashSet<>();
					STATE member;
					do {
						member = sccStack.pop();
						onStack.remove(member);
						scc.add(member);
					} while (!member.equals(node));
					if (scc.size() > 1 || neighbors(node, nodes).contains(node)) {
						result.add(scc);
					}
				}
			}
		}
		return result;
	}

	/**
	 * The head of the loop {@code loop} (a strongly connected component inside {@code enclosing}): the one state
	 * that is entered from outside the loop. Anything else is irreducible control flow.
	 */
	private STATE findHead(final Set<STATE> loop, final Set<STATE> enclosing, final boolean enclosingIsRoot) {
		final List<STATE> entries = new ArrayList<>();
		for (final STATE state : loop) {
			boolean isEntry = enclosingIsRoot && mInitStates.contains(state);
			for (final STATE pred : mPredecessors.getOrDefault(state, Collections.emptySet())) {
				if (loop.contains(pred)) {
					continue;
				}
				if (!enclosing.contains(pred)) {
					throw new UnsupportedOperationException(
							"Irreducible control flow: loop state " + state + " is entered from " + pred
									+ ", which is outside the enclosing loop");
				}
				isEntry = true;
			}
			if (isEntry) {
				entries.add(state);
			}
		}
		if (entries.size() != 1) {
			throw new UnsupportedOperationException(
					"Irreducible control flow: loop has " + entries.size() + " entry states " + entries);
		}
		return entries.get(0);
	}

	// ------------------------------------------------------------------------------------------------------------
	// Scopes
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * Builds the scope of the loop with head {@code head} and states {@code region}, or the root scope if
	 * {@code head == null}. Inner loops are built first (bottom-up), and each shows up here as a checkpoint.
	 */
	private Scope<STATE> buildScope(final STATE head, final Set<STATE> region, final int depth) {
		final boolean isRoot = head == null;
		final Set<STATE> inner = new LinkedHashSet<>(region);
		if (!isRoot) {
			inner.remove(head);
		}

		// inner loops
		final List<Scope<STATE>> children = new ArrayList<>();
		final Set<STATE> interiors = new HashSet<>();
		for (final Set<STATE> loop : nontrivialSccs(inner)) {
			final STATE childHead = findHead(loop, region, isRoot);
			children.add(buildScope(childHead, loop, depth + 1));
			interiors.addAll(loop);
			interiors.remove(childHead);
		}
		final Set<STATE> childHeads = new LinkedHashSet<>();
		for (final Scope<STATE> child : children) {
			childHeads.add(child.getHead());
		}

		// states this scope can leave to
		final Set<STATE> escapes = new LinkedHashSet<>();
		if (!isRoot) {
			for (final STATE state : region) {
				if (state.equals(head)) {
					continue;
				}
				for (final Pair<Edge<LETTER>, STATE> t : successors(state)) {
					if (!region.contains(t.getSecond())) {
						escapes.add(t.getSecond());
					}
				}
			}
		}

		// cut graph: no interiors of inner loops, no outgoing edges of inner heads or of the own head, so it is
		// acyclic
		final Set<STATE> nodes = new LinkedHashSet<>();
		for (final STATE state : region) {
			if (!interiors.contains(state)) {
				nodes.add(state);
			}
		}
		nodes.addAll(escapes);
		final GenericLabeledGraph<STATE, Edge<LETTER>> graph = new GenericLabeledGraph<>();
		for (final STATE node : nodes) {
			graph.addNode(node);
		}
		for (final STATE node : nodes) {
			if (escapes.contains(node) || node.equals(head) || childHeads.contains(node)) {
				continue;
			}
			for (final Pair<Edge<LETTER>, STATE> t : successors(node)) {
				if (nodes.contains(t.getSecond())) {
					graph.addEdge(node, t.getFirst(), t.getSecond());
				}
			}
		}
		final PathExpressionComputer<STATE, Edge<LETTER>> pathExprComputer = new PathExpressionComputer<>(graph);
		final RegexToTransFormula evaluator = new RegexToTransFormula();

		// checkpoints and the states each stands for
		final Map<Checkpoint<STATE>, Collection<STATE>> targets = new LinkedHashMap<>();
		for (final STATE childHead : childHeads) {
			targets.put(Checkpoint.loopHead(childHead), Collections.singleton(childHead));
		}
		if (!isRoot) {
			targets.put(Checkpoint.end(), Collections.singleton(head));
		}
		final List<STATE> finals = new ArrayList<>();
		for (final STATE state : mFinalStates) {
			if (nodes.contains(state)) {
				finals.add(state);
			}
		}
		if (!finals.isEmpty()) {
			targets.put(Checkpoint.fin(), finals);
		}
		for (final STATE escape : escapes) {
			if (!finals.contains(escape)) {
				targets.put(Checkpoint.escape(escape), Collections.singleton(escape));
			}
		}

		final Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> edges = new LinkedHashMap<>();

		// edges out of the start: (prefix formula or null, first state) pairs
		final List<Pair<UnmodifiableTransFormula, STATE>> sources = new ArrayList<>();
		UnmodifiableTransFormula entry = null;
		UnmodifiableTransFormula exit = null;
		if (isRoot) {
			for (final STATE init : mInitStates) {
				if (nodes.contains(init)) {
					sources.add(new Pair<>(null, init));
				}
			}
		} else {
			final List<UnmodifiableTransFormula> entries = new ArrayList<>();
			final List<UnmodifiableTransFormula> exits = new ArrayList<>();
			for (final Pair<Edge<LETTER>, STATE> t : successors(head)) {
				final UnmodifiableTransFormula tf = evaluator.letterFormula(t.getFirst());
				if (region.contains(t.getSecond())) {
					entries.add(tf);
					sources.add(new Pair<>(tf, t.getSecond()));
				} else {
					exits.add(tf);
				}
			}
			entry = combineAlternatives(mLogger, mServices, mMgdScript, entries);
			exit = combineAlternatives(mLogger, mServices, mMgdScript, exits);
		}
		for (final Map.Entry<Checkpoint<STATE>, Collection<STATE>> target : targets.entrySet()) {
			final List<UnmodifiableTransFormula> alternatives = new ArrayList<>();
			for (final Pair<UnmodifiableTransFormula, STATE> source : sources) {
				for (final STATE rep : target.getValue()) {
					final UnmodifiableTransFormula path =
							evaluator.evaluate(pathExprComputer.exprBetween(source.getSecond(), rep));
					if (path == null) {
						continue;
					}
					alternatives.add(source.getFirst() == null ? path : sequential(source.getFirst(), path));
				}
			}
			addEdge(edges, Checkpoint.init(), target.getKey(), alternatives);
		}

		// edges out of inner loop heads: leave via an exit transition, or (mid-body) leave from inside the body
		for (final Scope<STATE> child : children) {
			final STATE childHead = child.getHead();
			final Checkpoint<STATE> from = Checkpoint.loopHead(childHead);
			for (final Map.Entry<Checkpoint<STATE>, Collection<STATE>> target : targets.entrySet()) {
				if (target.getKey().equals(from)) {
					continue;
				}
				final List<UnmodifiableTransFormula> alternatives = new ArrayList<>();
				for (final Pair<Edge<LETTER>, STATE> t : successors(childHead)) {
					if (child.getRegion().contains(t.getSecond())) {
						continue;
					}
					final UnmodifiableTransFormula exitTf = evaluator.letterFormula(t.getFirst());
					for (final STATE rep : target.getValue()) {
						final UnmodifiableTransFormula tail =
								evaluator.evaluate(pathExprComputer.exprBetween(t.getSecond(), rep));
						if (tail != null) {
							alternatives.add(sequential(exitTf, tail));
						}
					}
				}
				for (final Checkpoint<STATE> leave : child.getLeaveCheckpoints()) {
					final UnmodifiableTransFormula body = child.getEdge(Checkpoint.init(), leave);
					if (body == null) {
						continue;
					}
					if (leave.isFinal()) {
						if (target.getKey().isFinal()) {
							alternatives.add(body);
						}
						continue;
					}
					final STATE escapeState = leave.getEscapeState();
					if (!nodes.contains(escapeState)) {
						continue;
					}
					for (final STATE rep : target.getValue()) {
						final UnmodifiableTransFormula tail =
								evaluator.evaluate(pathExprComputer.exprBetween(escapeState, rep));
						if (tail != null) {
							alternatives.add(sequential(body, tail));
						}
					}
				}
				addEdge(edges, from, target.getKey(), alternatives);
			}
		}

		// edges out of "waypoints": a plain state of this scope that an inner loop can jump to (e.g. by break). The
		// inner loop's scope only knows how to get to the waypoint, the way on from there is described here.
		final Set<STATE> waypoints = new LinkedHashSet<>();
		for (final Scope<STATE> child : children) {
			for (final Checkpoint<STATE> escape : child.getEscapeTargets()) {
				final STATE w = escape.getEscapeState();
				if (nodes.contains(w) && !childHeads.contains(w) && !w.equals(head) && !escapes.contains(w)
						&& !finals.contains(w)) {
					waypoints.add(w);
				}
			}
		}
		for (final STATE waypoint : waypoints) {
			for (final Map.Entry<Checkpoint<STATE>, Collection<STATE>> target : targets.entrySet()) {
				final List<UnmodifiableTransFormula> alternatives = new ArrayList<>();
				for (final STATE rep : target.getValue()) {
					final UnmodifiableTransFormula path =
							evaluator.evaluate(pathExprComputer.exprBetween(waypoint, rep));
					if (path != null) {
						alternatives.add(path);
					}
				}
				addEdge(edges, Checkpoint.escape(waypoint), target.getKey(), alternatives);
			}
		}

		// The automaton states behind each checkpoint. Built here, from the maps above, rather than re-derived
		// by a consumer: a re-derivation could drift from what the formulas were actually built from.
		final Map<Checkpoint<STATE>, Collection<STATE>> checkpointStates = new LinkedHashMap<>(targets);
		if (isRoot) {
			final Set<STATE> starts = new LinkedHashSet<>();
			for (final Pair<UnmodifiableTransFormula, STATE> source : sources) {
				starts.add(source.getSecond());
			}
			checkpointStates.put(Checkpoint.init(), starts);
		} else {
			// In a loop scope an edge out of INIT starts AT THE HEAD and takes an entry transition first.
			checkpointStates.put(Checkpoint.init(), Collections.singleton(head));
		}

		final Scope<STATE> scope =
				new Scope<>(head, region, children, entry, exit, edges, depth, checkpointStates, nodes);
		mLogger.info("LoopTree: scope %s built: %d inner loop(s), %d state(s), %d checkpoint edge(s)",
				isRoot ? "ROOT" : "loop " + head, children.size(), region.size(), scope.getNumEdges());
		return scope;
	}

	private void addEdge(final Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> edges,
			final Checkpoint<STATE> from, final Checkpoint<STATE> to,
			final List<UnmodifiableTransFormula> alternatives) {
		final UnmodifiableTransFormula tf = combineAlternatives(mLogger, mServices, mMgdScript, alternatives);
		if (tf != null) {
			edges.computeIfAbsent(from, k -> new LinkedHashMap<>()).put(to, tf);
		}
	}

	/**
	 * Disjunction of alternatives, {@code null} if there is none (a legitimately absent edge, not an error).
	 */
	public static UnmodifiableTransFormula combineAlternatives(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final List<UnmodifiableTransFormula> alternatives) {
		if (alternatives.isEmpty()) {
			return null;
		}
		if (alternatives.size() == 1) {
			return alternatives.get(0);
		}
		return TransFormulaUtils.parallelComposition(logger, services, mgdScript, null, false, true,
				alternatives.toArray(new UnmodifiableTransFormula[0]));
	}

	private UnmodifiableTransFormula sequential(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mMgdScript, false, false, false,
				SimplificationTechnique.NONE, List.of(first, second));
	}

	/**
	 * Evaluates a path expression into one relational {@link UnmodifiableTransFormula}, or {@code null} if it
	 * describes no path ({@code null} is the algebraic zero). The cut graphs are acyclic, so {@link Star} cannot
	 * occur.
	 */
	private final class RegexToTransFormula implements IRegexVisitor<Edge<LETTER>, UnmodifiableTransFormula, Void> {

		UnmodifiableTransFormula evaluate(final IRegex<Edge<LETTER>> regex) {
			return regex.accept(this);
		}

		UnmodifiableTransFormula letterFormula(final Edge<LETTER> edge) {
			if (edge.isVirtual()) {
				return edge.getVirtualFormula();
			}
			final LETTER letter = edge.getRealLetter();
			return mLetterCache.computeIfAbsent(letter, IAction::getTransformula);
		}

		@Override
		public UnmodifiableTransFormula visit(final Union<Edge<LETTER>> union, final Void argument) {
			final UnmodifiableTransFormula first = evaluate(union.getFirst());
			final UnmodifiableTransFormula second = evaluate(union.getSecond());
			if (first == null) {
				return second;
			}
			if (second == null) {
				return first;
			}
			return TransFormulaUtils.parallelComposition(mLogger, mServices, mMgdScript, null, false, true, first,
					second);
		}

		@Override
		public UnmodifiableTransFormula visit(final Concatenation<Edge<LETTER>> concatenation, final Void argument) {
			final UnmodifiableTransFormula first = evaluate(concatenation.getFirst());
			if (first == null) {
				return null;
			}
			final UnmodifiableTransFormula second = evaluate(concatenation.getSecond());
			if (second == null) {
				return null;
			}
			return sequential(first, second);
		}

		@Override
		public UnmodifiableTransFormula visit(final Star<Edge<LETTER>> star, final Void argument) {
			throw new AssertionError("Unexpected cycle in the cut graph of a scope");
		}

		@Override
		public UnmodifiableTransFormula visit(final Literal<Edge<LETTER>> literal, final Void argument) {
			return letterFormula(literal.getLetter());
		}

		@Override
		public UnmodifiableTransFormula visit(final Epsilon<Edge<LETTER>> epsilon, final Void argument) {
			return TransFormulaBuilder.getTrivialTransFormula(mMgdScript);
		}

		@Override
		public UnmodifiableTransFormula visit(final EmptySet<Edge<LETTER>> emptySet, final Void argument) {
			return null;
		}
	}

	/**
	 * One edge of a cut graph: a real automaton letter, or a precomputed virtual edge for a whole call-to-return
	 * span.
	 */
	static final class Edge<LETTER> {
		private final LETTER mRealLetter;
		private final UnmodifiableTransFormula mVirtualFormula;

		private Edge(final LETTER realLetter, final UnmodifiableTransFormula virtualFormula) {
			mRealLetter = realLetter;
			mVirtualFormula = virtualFormula;
		}

		static <L> Edge<L> real(final L letter) {
			return new Edge<>(letter, null);
		}

		static <L> Edge<L> virtual(final UnmodifiableTransFormula formula) {
			return new Edge<>(null, formula);
		}

		boolean isVirtual() {
			return mRealLetter == null;
		}

		LETTER getRealLetter() {
			return mRealLetter;
		}

		UnmodifiableTransFormula getVirtualFormula() {
			return mVirtualFormula;
		}

		@Override
		public String toString() {
			return isVirtual() ? "virtual(call)" : String.valueOf(mRealLetter);
		}
	}

	/**
	 * A node of a scope's checkpoint graph.
	 * <ul>
	 * <li>INIT: the start of the scope (program entry for the root, the state after the entry transition for a loop),
	 * <li>LOOP_HEAD: the head of a loop directly nested in the scope,
	 * <li>END: a loop scope only, the loop's own head reached again after one iteration,
	 * <li>FINAL: the accepting/error states,
	 * <li>ESCAPE: a state outside the loop that its body can jump to (e.g. by {@code break}).
	 * </ul>
	 */
	public static final class Checkpoint<STATE> {
		private enum Kind {
			INIT, LOOP_HEAD, END, FINAL, ESCAPE
		}

		private final Kind mKind;
		private final STATE mState;

		private Checkpoint(final Kind kind, final STATE state) {
			mKind = kind;
			mState = state;
		}

		public static <STATE> Checkpoint<STATE> init() {
			return new Checkpoint<>(Kind.INIT, null);
		}

		public static <STATE> Checkpoint<STATE> end() {
			return new Checkpoint<>(Kind.END, null);
		}

		public static <STATE> Checkpoint<STATE> fin() {
			return new Checkpoint<>(Kind.FINAL, null);
		}

		public static <STATE> Checkpoint<STATE> loopHead(final STATE loopHead) {
			return new Checkpoint<>(Kind.LOOP_HEAD, loopHead);
		}

		public static <STATE> Checkpoint<STATE> escape(final STATE state) {
			return new Checkpoint<>(Kind.ESCAPE, state);
		}

		public boolean isInit() {
			return mKind == Kind.INIT;
		}

		public boolean isEnd() {
			return mKind == Kind.END;
		}

		public boolean isFinal() {
			return mKind == Kind.FINAL;
		}

		public boolean isLoopHead() {
			return mKind == Kind.LOOP_HEAD;
		}

		public boolean isEscape() {
			return mKind == Kind.ESCAPE;
		}

		public STATE getLoopHead() {
			if (mKind != Kind.LOOP_HEAD) {
				throw new IllegalStateException("Not a loop-head checkpoint: " + this);
			}
			return mState;
		}

		public STATE getEscapeState() {
			if (mKind != Kind.ESCAPE) {
				throw new IllegalStateException("Not an escape checkpoint: " + this);
			}
			return mState;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (!(obj instanceof Checkpoint)) {
				return false;
			}
			final Checkpoint<?> other = (Checkpoint<?>) obj;
			return mKind == other.mKind && Objects.equals(mState, other.mState);
		}

		@Override
		public int hashCode() {
			return Objects.hash(mKind, mState);
		}

		@Override
		public String toString() {
			return mState == null ? mKind.toString() : mKind + "(" + mState + ")";
		}
	}

	/**
	 * The result: the root scope (whole program) with all loops as nested scopes.
	 */
	public static final class LoopTree<STATE> {
		private final Scope<STATE> mRoot;

		LoopTree(final Scope<STATE> root) {
			mRoot = root;
		}

		public Scope<STATE> getRoot() {
			return mRoot;
		}

		/** All loops, outer loops before the loops nested in them. */
		public List<Scope<STATE>> getLoops() {
			final List<Scope<STATE>> result = new ArrayList<>();
			collect(mRoot, result);
			return result;
		}

		private void collect(final Scope<STATE> scope, final List<Scope<STATE>> result) {
			for (final Scope<STATE> child : scope.getChildren()) {
				result.add(child);
				collect(child, result);
			}
		}

		/** The scope of the loop with head {@code head}, or {@code null}. */
		public Scope<STATE> getLoop(final STATE head) {
			for (final Scope<STATE> loop : getLoops()) {
				if (loop.getHead().equals(head)) {
					return loop;
				}
			}
			return null;
		}

		public int getMaxDepth() {
			int result = 0;
			for (final Scope<STATE> loop : getLoops()) {
				result = Math.max(result, loop.getDepth());
			}
			return result;
		}
	}

	/**
	 * The program (root, {@code getHead() == null}) or one loop, with all formulas between its {@link Checkpoint}s.
	 * Edges are {@code null} if there is no such path.
	 */
	public static final class Scope<STATE> {
		private final STATE mHead;
		private final Set<STATE> mRegion;
		private final List<Scope<STATE>> mChildren;
		private final UnmodifiableTransFormula mEntry;
		private final UnmodifiableTransFormula mExit;
		private final Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> mEdges;
		private final int mDepth;
		private final Map<Checkpoint<STATE>, Collection<STATE>> mCheckpointStates;
		private final Set<STATE> mCutGraphNodes;

		Scope(final STATE head, final Set<STATE> region, final List<Scope<STATE>> children,
				final UnmodifiableTransFormula entry, final UnmodifiableTransFormula exit,
				final Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> edges,
				final int depth, final Map<Checkpoint<STATE>, Collection<STATE>> checkpointStates,
				final Set<STATE> cutGraphNodes) {
			mHead = head;
			mRegion = region;
			mChildren = children;
			mEntry = entry;
			mExit = exit;
			mEdges = edges;
			mDepth = depth;
			mCheckpointStates = checkpointStates;
			mCutGraphNodes = cutGraphNodes;
		}

		/**
		 * The automaton states a checkpoint stands for, both as the source and as the target of this scope's
		 * edges: INIT in the root are the initial states inside this scope, INIT in a loop is the head (an edge
		 * out of INIT starts there and takes an entry transition first), END is the head, LOOP_HEAD(c) is
		 * {@code c}, FINAL are the accepting states inside this scope, ESCAPE(s) is {@code s}.
		 *
		 * @return the states, empty if the checkpoint does not occur in this scope.
		 */
		public Collection<STATE> getCheckpointStates(final Checkpoint<STATE> checkpoint) {
			final Collection<STATE> result = mCheckpointStates.get(checkpoint);
			return result == null ? Collections.emptyList() : Collections.unmodifiableCollection(result);
		}

		/** The nodes of this scope's cut graph: the region without the interiors of inner loops, plus the escapes. */
		public Set<STATE> getCutGraphNodes() {
			return Collections.unmodifiableSet(mCutGraphNodes);
		}

		public boolean isRoot() {
			return mHead == null;
		}

		/** The loop head, {@code null} for the root. */
		public STATE getHead() {
			return mHead;
		}

		/** Nesting depth: 0 for the root, 1 for an outermost loop, ... */
		public int getDepth() {
			return mDepth;
		}

		public Set<STATE> getRegion() {
			return mRegion;
		}

		/** The loops directly nested in this scope. */
		public List<Scope<STATE>> getChildren() {
			return mChildren;
		}

		/** Heads of the loops directly nested in this scope. */
		public Set<STATE> getLoopHeads() {
			final Set<STATE> result = new LinkedHashSet<>();
			for (final Scope<STATE> child : mChildren) {
				result.add(child.getHead());
			}
			return result;
		}

		public boolean isLeaf() {
			return mChildren.isEmpty();
		}

		/** The directly nested loop with head {@code head}, or {@code null}. */
		public Scope<STATE> getChild(final STATE head) {
			for (final Scope<STATE> child : mChildren) {
				if (child.getHead().equals(head)) {
					return child;
				}
			}
			return null;
		}

		/** Loop entry: union of the transitions from the head into the loop. {@code null} for the root. */
		public UnmodifiableTransFormula getEntry() {
			return mEntry;
		}

		/** Loop exit: union of the transitions from the head out of the loop. {@code null} for the root. */
		public UnmodifiableTransFormula getExit() {
			return mExit;
		}

		/**
		 * One iteration of this loop (head back to head, including the entry transition). Only for a loop
		 * without inner loops, otherwise use {@link #getEdge} on this scope's checkpoints.
		 */
		public UnmodifiableTransFormula getBody() {
			if (isRoot() || !isLeaf()) {
				throw new UnsupportedOperationException("No single loop-free body formula for " + this
						+ ": it is the root or has inner loops; use the checkpoint graph (getEdge) instead");
			}
			return getEdge(Checkpoint.init(), Checkpoint.end());
		}

		/** The body formula of the directly nested loop with head {@code head}, see {@link #getBody()}. */
		public UnmodifiableTransFormula getLoopBody(final STATE head) {
			final Scope<STATE> child = getChild(head);
			if (child == null) {
				throw new IllegalArgumentException(head + " is not the head of a loop nested directly in " + this);
			}
			return child.getBody();
		}

		/** Every loop-free way of getting from checkpoint {@code from} to {@code to}, or {@code null}. */
		public UnmodifiableTransFormula getEdge(final Checkpoint<STATE> from, final Checkpoint<STATE> to) {
			final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing = mEdges.get(from);
			return outgoing == null ? null : outgoing.get(to);
		}

		/** The checkpoints (other than INIT) reachable from INIT. */
		public Set<Checkpoint<STATE>> getCheckpoints() {
			final Set<Checkpoint<STATE>> result = new LinkedHashSet<>();
			for (final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing : mEdges.values()) {
				result.addAll(outgoing.keySet());
			}
			return result;
		}

		/**
		 * All edges of this scope: source checkpoint, target checkpoint, formula. A source can be INIT, an inner
		 * loop head, or an ESCAPE checkpoint that stands for a "waypoint" state of this scope, i.e. a state inside
		 * this scope that an inner loop can jump to (the way on from there is described by these edges).
		 */
		public Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> getEdges() {
			return Collections.unmodifiableMap(mEdges);
		}

		/** All ESCAPE checkpoints that occur as the target of an edge of this scope. */
		public Set<Checkpoint<STATE>> getEscapeTargets() {
			final Set<Checkpoint<STATE>> result = new LinkedHashSet<>();
			for (final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing : mEdges.values()) {
				for (final Checkpoint<STATE> target : outgoing.keySet()) {
					if (target.isEscape()) {
						result.add(target);
					}
				}
			}
			return result;
		}

		/** The FINAL and ESCAPE checkpoints INIT has an edge to, i.e. the ways a path can leave this loop. */
		List<Checkpoint<STATE>> getLeaveCheckpoints() {
			final List<Checkpoint<STATE>> result = new ArrayList<>();
			final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing = mEdges.get(Checkpoint.init());
			if (outgoing != null) {
				for (final Checkpoint<STATE> checkpoint : outgoing.keySet()) {
					if (checkpoint.isFinal() || checkpoint.isEscape()) {
						result.add(checkpoint);
					}
				}
			}
			return result;
		}

		int getNumEdges() {
			int result = 0;
			for (final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing : mEdges.values()) {
				result += outgoing.size();
			}
			return result;
		}

		/** All simple paths from INIT to FINAL, see {@link #enumeratePaths(Checkpoint)}. */
		public List<List<Checkpoint<STATE>>> enumeratePaths() {
			return enumeratePaths(Checkpoint.fin());
		}

		/**
		 * Every simple path from INIT to {@code target} through the present edges, as an ordered checkpoint list.
		 * An execution may visit only a subset of the inner loop heads, possibly several in sequence, so this is a
		 * genuine enumeration. There is no upper bound on the number of paths, which can be exponential in the
		 * number of loops.
		 */
		public List<List<Checkpoint<STATE>>> enumeratePaths(final Checkpoint<STATE> target) {
			final List<List<Checkpoint<STATE>>> result = new ArrayList<>();
			final Deque<Checkpoint<STATE>> current = new ArrayDeque<>();
			final Checkpoint<STATE> init = Checkpoint.init();
			current.addLast(init);
			final Set<Checkpoint<STATE>> visited = new HashSet<>();
			visited.add(init);
			enumeratePaths(init, target, current, visited, result);
			return result;
		}

		private void enumeratePaths(final Checkpoint<STATE> node, final Checkpoint<STATE> target,
				final Deque<Checkpoint<STATE>> current, final Set<Checkpoint<STATE>> visited,
				final List<List<Checkpoint<STATE>>> result) {
			if (node.equals(target)) {
				result.add(new ArrayList<>(current));
				return;
			}
			final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing = mEdges.get(node);
			if (outgoing == null) {
				return;
			}
			for (final Checkpoint<STATE> next : outgoing.keySet()) {
				if (!visited.add(next)) {
					continue;
				}
				current.addLast(next);
				enumeratePaths(next, target, current, visited, result);
				current.removeLast();
				visited.remove(next);
			}
		}

		@Override
		public String toString() {
			return isRoot() ? "ROOT" : "loop(" + mHead + ")";
		}
	}
}
