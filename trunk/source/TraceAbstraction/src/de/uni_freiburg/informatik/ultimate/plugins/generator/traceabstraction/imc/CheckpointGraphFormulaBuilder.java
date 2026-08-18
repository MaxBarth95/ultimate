package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Given a nested word automaton that represents a program with any number of loops (as long as none is nested
 * inside another's body), builds a small "checkpoint graph" whose nodes are the program's entry (INIT), every loop
 * head, and the program's accepting/error states (FINAL), and whose edges are {@link UnmodifiableTransFormula}s
 * summarizing <b>all</b> loop-free paths (not just one) between two checkpoints. Loop heads additionally get a
 * self-describing "loop body" formula (one pass through the loop, loop head back to loop head). Execution may visit
 * only a subset of the loop heads, and different branches may visit different subsets/orders, so INIT-to-FINAL
 * connectivity is a genuine DAG over checkpoints, not a flat list - see {@link CheckpointGraph#enumeratePaths()}.
 * <p>
 * With exactly one loop head, this collapses to formula-for-formula the same three regions
 * ({@code getEdge(INIT, loopHead)}, {@code getLoopBody(loopHead)}, {@code getEdge(loopHead, FINAL)}) this class used
 * to compute directly as prefix/loopBody/suffix.
 * <p>
 * Assumes procedures are already inlined: only internal transitions are considered, both at loop heads and
 * throughout the checkpoint graph. TODO: support call/return once that assumption is lifted.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class CheckpointGraphFormulaBuilder<LETTER extends IAction, STATE> {

	/**
	 * Hard cap on the number of distinct INIT-to-FINAL paths through the checkpoint graph. Exceeding it throws
	 * rather than silently truncating: dropping a whole path could hide a genuine bug entirely, which is a strictly
	 * worse failure mode than the per-loop {@code MAX_K} incompleteness {@link InterpolationBasedModelChecking}
	 * already accepts.
	 */
	private static final int MAX_PATHS = 256;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	// Plain term transfer only - IProgramVar identity is never translated (see transferLetterFormula), matching how
	// NestedSsaBuilder's own VariableVersioneer moves terms between scripts elsewhere in this codebase.
	private final Map<LETTER, UnmodifiableTransFormula> mLetterCache = new HashMap<>();

	public CheckpointGraphFormulaBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final INestedWordAutomaton<LETTER, STATE> abstraction) {
		mServices = services;
		mLogger = logger;
		mMgdScript = mgdScript;
		mAbstraction = abstraction;
	}

	/**
	 * Finds every loop head, validates the non-nesting invariant, then builds and returns the checkpoint graph, all
	 * native to the {@code targetMgdScript} passed to the constructor.
	 */
	public CheckpointGraph<STATE> build() {
		final Set<STATE> loopHeads = findLoopHeads();
		mLogger.info("IMC: found %d loop head(s): %s", loopHeads.size(), loopHeads);

		final Map<STATE, Pair<LETTER, STATE>> enters = new LinkedHashMap<>();
		final Map<STATE, Pair<LETTER, STATE>> exits = new LinkedHashMap<>();
		for (final STATE loopHead : loopHeads) {
			classifyLoopHeadTransitions(loopHead, enters, exits);
			mLogger.info("IMC: loop head %s - enter %s -> %s, exit %s -> %s", loopHead,
					enters.get(loopHead).getFirst(), enters.get(loopHead).getSecond(), exits.get(loopHead).getFirst(),
					exits.get(loopHead).getSecond());
		}

		final GenericLabeledGraph<STATE, LETTER> graph = buildCutGraph(loopHeads);
		mLogger.info("IMC: built checkpoint graph with %d states and %d edges (loop heads excluded from outgoing)",
				graph.getNodes().size(), graph.getEdges().size());

		final PathExpressionComputer<STATE, LETTER> pathExprComputer = new PathExpressionComputer<>(graph);
		final RegexToTransFormula evaluator = new RegexToTransFormula();

		validateNoNesting(loopHeads, enters, pathExprComputer, evaluator);

		final Map<STATE, UnmodifiableTransFormula> loopBodies = new LinkedHashMap<>();
		for (final STATE loopHead : loopHeads) {
			final Pair<LETTER, STATE> enter = enters.get(loopHead);
			final UnmodifiableTransFormula tail =
					evaluator.evaluate(pathExprComputer.exprBetween(enter.getSecond(), loopHead));
			if (tail == null) {
				throw new UnsupportedOperationException("Loop-entering transition of loop head " + loopHead
						+ " does not lead back to it via purely-internal transitions");
			}
			loopBodies.put(loopHead, sequential(evaluator.letterFormula(enter.getFirst()), tail));
			mLogger.info("IMC: loop-body formula for loop head %s built", loopHead);
		}

		final List<Checkpoint<STATE>> checkpoints = new ArrayList<>();
		checkpoints.add(Checkpoint.init());
		for (final STATE loopHead : loopHeads) {
			checkpoints.add(Checkpoint.loopHead(loopHead));
		}
		checkpoints.add(Checkpoint.fin());

		final Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> edges = new LinkedHashMap<>();
		for (final Checkpoint<STATE> from : checkpoints) {
			if (from.isFinal()) {
				continue;
			}
			for (final Checkpoint<STATE> to : checkpoints) {
				if (to.isInit() || from.equals(to)) {
					continue;
				}
				final UnmodifiableTransFormula edge =
						computeEdge(from, to, enters, exits, pathExprComputer, evaluator);
				if (edge != null) {
					edges.computeIfAbsent(from, k -> new LinkedHashMap<>()).put(to, edge);
					mLogger.info("IMC: edge %s -> %s built", from, to);
				}
			}
		}
		mLogger.info("IMC: checkpoint graph complete: %d checkpoint(s), %d loop body formula(s)", checkpoints.size(),
				loopBodies.size());

		return new CheckpointGraph<>(loopHeads, loopBodies, edges);
	}

	private void classifyLoopHeadTransitions(final STATE loopHead, final Map<STATE, Pair<LETTER, STATE>> enters,
			final Map<STATE, Pair<LETTER, STATE>> exits) {
		Pair<LETTER, STATE> enter = null;
		Pair<LETTER, STATE> exit = null;
		// TODO: only internal transitions considered at the loop head; extend to call/return once the loop
		// condition itself may involve a call.
		for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(loopHead)) {
			if (isLoopExitTransition(loopHead, t.getSucc())) {
				if (exit != null) {
					throw new UnsupportedOperationException("CheckpointGraphFormulaBuilder currently supports only "
							+ "a single loop-exit transition at loop head " + loopHead);
				}
				exit = new Pair<>(t.getLetter(), t.getSucc());
			} else {
				if (enter != null) {
					throw new UnsupportedOperationException("CheckpointGraphFormulaBuilder currently supports only "
							+ "a single loop-entry transition at loop head " + loopHead);
				}
				enter = new Pair<>(t.getLetter(), t.getSucc());
			}
		}
		if (enter == null || exit == null) {
			throw new UnsupportedOperationException(
					"Could not find both a loop-entering and a loop-exiting transition at loop head " + loopHead);
		}
		enters.put(loopHead, enter);
		exits.put(loopHead, exit);
	}

	/**
	 * Copies the whole automaton, suppressing every loop head's outgoing edges. Every cycle in the automaton passes
	 * through at least one {@link LoopEntryAnnotation}-marked state, so suppressing all of them here is what keeps
	 * this graph acyclic/Star-free for {@link PathExpressionComputer}, generalizing the single-loop-head argument
	 * this class used to rely on.
	 */
	private GenericLabeledGraph<STATE, LETTER> buildCutGraph(final Set<STATE> loopHeads) {
		final GenericLabeledGraph<STATE, LETTER> graph = new GenericLabeledGraph<>();
		// TODO: only internal transitions are added to the graph; extend to call/return edges once procedures
		// aren't assumed pre-inlined.
		for (final STATE state : mAbstraction.getStates()) {
			graph.addNode(state);
			if (loopHeads.contains(state)) {
				continue;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(state)) {
				graph.addEdge(state, t.getLetter(), t.getSucc());
			}
		}
		return graph;
	}

	/**
	 * "Non-nested" means no loop head is reachable from inside another loop head's body before that loop returns to
	 * its own head - if it were, the inner loop head would structurally be part of the outer loop's body extent.
	 * Checked directly via the same {@code exprBetween}/{@code evaluate} calls used everywhere else in this class
	 * (no separate reachability search needed), before any formula is built, so a violation fails fast.
	 */
	private void validateNoNesting(final Set<STATE> loopHeads, final Map<STATE, Pair<LETTER, STATE>> enters,
			final PathExpressionComputer<STATE, LETTER> pathExprComputer, final RegexToTransFormula evaluator) {
		for (final STATE outer : loopHeads) {
			final STATE enterSucc = enters.get(outer).getSecond();
			for (final STATE inner : loopHeads) {
				if (outer.equals(inner)) {
					continue;
				}
				if (evaluator.evaluate(pathExprComputer.exprBetween(enterSucc, inner)) != null) {
					throw new UnsupportedOperationException("CheckpointGraphFormulaBuilder currently supports only "
							+ "non-nested loops, but loop head " + inner + " is reachable from inside loop head "
							+ outer + "'s body without first returning to " + outer);
				}
			}
		}
		mLogger.info("IMC: non-nesting check passed for %d loop head(s)", loopHeads.size());
	}

	/**
	 * The automaton states a checkpoint stands for, when it is the <em>target</em> of an edge query: a loop head
	 * stands for itself, FINAL stands for every accepting/error state. INIT is never a target (nothing points back
	 * to program entry), so it has none.
	 */
	private Collection<STATE> representativeStates(final Checkpoint<STATE> checkpoint) {
		if (checkpoint.isFinal()) {
			return mAbstraction.getFinalStates();
		}
		if (checkpoint.isLoopHead()) {
			return Collections.singleton(checkpoint.getLoopHead());
		}
		throw new AssertionError("INIT checkpoint has no representative states as an edge target");
	}

	/**
	 * All loop-free ways of getting from checkpoint {@code from} to checkpoint {@code to}, or {@code null} if there
	 * are none (a legitimate, non-erroneous outcome in a multi-loop checkpoint DAG - unlike the mandatory
	 * {@code loopBody} formula, an edge between two checkpoints may simply not exist). Generalizes what this class
	 * used to compute as two hardcoded special cases:
	 * <ul>
	 * <li>{@code from == INIT}: every way an initial state reaches a representative state of {@code to} - this used
	 * to be hardcoded to "reaches the (one) loop head" (the old {@code prefix}); with {@code to == FINAL} it also
	 * transparently covers a path that skips every loop entirely.
	 * <li>{@code from} a loop head: every way execution can reach a representative state of {@code to} <em>without
	 * necessarily finishing this loop's current iteration</em> - via the loop's exit transition, or directly from
	 * inside the loop body (e.g. a failing assertion mid-iteration). This used to be hardcoded to "reaches a final
	 * state" (the old {@code suffix}); the same two routes are equally valid when the target is the next loop head
	 * on a path instead of the program's own error location.
	 * </ul>
	 */
	private UnmodifiableTransFormula computeEdge(final Checkpoint<STATE> from, final Checkpoint<STATE> to,
			final Map<STATE, Pair<LETTER, STATE>> enters, final Map<STATE, Pair<LETTER, STATE>> exits,
			final PathExpressionComputer<STATE, LETTER> pathExprComputer, final RegexToTransFormula evaluator) {
		final List<UnmodifiableTransFormula> alternatives = new ArrayList<>();
		if (from.isInit()) {
			for (final STATE init : mAbstraction.getInitialStates()) {
				for (final STATE target : representativeStates(to)) {
					final UnmodifiableTransFormula tf = evaluator.evaluate(pathExprComputer.exprBetween(init, target));
					if (tf != null) {
						alternatives.add(tf);
					}
				}
			}
		} else if (from.isLoopHead()) {
			final Pair<LETTER, STATE> exit = exits.get(from.getLoopHead());
			final Pair<LETTER, STATE> enter = enters.get(from.getLoopHead());
			for (final STATE target : representativeStates(to)) {
				final UnmodifiableTransFormula exitTail =
						evaluator.evaluate(pathExprComputer.exprBetween(exit.getSecond(), target));
				if (exitTail != null) {
					alternatives.add(sequential(evaluator.letterFormula(exit.getFirst()), exitTail));
				}
				final UnmodifiableTransFormula midLoopTail =
						evaluator.evaluate(pathExprComputer.exprBetween(enter.getSecond(), target));
				if (midLoopTail != null) {
					alternatives.add(sequential(evaluator.letterFormula(enter.getFirst()), midLoopTail));
				}
			}
		} else {
			throw new AssertionError("FINAL checkpoint has no outgoing edges");
		}
		return combine(alternatives);
	}

	/**
	 * {@code null} on an empty list - a legitimately absent edge, not an error (see {@link #computeEdge}); callers
	 * with a mandatory alternative (only {@code loopBody} today) check for {@code null} themselves.
	 */
	private UnmodifiableTransFormula combine(final List<UnmodifiableTransFormula> alternatives) {
		if (alternatives.isEmpty()) {
			return null;
		}
		if (alternatives.size() == 1) {
			return alternatives.get(0);
		}
		return TransFormulaUtils.parallelComposition(mLogger, mServices, mMgdScript, null, false, true,
				alternatives.toArray(new UnmodifiableTransFormula[0]));
	}

	private UnmodifiableTransFormula sequential(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mMgdScript, false, false, false,
				SimplificationTechnique.NONE, List.of(first, second));
	}

	/**
	 * A transition out of a loop head is a "loop exit" if, after taking it, that same loop head can no longer be
	 * reached again - i.e. it leaves the loop's cycle for good. Determined by exploring the automaton for a path
	 * from {@code succ} back to {@code loopHead} rather than relying on a {@code LoopExitAnnotation} (which does not
	 * reliably mark exit edges in practice): if no such path exists, the transition exits the loop.
	 */
	private boolean isLoopExitTransition(final STATE loopHead, final STATE succ) {
		return !canReach(succ, loopHead);
	}

	/**
	 * Simple BFS reachability check over internal transitions only (consistent with the "procedures inlined"
	 * assumption elsewhere in this class). TODO: extend to call/return once that assumption is lifted.
	 */
	private boolean canReach(final STATE from, final STATE target) {
		if (from.equals(target)) {
			return true;
		}
		final Set<STATE> visited = new HashSet<>();
		final Deque<STATE> worklist = new ArrayDeque<>();
		visited.add(from);
		worklist.add(from);
		while (!worklist.isEmpty()) {
			final STATE state = worklist.poll();
			for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(state)) {
				final STATE succ = t.getSucc();
				if (succ.equals(target)) {
					return true;
				}
				if (visited.add(succ)) {
					worklist.add(succ);
				}
			}
		}
		return false;
	}

	private boolean isLoopEntryLocation(final STATE state) {
		final IcfgLocation a = ((ISLPredicate) state).getProgramPoint();
		return a.getPayload().getAnnotations().containsKey(LoopEntryAnnotation.class.getName());
	}

	/**
	 * Finds every loop head of {@link #mAbstraction}. Zero loop heads is the legitimate loop-free-program case, not
	 * an error.
	 */
	private Set<STATE> findLoopHeads() {
		final Set<STATE> loopHeads = new LinkedHashSet<>();
		for (final STATE state : mAbstraction.getStates()) {
			if (isLoopEntryLocation(state)) {
				loopHeads.add(state);
			}
		}
		return loopHeads;
	}

	/**
	 * Evaluates a path expression (all paths between two automaton states) into one relational
	 * {@link UnmodifiableTransFormula}, native to {@link #mMgdScript} - or {@code null} if the expression describes
	 * no path at all ({@link EmptySet}, possibly nested inside a {@link Concatenation}/{@link Union}). {@code null}
	 * is the algebraic zero: concatenating with it is {@code null}, union-ing with it just returns the other side.
	 * Callers combining several alternative endpoints should treat {@code null} as "this endpoint contributes
	 * nothing" and skip it, rather than failing outright; callers with a single mandatory endpoint (the loop body)
	 * should treat it as an error.
	 * <p>
	 * The checkpoint-graph regions are guaranteed acyclic by construction (every loop head contributes no outgoing
	 * edges in the graph passed to {@link PathExpressionComputer}), so {@link Star} should never actually occur.
	 */
	private final class RegexToTransFormula implements IRegexVisitor<LETTER, UnmodifiableTransFormula, Void> {

		UnmodifiableTransFormula evaluate(final IRegex<LETTER> regex) {
			return regex.accept(this);
		}

		UnmodifiableTransFormula letterFormula(final LETTER letter) {
			if (mLetterCache.containsKey(letter)) {
				return mLetterCache.get(letter);
			}
			final UnmodifiableTransFormula result = letter.getTransformula();
			mLetterCache.put(letter, result);
			return result;
		}

		@Override
		public UnmodifiableTransFormula visit(final Union<LETTER> union, final Void argument) {
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
		public UnmodifiableTransFormula visit(final Concatenation<LETTER> concatenation, final Void argument) {
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
		public UnmodifiableTransFormula visit(final Star<LETTER> star, final Void argument) {
			throw new AssertionError("Unexpected cycle in checkpoint graph; non-nesting invariant violated");
		}

		@Override
		public UnmodifiableTransFormula visit(final Literal<LETTER> literal, final Void argument) {
			return letterFormula(literal.getLetter());
		}

		@Override
		public UnmodifiableTransFormula visit(final Epsilon<LETTER> epsilon, final Void argument) {
			return TransFormulaBuilder.getTrivialTransFormula(mMgdScript);
		}

		@Override
		public UnmodifiableTransFormula visit(final EmptySet<LETTER> emptySet, final Void argument) {
			// No path at all for this (sub-)expression. TODO: once calls are supported, this might mean "a path
			// exists but requires a call," not "no path" - for now (procedures assumed inlined) it genuinely
			// means unreachable via internal transitions.
			return null;
		}
	}

	/**
	 * A node of the checkpoint graph: program entry (INIT), a loop head, or the program's accepting/error states
	 * (FINAL). INIT and FINAL are virtual - each stands for a whole set of automaton states
	 * ({@code getInitialStates()}/{@code getFinalStates()}) rather than one - so this wraps a loop head's
	 * {@code STATE} together with two sentinel cases, giving every checkpoint a uniform key type for the edge map.
	 */
	public static final class Checkpoint<STATE> {
		private enum Kind {
			INIT, LOOP_HEAD, FINAL
		}

		private final Kind mKind;
		private final STATE mLoopHead;

		private Checkpoint(final Kind kind, final STATE loopHead) {
			mKind = kind;
			mLoopHead = loopHead;
		}

		// public: also constructed from outside this package by callers of CheckpointGraph's public getEdge/
		// getLoopBody API (e.g. traceabstraction.kinduction.KInduction), not just from within this package.
		public static <STATE> Checkpoint<STATE> init() {
			return new Checkpoint<>(Kind.INIT, null);
		}

		public static <STATE> Checkpoint<STATE> fin() {
			return new Checkpoint<>(Kind.FINAL, null);
		}

		public static <STATE> Checkpoint<STATE> loopHead(final STATE loopHead) {
			return new Checkpoint<>(Kind.LOOP_HEAD, loopHead);
		}

		public boolean isInit() {
			return mKind == Kind.INIT;
		}

		public boolean isFinal() {
			return mKind == Kind.FINAL;
		}

		public boolean isLoopHead() {
			return mKind == Kind.LOOP_HEAD;
		}

		public STATE getLoopHead() {
			if (mKind != Kind.LOOP_HEAD) {
				throw new IllegalStateException("Not a loop-head checkpoint: " + this);
			}
			return mLoopHead;
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
			return mKind == other.mKind && Objects.equals(mLoopHead, other.mLoopHead);
		}

		@Override
		public int hashCode() {
			return Objects.hash(mKind, mLoopHead);
		}

		@Override
		public String toString() {
			return mKind == Kind.LOOP_HEAD ? "loopHead(" + mLoopHead + ")" : mKind.toString();
		}
	}

	/**
	 * Immutable result: the checkpoint graph's loop-body formulas and inter-checkpoint edges, all native to the
	 * {@code targetMgdScript} given to {@link CheckpointGraphFormulaBuilder}'s constructor.
	 */
	public static final class CheckpointGraph<STATE> {
		private final Set<STATE> mLoopHeads;
		private final Map<STATE, UnmodifiableTransFormula> mLoopBodies;
		private final Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> mEdges;

		CheckpointGraph(final Set<STATE> loopHeads, final Map<STATE, UnmodifiableTransFormula> loopBodies,
				final Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> edges) {
			mLoopHeads = loopHeads;
			mLoopBodies = loopBodies;
			mEdges = edges;
		}

		public Set<STATE> getLoopHeads() {
			return mLoopHeads;
		}

		/** One pass through the loop at {@code loopHead} (loop head back to loop head). */
		public UnmodifiableTransFormula getLoopBody(final STATE loopHead) {
			return mLoopBodies.get(loopHead);
		}

		/** Every loop-free way of getting from checkpoint {@code from} to checkpoint {@code to}, or {@code null}. */
		public UnmodifiableTransFormula getEdge(final Checkpoint<STATE> from, final Checkpoint<STATE> to) {
			final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing = mEdges.get(from);
			return outgoing == null ? null : outgoing.get(to);
		}

		/**
		 * Every simple path from {@link Checkpoint#init()} to {@link Checkpoint#fin()} through the present edges,
		 * as an ordered checkpoint list starting with INIT and ending with FINAL. A single execution may visit only
		 * a subset of the program's loop heads, possibly several in sequence, and different branches may visit
		 * different subsets/orders - so this is a genuine enumeration, not a single fixed sequence.
		 */
		public List<List<Checkpoint<STATE>>> enumeratePaths() {
			final List<List<Checkpoint<STATE>>> result = new ArrayList<>();
			final Deque<Checkpoint<STATE>> current = new ArrayDeque<>();
			final Checkpoint<STATE> init = Checkpoint.init();
			current.addLast(init);
			final Set<Checkpoint<STATE>> visited = new HashSet<>();
			visited.add(init);
			enumeratePaths(init, current, visited, result);
			return result;
		}

		private void enumeratePaths(final Checkpoint<STATE> node, final Deque<Checkpoint<STATE>> current,
				final Set<Checkpoint<STATE>> visited, final List<List<Checkpoint<STATE>>> result) {
			if (node.isFinal()) {
				if (result.size() >= MAX_PATHS) {
					throw new UnsupportedOperationException("CheckpointGraphFormulaBuilder found more than "
							+ MAX_PATHS + " distinct INIT-to-FINAL paths through the checkpoint graph");
				}
				result.add(new ArrayList<>(current));
				return;
			}
			final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing = mEdges.get(node);
			if (outgoing == null) {
				return;
			}
			// Defensive visited-set per DFS branch: the checkpoint graph is provably acyclic (every loop head's
			// outgoing edges were suppressed while building it), but a revisit here is cheap to detect and would
			// indicate a real bug worth surfacing loudly rather than an infinite loop.
			for (final Checkpoint<STATE> next : outgoing.keySet()) {
				if (!visited.add(next)) {
					continue;
				}
				current.addLast(next);
				enumeratePaths(next, current, visited, result);
				current.removeLast();
				visited.remove(next);
			}
		}
	}
}
