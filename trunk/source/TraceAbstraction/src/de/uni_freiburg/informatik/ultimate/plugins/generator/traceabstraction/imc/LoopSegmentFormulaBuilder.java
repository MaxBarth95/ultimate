package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
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
 * Given a nested word automaton that represents a single-loop program, builds three {@link UnmodifiableTransFormula}s
 * summarizing <b>all</b> paths (not just one) before, inside, and after the loop: a prefix formula (initial states to
 * the loop head), a loop-body formula (one pass through the loop, loop head back to loop head), and a suffix formula
 * (every way execution can reach an accepting/error state after some number of complete iterations: via the normal
 * loop-exit transition, or directly from within the loop body without completing the iteration, e.g. a failing
 * assertion).
 * <p>
 * Assumes procedures are already inlined: only internal transitions are considered, both at the loop head itself and
 * throughout the three regions. TODO: support call/return once that assumption is lifted.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class LoopSegmentFormulaBuilder<LETTER extends IAction, STATE> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	// Plain term transfer only - IProgramVar identity is never translated (see transferLetterFormula), matching how
	// NestedSsaBuilder's own VariableVersioneer moves terms between scripts elsewhere in this codebase.
	private final Map<LETTER, UnmodifiableTransFormula> mLetterCache = new HashMap<>();

	public LoopSegmentFormulaBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final INestedWordAutomaton<LETTER, STATE> abstraction) {
		mServices = services;
		mLogger = logger;
		mMgdScript = mgdScript;
		mAbstraction = abstraction;
	}

	/**
	 * Runs the single-loop check, then builds and returns the three region formulas, all native to the
	 * {@code targetMgdScript} passed to the constructor.
	 */
	public LoopSegments build() {
		final STATE loopHead = findLoopHead();
		mLogger.info("IMC: found loop head %s", loopHead);

		Pair<LETTER, STATE> enter = null;
		Pair<LETTER, STATE> exit = null;
		// TODO: only internal transitions considered at the loop head; extend to call/return once the loop
		// condition itself may involve a call.
		for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(loopHead)) {
			if (isLoopExitTransition(loopHead, t.getSucc())) {
				if (exit != null) {
					throw new UnsupportedOperationException(
							"LoopSegmentFormulaBuilder currently supports only a single loop-exit transition at the loop head");
				}
				exit = new Pair<>(t.getLetter(), t.getSucc());
			} else {
				if (enter != null) {
					throw new UnsupportedOperationException(
							"LoopSegmentFormulaBuilder currently supports only a single loop-entry transition at the loop head");
				}
				enter = new Pair<>(t.getLetter(), t.getSucc());
			}
		}

		if (enter == null || exit == null) {
			throw new UnsupportedOperationException(
					"Could not find both a loop-entering and a loop-exiting transition at the loop head");
		}
		final Pair<LETTER, STATE> loopenter = enter;
		final Pair<LETTER, STATE> loopexit = exit;
		mLogger.info("IMC: loop-entering transition %s -> %s", loopenter.getFirst(), loopenter.getSecond());
		mLogger.info("IMC: loop-exiting transition %s -> %s", loopexit.getFirst(), loopexit.getSecond());

		final GenericLabeledGraph<STATE, LETTER> graph = new GenericLabeledGraph<>();
		// TODO: only internal transitions are added to the graph; extend to call/return edges once procedures
		// aren't assumed pre-inlined.
		for (final STATE state : mAbstraction.getStates()) {
			graph.addNode(state);
			if (state.equals(loopHead)) {
				// loopHead contributes no outgoing edges here: the automaton's unique cycle point (guaranteed by
				// the single-loop check above) is suppressed so every path-expression query below is Star-free.
				continue;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(state)) {
				graph.addEdge(state, t.getLetter(), t.getSucc());
			}
		}
		mLogger.info("IMC: built loop-segment graph with %d states and %d edges (loop head excluded from outgoing)",
				graph.getNodes().size(), graph.getEdges().size());

		mLogger.info("IMC: constructing PathExpressionComputer");
		final PathExpressionComputer<STATE, LETTER> pathExprComputer = new PathExpressionComputer<>(graph);
		mLogger.info("IMC: PathExpressionComputer constructed");
		final RegexToTransFormula evaluator = new RegexToTransFormula();

		final List<UnmodifiableTransFormula> prefixAlternatives = new ArrayList<>();
		for (final STATE init : mAbstraction.getInitialStates()) {
			mLogger.info("IMC: prefix - computing exprBetween(%s, loopHead)", init);
			final var regex = pathExprComputer.exprBetween(init, loopHead);
			mLogger.info("IMC: prefix - exprBetween done, evaluating regex to a formula");
			final UnmodifiableTransFormula tf = evaluator.evaluate(regex);
			mLogger.info("IMC: prefix - regex for initial state %s evaluated (null=%b)", init, tf == null);
			if (tf != null) {
				prefixAlternatives.add(tf);
			}
		}
		final UnmodifiableTransFormula prefix =
				combine(prefixAlternatives, "No initial state can reach the loop head via purely-internal transitions");
		mLogger.info("IMC: prefix formula built");

		mLogger.info("IMC: loop-body - computing exprBetween(enterSucc, loopHead)");
		final var loopBodyTailRegex = pathExprComputer.exprBetween(loopenter.getSecond(), loopHead);
		mLogger.info("IMC: loop-body - exprBetween done, evaluating regex to a formula");
		final UnmodifiableTransFormula loopBodyTail = evaluator.evaluate(loopBodyTailRegex);
		if (loopBodyTail == null) {
			throw new UnsupportedOperationException(
					"Loop-entering transition does not lead back to the loop head via purely-internal transitions");
		}
		mLogger.info("IMC: loop-body - tail evaluated, combining with enter-letter formula");
		final UnmodifiableTransFormula loopBody =
				sequential(evaluator.letterFormula(loopenter.getFirst()), loopBodyTail);
		mLogger.info("IMC: loop-body formula built");

		// An accepting state can be reached after k full iterations two structurally different ways: (1) take the
		// exit edge, then reach it through the rest of the program ("normal exit"), or (2) take the enter edge to
		// start iteration k+1, but branch directly to an accepting state instead of completing the iteration and
		// returning to the loop head (e.g. an assertion inside the loop body). Both are gathered into one
		// alternatives list and combined with a single combine() call, so this only fails if *neither* route can
		// reach *any* accepting state.
		final List<UnmodifiableTransFormula> badEndingAlternatives = new ArrayList<>();
		for (final STATE fin : mAbstraction.getFinalStates()) {
			mLogger.info("IMC: suffix - computing exit route exprBetween(exitSucc, %s)", fin);
			final var exitRegex = pathExprComputer.exprBetween(loopexit.getSecond(), fin);
			mLogger.info("IMC: suffix - exit route exprBetween done, evaluating");
			final UnmodifiableTransFormula exitTail = evaluator.evaluate(exitRegex);
			mLogger.info("IMC: suffix - exit route for final state %s evaluated (null=%b)", fin, exitTail == null);
			if (exitTail != null) {
				badEndingAlternatives.add(sequential(evaluator.letterFormula(loopexit.getFirst()), exitTail));
			}
		}
		for (final STATE fin : mAbstraction.getFinalStates()) {
			mLogger.info("IMC: suffix - computing mid-loop route exprBetween(enterSucc, %s)", fin);
			final var midLoopRegex = pathExprComputer.exprBetween(loopenter.getSecond(), fin);
			mLogger.info("IMC: suffix - mid-loop route exprBetween done, evaluating");
			final UnmodifiableTransFormula midLoopTail = evaluator.evaluate(midLoopRegex);
			mLogger.info("IMC: suffix - mid-loop route for final state %s evaluated (null=%b)", fin,
					midLoopTail == null);
			if (midLoopTail != null) {
				badEndingAlternatives.add(sequential(evaluator.letterFormula(loopenter.getFirst()), midLoopTail));
			}
		}
		mLogger.info("IMC: suffix - combining %d alternative(s)", badEndingAlternatives.size());
		final UnmodifiableTransFormula suffix = combine(badEndingAlternatives,
				"No accepting state is reachable from the loop, neither via the exit transition nor from within the loop body");
		mLogger.info("IMC: suffix (exit-or-mid-loop-error) formula built from %d alternative(s)",
				badEndingAlternatives.size());

		return new LoopSegments(prefix, loopBody, suffix);
	}

	private UnmodifiableTransFormula combine(final List<UnmodifiableTransFormula> alternatives,
			final String emptyMessage) {
		if (alternatives.isEmpty()) {
			throw new UnsupportedOperationException(emptyMessage);
		}
		if (alternatives.size() == 1) {
			return alternatives.get(0);
		}
		mLogger.info("IMC: combine - calling parallelComposition on %d alternatives", alternatives.size());
		final UnmodifiableTransFormula result = TransFormulaUtils.parallelComposition(mLogger, mServices, mMgdScript,
				null, false, true, alternatives.toArray(new UnmodifiableTransFormula[0]));
		mLogger.info("IMC: combine - parallelComposition done");
		return result;
	}

	private UnmodifiableTransFormula sequential(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
		mLogger.info("IMC: sequential - calling sequentialComposition");
		final UnmodifiableTransFormula result = TransFormulaUtils.sequentialComposition(mLogger, mServices, mMgdScript,
				false, false, false, SimplificationTechnique.NONE, List.of(first, second));
		mLogger.info("IMC: sequential - sequentialComposition done");
		return result;
	}

	/**
	 * Diagnostic-only: crude term size (distinct-subterm count via string length as a cheap proxy) so a hang here can
	 * be told apart from a hang caused by a pathologically large formula.
	 */
	private static int termSize(final Term term) {
		return term.toStringDirect().length();
	}

	/**
	 * A transition out of the loop head is a "loop exit" if, after taking it, the loop head can no longer be reached
	 * again — i.e. it leaves the loop's cycle for good. Determined by exploring the automaton for a path from
	 * {@code succ} back to {@code loopHead} rather than relying on a {@code LoopExitAnnotation} (which does not
	 * reliably mark exit edges in practice): if no such path exists, the transition exits the loop.
	 */
	private boolean isLoopExitTransition(final STATE loopHead, final STATE succ) {
		return !canReach(succ, loopHead);
	}

	/**
	 * Simple BFS reachability check over internal transitions only (consistent with the "procedures inlined" assumption
	 * elsewhere in this class). TODO: extend to call/return once that assumption is lifted.
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
	 * Finds the unique loop-head location of {@link #mAbstraction}. IMC currently only supports programs with exactly
	 * one loop.
	 */
	private STATE findLoopHead() {
		final Set<STATE> loopHeads = new HashSet<>();
		for (final STATE state : mAbstraction.getStates()) {
			if (isLoopEntryLocation(state)) {
				loopHeads.add(state);
			}
		}
		if (loopHeads.size() != 1) {
			throw new UnsupportedOperationException(
					"IMC currently supports exactly one loop, found " + loopHeads.size());
		}
		return loopHeads.iterator().next();
	}

	/**
	 * Evaluates a path expression (all paths between two automaton states) into one relational
	 * {@link UnmodifiableTransFormula}, native to {@link #mTargetMgdScript} — or {@code null} if the expression
	 * describes no path at all ({@link EmptySet}, possibly nested inside a {@link Concatenation}/{@link Union}).
	 * {@code null} is the algebraic zero: concatenating with it is {@code null}, union-ing with it just returns the
	 * other side. Callers combining several alternative endpoints (multiple initial/final states) should treat
	 * {@code null} as "this endpoint contributes nothing" and skip it, rather than failing outright; callers with a
	 * single mandatory endpoint (the loop body) should treat it as an error.
	 * <p>
	 * Regions are guaranteed acyclic by construction (the loop head contributes no outgoing edges in the graph passed
	 * to {@link PathExpressionComputer}), so {@link Star} should never actually occur.
	 */
	private final class RegexToTransFormula implements IRegexVisitor<LETTER, UnmodifiableTransFormula, Void> {

		UnmodifiableTransFormula evaluate(final IRegex<LETTER> regex) {
			return regex.accept(this);
		}

		UnmodifiableTransFormula letterFormula(final LETTER letter) {
			if (mLetterCache.containsKey(letter)) {
				mLogger.info("IMC: letterFormula - cache hit for letter %s", letter);
				return mLetterCache.get(letter);
			}
			mLogger.info("IMC: letterFormula - cache miss for letter %s, transferring", letter);
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
			throw new AssertionError("Unexpected cycle in loop-segment graph; single-loop invariant violated");
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
	 * Immutable result: the three region summaries, all native to the {@code targetMgdScript} given at construction.
	 */
	public static final class LoopSegments {
		private final UnmodifiableTransFormula mPrefix;
		private final UnmodifiableTransFormula mLoopBody;
		private final UnmodifiableTransFormula mSuffix;

		LoopSegments(final UnmodifiableTransFormula prefix, final UnmodifiableTransFormula loopBody,
				final UnmodifiableTransFormula suffix) {
			mPrefix = prefix;
			mLoopBody = loopBody;
			mSuffix = suffix;
		}

		public UnmodifiableTransFormula getPrefix() {
			return mPrefix;
		}

		public UnmodifiableTransFormula getLoopBody() {
			return mLoopBody;
		}

		/**
		 * Every way execution can reach an accepting/error state after some number of complete loop iterations: taking
		 * the normal exit transition and reaching it via the rest of the program, <em>or</em> starting another
		 * iteration but branching directly to an accepting state instead of completing it (e.g. a failing assertion
		 * inside the loop body).
		 */
		public UnmodifiableTransFormula getSuffix() {
			return mSuffix;
		}
	}
}
