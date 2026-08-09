package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopExitAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.icfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TransferrerWithVariableCache;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Given a nested word automaton that represents a single-loop program, builds three {@link UnmodifiableTransFormula}s
 * summarizing <b>all</b> paths (not just one) before, inside, and after the loop: a prefix formula (initial states to
 * the loop head), a loop-body formula (one pass through the loop, loop head back to loop head), and a suffix formula
 * (the loop-exit transition to an accepting/error state).
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
	private final ManagedScript mTargetMgdScript;
	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final TransferrerWithVariableCache mTransferrer;
	private final Map<LETTER, UnmodifiableTransFormula> mLetterCache = new HashMap<>();

	public LoopSegmentFormulaBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript sourceMgdScript, final ManagedScript targetMgdScript,
			final INestedWordAutomaton<LETTER, STATE> abstraction) {
		mServices = services;
		mLogger = logger;
		mTargetMgdScript = targetMgdScript;
		mAbstraction = abstraction;
		mTransferrer = new TransferrerWithVariableCache(sourceMgdScript.getScript(), targetMgdScript);
	}

	/**
	 * Runs the single-loop check, then builds and returns the three region formulas, all native to the
	 * {@code targetMgdScript} passed to the constructor.
	 */
	public LoopSegments build() {
		final STATE loopHead = findLoopHead();

		Pair<LETTER, STATE> loopenter = null;
		Pair<LETTER, STATE> exit = null;
		// TODO: only internal transitions considered at the loop head; extend to call/return once the loop
		// condition itself may involve a call.
		for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(loopHead)) {
			if (isLoopExitTransition(t.getLetter())) {
				if (exit != null) {
					throw new UnsupportedOperationException(
							"LoopSegmentFormulaBuilder currently supports only a single loop-exit transition at the loop head");
				}
				exit = new Pair<>(t.getLetter(), t.getSucc());
			} else if (entersLoopBody(t.getLetter())) {
				if (loopenter != null) {
					throw new UnsupportedOperationException(
							"LoopSegmentFormulaBuilder currently supports only a single loop-entry transition at the loop head");
				}
				loopenter = new Pair<>(t.getLetter(), t.getSucc());
			} else {
				throw new AssertionError("unreachable: entersLoopBody is the negation of isLoopExitTransition");
			}
		}
		if (loopenter == null || exit == null) {
			throw new UnsupportedOperationException(
					"Could not find both a loop-entering and a loop-exiting transition at the loop head");
		}

		final Pair<LETTER, STATE> loopexit = exit;

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

		final PathExpressionComputer<STATE, LETTER> pathExprComputer = new PathExpressionComputer<>(graph);
		final RegexToTransFormula evaluator = new RegexToTransFormula();

		final UnmodifiableTransFormula prefix = combine(mAbstraction.getInitialStates().stream()
				.map(init -> evaluator.evaluate(pathExprComputer.exprBetween(init, loopHead)))
				.collect(Collectors.toList()), "prefix (no initial states?)");

		final UnmodifiableTransFormula loopBodyTail =
				evaluator.evaluate(pathExprComputer.exprBetween(loopenter.getSecond(), loopHead));
		final UnmodifiableTransFormula loopBody =
				sequential(evaluator.letterFormula(loopenter.getFirst()), loopBodyTail);

		final UnmodifiableTransFormula suffixTail = combine(mAbstraction.getFinalStates().stream()
				.map(fin -> evaluator.evaluate(pathExprComputer.exprBetween(loopexit.getSecond(), fin)))
				.collect(Collectors.toList()), "suffix (no accepting states?)");
		final UnmodifiableTransFormula suffix = sequential(evaluator.letterFormula(loopexit.getFirst()), suffixTail);

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
		return TransFormulaUtils.parallelComposition(mLogger, mServices, mTargetMgdScript, null, false, true,
				alternatives.toArray(new UnmodifiableTransFormula[0]));
	}

	private UnmodifiableTransFormula sequential(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mTargetMgdScript, false, false, false,
				SimplificationTechnique.NONE, List.of(first, second));
	}

	private boolean entersLoopBody(final LETTER letter) {
		final CodeBlock stmt = (CodeBlock) letter;
		if (stmt.getPayload().getAnnotations().containsKey(LoopExitAnnotation.class.getName())) {
			return false;
		}
		return true;
	}

	private boolean isLoopExitTransition(final LETTER letter) {
		final CodeBlock stmt = (CodeBlock) letter;
		return stmt.getPayload().getAnnotations().containsKey(LoopExitAnnotation.class.getName());
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
	 * {@link UnmodifiableTransFormula}, native to {@link #mTargetMgdScript}. Regions are guaranteed acyclic by
	 * construction (the loop head contributes no outgoing edges in the graph passed to {@link PathExpressionComputer}),
	 * so {@link Star} should never actually occur.
	 */
	private final class RegexToTransFormula implements IRegexVisitor<LETTER, UnmodifiableTransFormula, Void> {

		UnmodifiableTransFormula evaluate(final IRegex<LETTER> regex) {
			return regex.accept(this);
		}

		UnmodifiableTransFormula letterFormula(final LETTER letter) {
			return mLetterCache.computeIfAbsent(letter, l -> mTransferrer.transferTransFormula(l.getTransformula()));
		}

		@Override
		public UnmodifiableTransFormula visit(final Union<LETTER> union, final Void argument) {
			final UnmodifiableTransFormula first = evaluate(union.getFirst());
			final UnmodifiableTransFormula second = evaluate(union.getSecond());
			return TransFormulaUtils.parallelComposition(mLogger, mServices, mTargetMgdScript, null, false, true, first,
					second);
		}

		@Override
		public UnmodifiableTransFormula visit(final Concatenation<LETTER> concatenation, final Void argument) {
			final UnmodifiableTransFormula first = evaluate(concatenation.getFirst());
			final UnmodifiableTransFormula second = evaluate(concatenation.getSecond());
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
			return TransFormulaBuilder.getTrivialTransFormula(mTargetMgdScript);
		}

		@Override
		public UnmodifiableTransFormula visit(final EmptySet<LETTER> emptySet, final Void argument) {
			// TODO: once calls are supported, an internal-only EmptySet might mean "a path exists but requires
			// a call," not "no path."
			throw new UnsupportedOperationException("No purely-internal path found for this region"
					+ " - are all procedures inlined? TODO: support calls/returns in loop-segment regions.");
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

		public UnmodifiableTransFormula getSuffix() {
			return mSuffix;
		}
	}
}
