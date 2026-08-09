package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopExitAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.icfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedSsaBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class InterpolationBasedModelChecking<LETTER extends IAction, STATE> {

	/**
	 * Upper bound on how many times the loop body is unwound while searching for an inductive interpolant. Placeholder
	 * constant; not yet wired through a preference.
	 */
	private static final int MAX_K = 20;

	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final ManagedScript mMgdScript;
	protected final IMCLock mIMCLock = new IMCLock();
	protected final STATE mDummyEmptyStackState;

	NestedRun<LETTER, STATE> mCounterexample;

	// this stuff is needed only for asserting / ssa
	private final CfgSmtToolkit mCsToolkit;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private boolean mSolverReturnedUnknown;
	private boolean mSafe;

	// TC Solver setup
	TaCheckAndRefinementPreferences<?> mPrefs;
	TaskIdentifier mTaskIdentifier = null;
	private final InterpolModelCheckingWorkerThread mImcWorkerThread;
	private final ManagedScript mMainMgdScript;
	private final TAPreferences mPref;

	// naming for interpolation, and the representative (non-SSA'd) variable frame used to compare cut-point
	// interpolants obtained at different loop-unwinding depths
	private int mNameCounter;
	private final Map<IProgramVar, TermVariable> mRepresentativeVars = new HashMap<>();
	private Map<Term, IProgramVar> mConstants2BoogieVar;

	/**
	 *
	 * @param csToolkit
	 * @param logger
	 * @param services
	 * @param preferences
	 * @throws InterruptedException
	 * @throws AutomataLibraryException
	 *
	 */
	public InterpolationBasedModelChecking(final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences prefs, final CfgSmtToolkit csToolkit,
			final ManagedScript mainMgdScript, final INestedWordAutomaton<LETTER, STATE> abstraction,
			final TaskIdentifier taskIdentifier, final InterpolModelCheckingWorkerThread imcWorkerThread,
			final TAPreferences preferences) throws AutomataLibraryException, InterruptedException {
		mAbstraction = abstraction;
		mMainMgdScript = mainMgdScript;
		mDummyEmptyStackState = mAbstraction.getEmptyStackState();
		mCsToolkit = csToolkit;
		mLogger = logger;
		mServices = services;
		mTaskIdentifier = taskIdentifier;
		mPrefs = prefs;
		mImcWorkerThread = imcWorkerThread;
		mMgdScript = csToolkit.createFreshManagedScript(mServices, getSolverSetting(), "SymExec");
		mPref = preferences;
		run();
	}

	/**
	 * Runs bounded-unwinding Interpolation-Based Model Checking on a nested word automaton (path program or
	 * abstraction) that represents a program with exactly one loop.
	 *
	 * For k = 1, 2, ..., MAX_K: assert prefix &and; loop^k &and; suffix as SSA, named per position. If SAT, a real bug
	 * was found. If UNSAT, obtain the k+1 cut-point interpolants; if the newest one is already subsumed by the
	 * disjunction of the earlier ones, the loop-head reachable set has stabilized (a valid, sound stopping criterion
	 * since iterations 1..k were each individually confirmed infeasible already) and the program is safe.
	 */
	private void run() throws AutomataLibraryException {
		mMgdScript.lock(mIMCLock);

		final STATE loopHead = findLoopHead();
		final List<NestedRun<LETTER, STATE>> segments = buildBaseSegments(loopHead);
		final NestedRun<LETTER, STATE> prefix = segments.get(0);
		final NestedRun<LETTER, STATE> loopBody = segments.get(1);
		final NestedRun<LETTER, STATE> suffix = segments.get(2);
		final int prefixLen = prefix.getWord().length();
		final int loopLen = loopBody.getWord().length();

		for (int k = 1; k <= MAX_K; k++) {
			mMgdScript.push(mIMCLock, 1);

			NestedRun<LETTER, STATE> combined = prefix;
			for (int i = 0; i < k; i++) {
				combined = combined.concatenate(loopBody);
			}
			combined = combined.concatenate(suffix);

			final Term[] partition = assertFormulaNamed(combined, prefixLen, loopLen, k);
			final LBool sat = mMgdScript.checkSat(mIMCLock);

			if (sat == LBool.SAT) {
				mSafe = false;
				mCounterexample = combined;
				mMgdScript.pop(mIMCLock, 1);
				break;
			}
			if (sat == LBool.UNKNOWN) {
				mSolverReturnedUnknown = true;
				mSafe = false;
				mMgdScript.pop(mIMCLock, 1);
				break;
			}

			// UNSAT: extract the k+1 cut-point interpolants before popping the scope
			final Term[] interpolants = mMgdScript.getInterpolants(mIMCLock, partition);
			final IPredicate[] cutpointPreds = unSsaToRepresentativeFrame(interpolants);
			mMgdScript.pop(mIMCLock, 1);

			if (hasStabilized(cutpointPreds, k)) {
				mSafe = true;
				break;
			}
			if (k == MAX_K) {
				mSolverReturnedUnknown = true;
				mSafe = false;
			}
		}

		mMgdScript.unlock(mIMCLock);
		mLogger.info("is safe " + (mSafe && !mSolverReturnedUnknown));
		mLogger.info("solver returned unknown: " + mSolverReturnedUnknown);
	}

	private SolverSettings getSolverSetting() {
		// getInterpolants requires an interpolation-capable solver; Internal_SMTInterpol needs no external process
		// and supports interpolation natively.
		return SolverBuilder.constructSolverSettings();
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

	private boolean entersLoopBody(final LETTER letter) {
		final CodeBlock stmt = ((CodeBlock) letter);
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
		if (a.getPayload().getAnnotations().containsKey(LoopEntryAnnotation.class.getName())) {
			return true;
		}
		return false;
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
	 * Builds the three trace segments needed for IMC: the run from an initial state to {@code loopHead} (prefix), one
	 * pass through the loop body (loop head back to loop head), and the run from the loop head via the loop-exit
	 * transition to an accepting (error) state (suffix). Assumes the loop head has exactly one loop-entering and one
	 * loop-exiting internal transition (loop conditions are assume-statements, i.e. internal transitions).
	 */
	private List<NestedRun<LETTER, STATE>> buildBaseSegments(final STATE loopHead)
			throws AutomataOperationCanceledException {
		Pair<LETTER, STATE> enter = null;
		Pair<LETTER, STATE> exit = null;
		for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(loopHead)) {
			if (isLoopExitTransition(t.getLetter())) {
				if (exit != null) {
					throw new UnsupportedOperationException(
							"IMC currently supports only a single loop-exit transition at the loop head");
				}
				exit = new Pair<>(t.getLetter(), t.getSucc());
			} else {
				if (enter != null) {
					throw new UnsupportedOperationException(
							"IMC currently supports only a single loop-entry transition at the loop head");
				}
				enter = new Pair<>(t.getLetter(), t.getSucc());
			}
		}
		if (enter == null || exit == null) {
			throw new UnsupportedOperationException(
					"Could not find both a loop-entering and a loop-exiting transition at the loop head");
		}

		final AutomataLibraryServices services = new AutomataLibraryServices(mServices);

		final IsEmpty<LETTER, STATE> prefixSearch = new IsEmpty<>(services, mAbstraction,
				mAbstraction.getInitialStates(), Collections.emptySet(), Collections.singleton(loopHead));
		if (prefixSearch.getResult()) {
			throw new UnsupportedOperationException("Loop head is not reachable from an initial state");
		}
		final NestedRun<LETTER, STATE> prefix = prefixSearch.getNestedRun();

		final IsEmpty<LETTER, STATE> loopSearch = new IsEmpty<>(services, mAbstraction,
				Collections.singleton(enter.getSecond()), Collections.emptySet(), Collections.singleton(loopHead));
		if (loopSearch.getResult()) {
			throw new UnsupportedOperationException("Loop body does not lead back to the loop head");
		}
		final NestedRun<LETTER, STATE> loopBody = new NestedRun<LETTER, STATE>(loopHead, enter.getFirst(),
				NestedWord.INTERNAL_POSITION, enter.getSecond()).concatenate(loopSearch.getNestedRun());

		final IsEmpty<LETTER, STATE> suffixSearch = new IsEmpty<>(services, mAbstraction,
				Collections.singleton(exit.getSecond()), Collections.emptySet(),
				new HashSet<>(mAbstraction.getFinalStates()));
		if (suffixSearch.getResult()) {
			throw new UnsupportedOperationException("No accepting state is reachable after leaving the loop");
		}
		final NestedRun<LETTER, STATE> suffix = new NestedRun<LETTER, STATE>(loopHead, exit.getFirst(),
				NestedWord.INTERNAL_POSITION, exit.getSecond()).concatenate(suffixSearch.getNestedRun());

		return Arrays.asList(prefix, loopBody, suffix);
	}

	private NestedFormulas<LETTER, UnmodifiableTransFormula, IPredicate>
			createNestedFormulas(final NestedRun<LETTER, STATE> trace) {
		final NestedWord<LETTER> nw = trace.getWord();
		final BasicPredicateFactory bpf = new BasicPredicateFactory(mServices, mMgdScript, mCsToolkit.getSymbolTable());
		final BasicPredicate truePred = bpf.newPredicate(mMgdScript.getScript().term("true"));
		final BasicPredicate falsePred = bpf.newPredicate(mMgdScript.getScript().term("false"));
		final SortedMap<Integer, IPredicate> pendingContexts = new TreeMap<>();
		final NestedFormulas<LETTER, UnmodifiableTransFormula, IPredicate> rv = new DefaultTransFormulas<>(nw, truePred,
				falsePred, pendingContexts, mCsToolkit.getOldVarsAssignmentCache(), false);
		return rv;
	}

	/**
	 * Index (into the {@code k+2}-entry interpolation partition) of trace position {@code i}: {@code 0} = prefix,
	 * {@code 1..k} = the corresponding loop-copy, {@code k+1} = suffix.
	 */
	private static int segmentIndexForPosition(final int i, final int prefixLen, final int loopLen, final int k) {
		if (i < prefixLen) {
			return 0;
		}
		final int loopCopy = (i - prefixLen) / loopLen;
		if (loopCopy < k) {
			return 1 + loopCopy;
		}
		return 1 + k;
	}

	/**
	 * Creates the SSA and asserts it to the solver, one named ({@code :named}) assertion per position (required by
	 * {@link ManagedScript#getInterpolants}). Per-position names are grouped into {@code k+2} segments (prefix,
	 * {@code k} loop copies, suffix); returns one conjunction-of-names {@link Term} per segment, ready to be used as
	 * an interpolation partition. Also refreshes {@link #mConstants2BoogieVar} so the caller can un-SSA the resulting
	 * interpolants.
	 */
	private Term[] assertFormulaNamed(final NestedRun<LETTER, STATE> trace, final int prefixLen, final int loopLen,
			final int k) {
		final NestedFormulas<LETTER, UnmodifiableTransFormula, IPredicate> nestedFormulas = createNestedFormulas(trace);
		final NestedSsaBuilder<LETTER> nsb = new NestedSsaBuilder<>(mMgdScript, mCsToolkit, nestedFormulas, mLogger);
		final NestedFormulas<LETTER, Term, Term> ssa = nsb.getSsa();
		final TermTransferrer mainToWorker = new TermTransferrer(mMainMgdScript.getScript(), mMgdScript.getScript());

		final List<List<Term>> segmentNames = new ArrayList<>(k + 2);
		for (int s = 0; s < k + 2; s++) {
			segmentNames.add(new ArrayList<>());
		}

		for (int i = 0; i < trace.getWord().length(); i++) {
			final List<Term> names = segmentNames.get(segmentIndexForPosition(i, prefixLen, loopLen, k));
			if (trace.isCallPosition(i)) {
				names.add(assertNamed(mainToWorker.transform(ssa.getGlobalVarAssignment(i))));
				names.add(assertNamed(mainToWorker.transform(ssa.getLocalVarAssignment(i))));
				names.add(assertNamed(mainToWorker.transform(ssa.getOldVarAssignment(i))));
			} else {
				names.add(assertNamed(mainToWorker.transform(ssa.getFormulaFromNonCallPos(i))));
			}
		}

		mConstants2BoogieVar = nsb.getConstants2BoogieVar();

		final Term[] partition = new Term[k + 2];
		for (int s = 0; s < k + 2; s++) {
			partition[s] = SmtUtils.and(mMgdScript.getScript(), segmentNames.get(s));
		}
		return partition;
	}

	/**
	 * Asserts {@code term} under a fresh {@code :named} annotation and returns the SMT constant naming it, ready to be
	 * used as an entry of a {@link ManagedScript#getInterpolants} partition.
	 */
	private Term assertNamed(final Term term) {
		final String name = "imc_" + mNameCounter++;
		final Term named = mMgdScript.getScript().annotate(term, new Annotation(":named", name));
		mMgdScript.assertTerm(mIMCLock, named);
		return mMgdScript.getScript().term(name);
	}

	/**
	 * Maps every SSA constant back to a canonical, non-indexed {@link TermVariable} per program variable (cached in
	 * {@link #mRepresentativeVars}), so that cut-point interpolants obtained at different loop-copy positions become
	 * directly comparable formulas over the same variable frame.
	 */
	private IPredicate[] unSsaToRepresentativeFrame(final Term[] interpolants) {
		final Map<Term, Term> const2RepTv = new HashMap<>();
		for (final Map.Entry<Term, IProgramVar> entry : mConstants2BoogieVar.entrySet()) {
			final Term constant = entry.getKey();
			final TermVariable rep = mRepresentativeVars.computeIfAbsent(entry.getValue(),
					pv -> mMgdScript.constructFreshTermVariable(pv.toString(), constant.getSort()));
			const2RepTv.put(constant, rep);
		}
		final BasicPredicateFactory predicateFactory =
				new BasicPredicateFactory(mServices, mMgdScript, mCsToolkit.getSymbolTable());
		final IPredicate[] result = new IPredicate[interpolants.length];
		for (int i = 0; i < interpolants.length; i++) {
			final Term unlet = new FormulaUnLet().transform(interpolants[i]);
			final Term representative = PureSubstitution.apply(mMgdScript, const2RepTv, unlet);
			result[i] = predicateFactory.newPredicate(representative);
		}
		return result;
	}

	/**
	 * {@code cutpointPreds[j]} over-approximates the loop-head state after {@code j} loop iterations
	 * ({@code j = 0..k}). If the newest layer is already subsumed by the union (disjunction) of all earlier layers, no
	 * further unwinding can discover new abstract states at the loop head: the union is an inductive invariant, and
	 * since iterations {@code 1..k} were each individually confirmed infeasible by the caller already, the program is
	 * safe.
	 */
	private boolean hasStabilized(final IPredicate[] cutpointPreds, final int k) {
		final BasicPredicateFactory predicateFactory =
				new BasicPredicateFactory(mServices, mMgdScript, mCsToolkit.getSymbolTable());
		final List<IPredicate> earlierLayers = new ArrayList<>(k);
		for (int j = 0; j < k; j++) {
			earlierLayers.add(cutpointPreds[j]);
		}
		final IPredicate union = predicateFactory.or(earlierLayers);
		return isUnsat(cutpointPreds[k].getFormula(), SmtUtils.not(mMgdScript.getScript(), union.getFormula()));
	}

	private boolean isUnsat(final Term... conjuncts) {
		mMgdScript.push(mIMCLock, 1);
		for (final Term t : conjuncts) {
			mMgdScript.assertTerm(mIMCLock, t);
		}
		final LBool result = mMgdScript.checkSat(mIMCLock);
		mMgdScript.pop(mIMCLock, 1);
		return result == LBool.UNSAT;
	}

	/**
	 * Package private class used by IMC to lock the {@link ManagedScript}.
	 */
	static class IMCLock {
	}
}
