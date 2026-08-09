package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.imc.LoopSegmentFormulaBuilder.LoopSegments;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

public class InterpolationBasedModelChecking<LETTER extends IAction, STATE> {

	/**
	 * Upper bound on how many times the loop body is unwound while searching for an inductive interpolant.
	 * Placeholder constant; not yet wired through a preference.
	 */
	private static final int MAX_K = 20;

	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final ManagedScript mMgdScript;
	protected final IMCLock mIMCLock = new IMCLock();
	protected final STATE mDummyEmptyStackState;

	// TODO: on SAT, a concrete witness path is not yet extracted; left unset. See run().
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
	 * The three region summaries (prefix / one loop-body pass / suffix), each covering <b>all</b> paths through
	 * their region, come from {@link LoopSegmentFormulaBuilder}. For k = 1, 2, ..., MAX_K: assert
	 * prefix &and; loop^k &and; suffix as SSA, named per region. If SAT, a real bug was found. If UNSAT, obtain the
	 * k+1 cut-point interpolants; if the newest one is already subsumed by the disjunction of the earlier ones, the
	 * loop-head reachable set has stabilized (a valid, sound stopping criterion since iterations 1..k were each
	 * individually confirmed infeasible already) and the program is safe.
	 */
	private void run() throws AutomataLibraryException {
		mMgdScript.lock(mIMCLock);

		final LoopSegments segments =
				new LoopSegmentFormulaBuilder<>(mServices, mLogger, mMainMgdScript, mMgdScript, mAbstraction).build();

		for (int k = 1; k <= MAX_K; k++) {
			mMgdScript.push(mIMCLock, 1);

			final List<UnmodifiableTransFormula> regions = new ArrayList<>();
			regions.add(segments.getPrefix());
			regions.addAll(Collections.nCopies(k, segments.getLoopBody()));
			regions.add(segments.getSuffix());

			final Term[] partition = assertRegionSequenceNamed(regions);
			final LBool sat = mMgdScript.checkSat(mIMCLock);

			if (sat == LBool.SAT) {
				mSafe = false;
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

	/**
	 * SSA-chains {@code regions} (already {@code mMgdScript}-native {@link UnmodifiableTransFormula}s, one per
	 * interpolation partition) into a sequence of named ({@code :named}) SMT assertions via
	 * {@link PredicateUtils#formulaWithIndexedVars} — region {@code s}'s inVars are renamed to index {@code s} and
	 * its genuinely-updated outVars to index {@code s + 1}, via a shared indexed-constant cache, so consecutive
	 * regions' matching in/out vars land on the same constant automatically. The {@code :named} constant for region
	 * {@code s} becomes {@code partition[s]} directly. Also refreshes {@link #mConstants2BoogieVar} so
	 * {@link #unSsaToRepresentativeFrame} can un-SSA the resulting interpolants.
	 *
	 * Assumes procedures are inlined (no oldvars / calling contexts to special-case).
	 */
	private Term[] assertRegionSequenceNamed(final List<UnmodifiableTransFormula> regions) {
		final Map<String, Term> indexedConstants = new HashMap<>();
		mConstants2BoogieVar = new HashMap<>();
		final Term[] partition = new Term[regions.size()];
		for (int s = 0; s < regions.size(); s++) {
			final UnmodifiableTransFormula region = regions.get(s);
			final int idxInVar = s;
			final int idxOutVar = s + 1;
			final Set<IProgramVar> assignedVars = new HashSet<>();
			final Term ssaFormula = PredicateUtils.formulaWithIndexedVars(region, idxInVar, idxOutVar, assignedVars,
					indexedConstants, mMgdScript.getScript());
			// Mirrors formulaWithIndexedVars' own constant choice per var exactly (oldvars use their stable default
			// constant instead of an indexed one) so mConstants2BoogieVar always maps the constant that actually
			// occurs in ssaFormula, not a freshly-minted one nobody references. Not expected to trigger while
			// procedures are assumed inlined, but cheap to keep correct in case an oldvar slips through.
			for (final IProgramVar pv : region.getInVars().keySet()) {
				final Term constant = pv.isOldvar() ? pv.getDefaultConstant()
						: PredicateUtils.getIndexedConstant(pv, idxInVar, indexedConstants, mMgdScript.getScript());
				mConstants2BoogieVar.put(constant, pv);
			}
			for (final IProgramVar pv : assignedVars) {
				final Term constant = pv.isOldvar() && !region.getAssignedVars().contains(pv) ? pv.getDefaultConstant()
						: PredicateUtils.getIndexedConstant(pv, idxOutVar, indexedConstants, mMgdScript.getScript());
				mConstants2BoogieVar.put(constant, pv);
			}
			partition[s] = assertNamed(ssaFormula);
		}
		return partition;
	}

	/**
	 * Asserts {@code term} under a fresh {@code :named} annotation and returns the SMT constant naming it, ready to
	 * be used as an entry of a {@link ManagedScript#getInterpolants} partition.
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
	 * ({@code j = 0..k}). If the newest layer is already subsumed by the union (disjunction) of all earlier layers,
	 * no further unwinding can discover new abstract states at the loop head: the union is an inductive invariant,
	 * and since iterations {@code 1..k} were each individually confirmed infeasible by the caller already, the
	 * program is safe.
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
