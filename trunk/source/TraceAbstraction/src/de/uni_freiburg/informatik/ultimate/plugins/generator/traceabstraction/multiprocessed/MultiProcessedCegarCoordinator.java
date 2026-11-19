/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed;

import java.time.Instant;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;
import java.util.OptionalLong;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.proofs.IProof;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.IFloydHoareAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateParsingWrapperScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.JsonCodec.ResultStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.JsonCodec.VerdictValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ParallelCounterexampleSearch;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerAutomatonDifference;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.MultiProcessComponent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;

/**
 * The COORDINATOR session kind: the CEGAR loop of the multi-process trace abstraction. It is the process counterpart
 * of {@code ParallelNwaCegarLoop} and shares its counterexample search ({@link ParallelCounterexampleSearch}) and its
 * difference with a worker's automaton ({@link WorkerAutomatonDifference}).
 *
 * The coordinator checks no trace itself and waits at no barrier. It keeps at most {@code taWorkers} jobs in flight:
 * it sends each counterexample as a {@code COUNTEREXAMPLE} and refines the abstraction with the
 * {@code INTERPOLANT_AUTOMATON} that comes back.
 * <ul>
 * <li>After each refinement it cancels the jobs whose word the abstraction no longer accepts, and it publishes the
 * abstraction as a new generation if it is smaller than the last one published (as the threaded workers take the
 * main abstraction if it is smaller than theirs).</li>
 * <li>A feasible counterexample is registered as UNSAFE. With "stop after first violation" the loop ends; otherwise it
 * refines with the error automaton.</li>
 * <li>An empty abstraction ends the loop with SAFE, the time limit with TIMEOUT, a lost TA session as
 * {@code handleCrashedWorker} does.</li>
 * </ul>
 * The verdict goes out after the loop, see {@link #publishVerdict}, once the proof is computed: the
 * {@code PROOF_ANNOTATION} strictly before {@code VERDICT TRUE}.
 *
 * @param <L>
 *            the letter type
 */
public final class MultiProcessedCegarCoordinator<L extends IIcfgTransition<?>> extends NwaCegarLoop<L> {

	private static final String ABSTRACTION_NAME = "abstraction";
	private static final String DECIDED_BY = MultiProcessComponent.COORDINATOR.name();

	/**
	 * A counterexample in flight.
	 */
	private static final class Job<L> {
		private final NestedRun<L, IPredicate> mRun;
		// null until the RESULT arrived
		private ResultStatus mResult;

		private Job(final NestedRun<L, IPredicate> run) {
			mRun = run;
		}
	}

	private final IExchange mExchange;
	private final LetterNaming<L> mLetters;
	private final LocationNaming mLocations;
	private final AtsCodec<L> mAts;
	private final ParallelCounterexampleSearch<L> mSearch;
	private final PathProgramCache<L> mProgramCache;
	private final PredicateParsingWrapperScript mParsingScript;
	private final PredicateUnifier mPredicateUnifier;
	private final Map<Long, Job<L>> mJobs = new LinkedHashMap<>();
	private final Set<Long> mCancelledJobs = new HashSet<>();
	private final int mTaWorkers;
	private int mLostTaSessions;
	private long mNextJob = 1;
	private long mGeneration;
	private int mPublishedSize;
	private int mRefinements;
	private NestedWord<L> mViolation;

	/**
	 * Writes {@code ready.json} with the fingerprint of the initial abstraction, before any work.
	 *
	 * @param exchange
	 *            the session directory; the coordinator keeps it until {@link #closeExchange()}
	 */
	public MultiProcessedCegarCoordinator(final DebugIdentifier name,
			final INestedWordAutomaton<L, IPredicate> initialAbstraction, final IIcfg<IcfgLocation> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<? extends IcfgLocation> errorLocs, final NwaHoareProofProducer<L> proofProducer,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement, final IExchange exchange) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, proofProducer,
				services, transitionClazz, stateFactoryForRefinement);
		mExchange = exchange;
		mTaWorkers = taPrefs.getNumTaWorkers();
		if (mTaWorkers < 1) {
			throw new IllegalArgumentException("A coordinator needs at least one TA worker, not " + mTaWorkers);
		}
		if (mProofUpdater != null && taPrefs.differenceSenwa()) {
			throw new UnsupportedOperationException(
					"Computing a Hoare annotation in the coordinator requires the NWA difference, not SENWA");
		}
		mLetters = new LetterNaming<>(initialAbstraction.getVpAlphabet());
		mLocations = new LocationNaming(rootNode);
		mAts = new AtsCodec<>(services, mLogger, mLetters);
		mSearch = new ParallelCounterexampleSearch<>(mLogger, taPrefs);
		mProgramCache = new PathProgramCache<>(mLogger);
		mParsingScript = new PredicateParsingWrapperScript(csToolkit);
		mPredicateUnifier = new PredicateUnifier(mLogger, services, csToolkit.getManagedScript(), predicateFactory,
				csToolkit.getSymbolTable(), SimplificationTechnique.SIMPLIFY_DDA);
		mGeneration = 0;
		mPublishedSize = initialAbstraction.size();
		MultiProcessSession.announceReady(exchange, MultiProcessComponent.COORDINATOR, services, mLogger, rootNode,
				initialAbstraction);
	}

	@Override
	protected void iterate() throws AutomataLibraryException {
		final long deadlineMillis = getServices().getProgressMonitorService().getDeadline();
		if (deadlineMillis <= 0) {
			throw new IllegalArgumentException("A COORDINATOR session needs a time limit (the toolchain timeout)");
		}
		final Instant deadline = Instant.ofEpochMilli(deadlineMillis);
		// the initial emptiness check found the first counterexample
		boolean freshAbstraction = true;
		if (mCounterexample != null) {
			dispatch((NestedRun<L, IPredicate>) mCounterexample);
			freshAbstraction = false;
		}
		mIteration = 1;
		while (true) {
			abortIfTimeout();
			while (mJobs.size() < mTaWorkers - mLostTaSessions) {
				final NestedRun<L, IPredicate> cex =
						mSearch.search(getServices(), mAbstraction, mStateFactoryForRefinement, !freshAbstraction);
				freshAbstraction = false;
				if (cex == null) {
					break;
				}
				dispatch(cex);
			}
			if (mJobs.isEmpty()) {
				// nothing in flight and no counterexample: the abstraction must be empty
				if (isAbstractionEmpty()) {
					mResultBuilder.addResultForAllRemaining(Result.SAFE);
					return;
				}
				throw new IllegalStateException(
						"No job in flight and no counterexample found, but the abstraction is not empty");
			}
			final Optional<ExchangeMessage> next;
			try {
				next = mExchange.take(deadline);
			} catch (final DeadlineExpiredException e) {
				mLogger.info("Coordinator reached its time limit with %s jobs in flight", mJobs.size());
				mResultBuilder.addResultForAllRemaining(Result.TIMEOUT);
				return;
			}
			if (next.isEmpty()) {
				mLogger.info("Coordinator was asked to shut down");
				mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
				return;
			}
			// as the threaded loop: handle every message that is there, then minimize once
			final int refinementsBefore = mRefinements;
			Optional<ExchangeMessage> message = next;
			while (message.isPresent()) {
				if (handle(message.get())) {
					return;
				}
				message = mExchange.poll();
			}
			if (mRefinements > refinementsBefore) {
				if (!mPref.minimizeAbstractionPerWorker()) {
					minimizeAbstractionIfEnabled();
				}
				cancelJobsNoLongerAccepted();
				publishIfSmaller();
				freshAbstraction = true;
			}
		}
	}

	/**
	 * @return true if the loop ends
	 */
	private boolean handle(final ExchangeMessage message) throws AutomataLibraryException {
		switch (message.type()) {
		case RESULT:
			return onResult(message);
		case INTERPOLANT_AUTOMATON:
			return onAutomaton(message);
		default:
			throw new IllegalArgumentException("A COORDINATOR does not accept " + message.type());
		}
	}

	private void dispatch(final NestedRun<L, IPredicate> run) {
		final long job = mNextJob++;
		mSearch.add(run);
		mProgramCache.addRun(run.getWord());
		final int pathProgramCount = mProgramCache.getPathProgramCount(run.getWord());
		final NestedWord<L> word = run.getWord();
		final WordCodec.EncodedWord encoded = WordCodec.encode(word, mLetters);
		mExchange.send(MessageType.COUNTEREXAMPLE, OptionalLong.of(job), OptionalLong.of(mGeneration),
				JsonCodec.encode(new JsonCodec.Counterexample(job, mGeneration, encoded.word(), encoded.nesting(),
						pathProgramCount)));
		mJobs.put(job, new Job<>(run));
		mLogger.info("Coordinator: job %s, a counterexample of length %s (generation %s, %s jobs in flight)", job,
				word.length(), mGeneration, mJobs.size());
	}

	/**
	 * @return true if the loop ends
	 */
	private boolean onResult(final ExchangeMessage message) {
		final JsonCodec.Result result = JsonCodec.decode(message.body(), JsonCodec.Result.class);
		final long jobId = result.job();
		final Job<L> job = liveJob(jobId, message);
		if (job == null) {
			return false;
		}
		if (job.mResult != null) {
			throw new IllegalArgumentException("Second RESULT for job " + jobId);
		}
		if (result.isSessionLost()) {
			return onSessionLost(jobId, job);
		}
		job.mResult = result.status();
		final NestedWord<L> word = job.mRun.getWord();
		switch (result.status()) {
		case UNSAT:
			return false;
		case SAT: {
			final NestedWord<L> reported =
					WordCodec.decode(new WordCodec.EncodedWord(result.word(), result.nesting()), mLetters);
			if (!reported.equals(word)) {
				throw new IllegalArgumentException("The SAT result of job " + jobId + " carries another word");
			}
			mLogger.info("Coordinator: job %s found a feasible counterexample", jobId);
			mResultBuilder.addResultForProgramExecution(Result.UNSAFE, programExecution(word), null, null);
			if (mViolation == null) {
				mViolation = word;
			}
			if (mPref.stopAfterFirstViolation()) {
				mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
				return true;
			}
			return false;
		}
		case UNKNOWN: {
			final UnprovabilityReason reason = new UnprovabilityReason(result.reason() == null
					? "unable to decide satisfiability of path constraint" : result.reason());
			mResultBuilder.addResultForProgramExecution(Result.UNKNOWN, programExecution(word), null, reason);
			mResultBuilder.addResult(errorLocation(job.mRun), Result.TIMEOUT, null, null, null);
			if (mPref.stopAfterFirstViolation()) {
				mResultBuilder.addResultForAllRemaining(Result.TIMEOUT);
				return true;
			}
			return false;
		}
		default:
			throw new AssertionError(result.status());
		}
	}

	/**
	 * A TA session was lost with this job, as {@code handleCrashedWorker} handles a crashed TA worker thread.
	 *
	 * @return true if the loop ends
	 */
	private boolean onSessionLost(final long jobId, final Job<L> job) {
		mJobs.remove(jobId);
		mSearch.forget(job.mRun);
		mLostTaSessions++;
		if (mPref.getRefinementStrategy() != RefinementStrategy.FOX) {
			mLogger.warn("Coordinator: the TA session of job %s was lost, reporting UNKNOWN to leave the time to the "
					+ "bit-precise analysis", jobId);
			mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
			return true;
		}
		mLogger.warn("Coordinator: the TA session of job %s was lost (%s of %s TA sessions lost)", jobId,
				mLostTaSessions, mTaWorkers);
		if (mLostTaSessions >= mTaWorkers) {
			mLogger.warn("Coordinator: no TA session is left, reporting UNKNOWN");
			mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
			return true;
		}
		return false;
	}

	/**
	 * @return true if the loop ends
	 */
	private boolean onAutomaton(final ExchangeMessage message) throws AutomataLibraryException {
		final long jobId = message.requireJob();
		final Job<L> job = liveJob(jobId, message);
		if (job == null) {
			return false;
		}
		if (job.mResult == null) {
			throw new IllegalArgumentException("INTERPOLANT_AUTOMATON of job " + jobId + " before its RESULT");
		}
		final NestedWordAutomaton<L, IPredicate> automaton = mAts.parseInterpolantAutomaton(message.body(),
				smt -> mPredicateUnifier.getOrConstructPredicate(TermParseUtils.parseTerm(mParsingScript, smt)),
				mPredicateFactoryInterpolantAutomata);
		// NwaCegarLoop has an AutomatonType of its own; the difference takes the one of AbstractCegarLoop
		final AbstractCegarLoop.AutomatonType type = job.mResult == ResultStatus.UNSAT
				? AbstractCegarLoop.AutomatonType.INTERPOLANT
				: AbstractCegarLoop.AutomatonType.ERROR;
		mLogger.info("Coordinator: refining with the %s automaton of job %s (%s states)", type, jobId,
				automaton.size());

		mCegarLoopBenchmark.announceNextIteration();
		mSearch.refinedWith(job.mRun);
		// Future work:
		assert !mPref.dumpOnlyReuseAutomata();
		assert mFaultLocalizationMode == RelevanceAnalysisMode.NONE;
		mAbstraction = WorkerAutomatonDifference.compute(getServices(), mLogger, mPref, mAbstraction, automaton, type,
				job.mRun.getWord(), mStateFactoryForRefinement, mPredicateFactoryInterpolantAutomata, mProofUpdater,
				mCegarLoopBenchmark).getResult();
		if (mPref.minimizeAbstractionPerWorker()) {
			minimizeAbstractionIfEnabled();
		}
		mJobs.remove(jobId);
		mRefinements++;
		mIteration++;
		mCegarLoopBenchmark.reportAbstractionSize(mAbstraction.size(), mIteration);

		if (mAbstraction.size() == 0 || isAbstractionEmpty()) {
			mLogger.info("Coordinator: the abstraction is empty after %s refinements", mRefinements);
			cancelAll();
			mResultBuilder.addResultForAllRemaining(Result.SAFE);
			return true;
		}
		// the emptiness check left its run in mCounterexample; the search runs again on the fresh abstraction
		mCounterexample = null;
		if (mRefinements >= mPref.maxIterations()) {
			mResultBuilder.addResultForAllRemaining(Result.USER_LIMIT_ITERATIONS);
			return true;
		}
		return false;
	}

	/**
	 * @return the job, or null if it was cancelled (a message that crossed the {@code CANCEL})
	 */
	private Job<L> liveJob(final long jobId, final ExchangeMessage message) {
		if (message.job().isPresent() && message.job().getAsLong() != jobId) {
			throw new IllegalArgumentException(message.type() + " file of job " + message.job().getAsLong()
					+ " contains job " + jobId);
		}
		final Job<L> job = mJobs.get(jobId);
		if (job == null) {
			if (mCancelledJobs.contains(jobId)) {
				mLogger.info("Coordinator: ignoring %s of cancelled job %s", message.type(), jobId);
				return null;
			}
			throw new IllegalArgumentException(message.type() + " for unknown job " + jobId);
		}
		return job;
	}

	private void cancelJobsNoLongerAccepted() throws AutomataLibraryException {
		for (final Map.Entry<Long, Job<L>> entry : new ArrayList<>(mJobs.entrySet())) {
			final NestedWord<L> word = entry.getValue().mRun.getWord();
			if (!new Accepts<>(new AutomataLibraryServices(getServices()), mAbstraction, word).getResult()) {
				cancel(entry.getKey());
			}
		}
	}

	private void cancelAll() {
		for (final Long job : new ArrayList<>(mJobs.keySet())) {
			cancel(job);
		}
	}

	private void cancel(final long jobId) {
		final Job<L> job = mJobs.remove(jobId);
		mSearch.forget(job.mRun);
		mCancelledJobs.add(jobId);
		mExchange.send(MessageType.CANCEL, OptionalLong.of(jobId), OptionalLong.empty(),
				JsonCodec.encode(new JsonCodec.Cancel(jobId)));
		mLogger.info("Coordinator: cancelled job %s, the abstraction no longer accepts its word", jobId);
	}

	private void publishIfSmaller() {
		if (mAbstraction.size() >= mPublishedSize) {
			return;
		}
		mGeneration++;
		mPublishedSize = mAbstraction.size();
		mExchange.send(MessageType.ABSTRACTION, OptionalLong.empty(), OptionalLong.of(mGeneration),
				mAts.printAbstraction(ABSTRACTION_NAME, mAbstraction, mLocations));
		mLogger.info("Coordinator: published abstraction generation %s with %s states", mGeneration,
				mPublishedSize);
	}

	private IProgramExecution<L, Term> programExecution(final NestedWord<L> word) {
		final IcfgProgramExecution<L> execution = TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(word);
		execution.setOriginCfgScript(mCsToolkit.getManagedScript());
		return execution;
	}

	private static <L extends IIcfgTransition<?>> IcfgLocation errorLocation(final NestedRun<L, IPredicate> run) {
		return run.getSymbol(run.getLength() - 2).getTarget();
	}

	/**
	 * Sends the verdict of the loop. For TRUE, the {@code PROOF_ANNOTATION} goes out first (if there is a proof), so
	 * that it has the lower sequence number; for FALSE the evidence is the first feasible counterexample.
	 *
	 * @param proof
	 *            the proof the loop produced, or null
	 */
	public void publishVerdict(final CegarLoopResult<L> result, final IProof proof) {
		final VerdictValue verdict;
		if (result.resultStream().anyMatch(r -> r == Result.UNSAFE)) {
			verdict = VerdictValue.FALSE;
		} else if (result.resultStream().allMatch(r -> r == Result.SAFE)) {
			verdict = VerdictValue.TRUE;
		} else {
			verdict = VerdictValue.UNKNOWN;
		}
		JsonCodec.Evidence evidence = new JsonCodec.Evidence(null, null, null);
		if (verdict == VerdictValue.TRUE && proof != null) {
			if (!(proof instanceof IFloydHoareAnnotation<?>)) {
				throw new UnsupportedOperationException("Unknown type of proof: " + proof.getClass());
			}
			@SuppressWarnings("unchecked")
			final IFloydHoareAnnotation<IcfgLocation> annotation = (IFloydHoareAnnotation<IcfgLocation>) proof;
			mExchange.send(MessageType.PROOF_ANNOTATION, OptionalLong.empty(), OptionalLong.of(mGeneration),
					JsonCodec.encode(new JsonCodec.ProofAnnotation(mGeneration, invariants(annotation))));
		} else if (verdict == VerdictValue.FALSE) {
			if (mViolation == null) {
				throw new IllegalStateException("UNSAFE without a feasible counterexample");
			}
			final WordCodec.EncodedWord word = WordCodec.encode(mViolation, mLetters);
			evidence = new JsonCodec.Evidence(word.word(), word.nesting(), null);
		}
		mExchange.send(MessageType.VERDICT, OptionalLong.empty(), OptionalLong.empty(),
				JsonCodec.encode(new JsonCodec.Verdict(verdict, DECIDED_BY, evidence)));
		mLogger.info("Coordinator: verdict %s after %s refinements", verdict, mRefinements);
	}

	private TreeMap<String, String> invariants(final IFloydHoareAnnotation<IcfgLocation> annotation) {
		final TreeMap<String, String> result = new TreeMap<>();
		for (final Map<?, ? extends IcfgLocation> procedure : mIcfg.getProgramPoints().values()) {
			for (final IcfgLocation loc : procedure.values()) {
				final IPredicate invariant = annotation.getAnnotation(loc);
				if (invariant != null) {
					result.put(mLocations.name(loc), invariant.getFormula().toStringDirect());
				}
			}
		}
		return result;
	}

	/**
	 * Sends an {@code EXCEPTION} for a failure of the session, if it still can.
	 */
	public void reportException(final Throwable failure) {
		MultiProcessSession.reportException(mExchange, MultiProcessComponent.COORDINATOR, failure);
	}

	/**
	 * Closes the session directory.
	 */
	public void closeExchange() {
		mExchange.close();
	}
}
