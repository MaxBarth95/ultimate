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

import java.time.Duration;
import java.time.Instant;
import java.util.Collections;
import java.util.HashSet;
import java.util.Optional;
import java.util.OptionalLong;
import java.util.Set;
import java.util.concurrent.atomic.AtomicReference;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.JsonCodec.ResultStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.RetirementTimer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TaJobProcessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TaJobProcessor.Feasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TaJobProcessor.RefinementAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TaskScopedServices;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.MultiProcessComponent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

/**
 * The TA_WORKER session kind: checks the counterexamples the coordinator sends and returns the automata it refines
 * with. It is the process counterpart of {@code CegarNwaWorkerThread} and shares its work, {@link TaJobProcessor}.
 *
 * It reads {@code in/} in order:
 * <ul>
 * <li>{@code ABSTRACTION}: installs the abstraction if its generation is newer than the installed one. Generation 0 is
 * the session's own initial abstraction.</li>
 * <li>{@code COUNTEREXAMPLE}: rebuilds the run of the word through the installed abstraction, checks it, and sends
 * {@code RESULT} and then {@code INTERPOLANT_AUTOMATON}, both with the job and the generation it used. The result
 * goes out before the automaton is built, so that a failure while building it cannot lose a feasible
 * counterexample.</li>
 * <li>{@code CANCEL}: stops the job if it is running, and skips it if it has not started. A {@code CANCEL} that
 * arrives while a job runs is noticed by a watcher thread.</li>
 * <li>{@code in/shutdown}: ends the session.</li>
 * </ul>
 * Reaching the time limit of the toolchain ends the session normally. Any other failure throws.
 *
 * @param <L>
 *            the letter type
 */
public final class TaWorkerSession<L extends IIcfgTransition<?>> {

	private static final Duration STOP_WATCH_INTERVAL = Duration.ofSeconds(1);
	private static final String ABSTRACTION_NAME = "abstraction";
	private static final String AUTOMATON_NAME = "interpolantAutomaton";

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IExchange mExchange;
	private final LetterNaming<L> mLetters;
	private final LocationNaming mLocations;
	private final AtsCodec<L> mAts;
	private final PredicateFactory mPredicateFactory;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	private final TaJobProcessor<L> mProcessor;
	private final Set<Long> mCancelledJobs = new HashSet<>();
	private final SessionStatistics mStatistics;
	private INestedWordAutomaton<L, IPredicate> mAbstraction;
	private long mGeneration;

	/**
	 * @param services
	 *            the services of the toolchain
	 * @param logger
	 *            the logger
	 * @param prefs
	 *            the trace abstraction settings
	 * @param icfg
	 *            the program
	 * @param exchange
	 *            the exchange, after {@code ready.json} was written
	 * @param predicateFactory
	 *            the predicate factory of the initial abstraction
	 * @param initialAbstraction
	 *            the initial abstraction, generation 0
	 * @param transitionClazz
	 *            the letter class
	 * @param taskIdentifier
	 *            the identifier of this analysis, for file names of dumps
	 */
	public TaWorkerSession(final IUltimateServiceProvider services, final ILogger logger, final TAPreferences prefs,
			final IIcfg<IcfgLocation> icfg, final IExchange exchange, final PredicateFactory predicateFactory,
			final INestedWordAutomaton<L, IPredicate> initialAbstraction, final Class<L> transitionClazz,
			final TaskIdentifier taskIdentifier) {
		mServices = services;
		mLogger = logger;
		mExchange = exchange;
		mLetters = new LetterNaming<>(initialAbstraction.getVpAlphabet());
		mLocations = new LocationNaming(icfg);
		mAts = new AtsCodec<>(services, logger, mLetters);
		mPredicateFactory = predicateFactory;
		mAbstraction = initialAbstraction;
		mGeneration = 0;
		mStatistics = new SessionStatistics(MultiProcessComponent.TA_WORKER, prefs.getMultiProcessSessionId());
		mStatistics.declare("jobs", "jobsUnsat", "jobsSat", "jobsUnknown", "jobsSkipped", "jobsStopped",
				"abstractionsInstalled", "traceCheckTimeMs", "automatonTimeMs", "maxJobTimeMs");

		// as ParallelNwaCegarLoop sets up a TA worker thread, but on the main script: the process has it alone
		final CfgSmtToolkit toolkit = icfg.getCfgSmtToolkit();
		mPredicateFactoryInterpolantAutomata =
				new PredicateFactoryForInterpolantAutomata(toolkit.getManagedScript(), predicateFactory, false);
		final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(services,
				toolkit.getManagedScript(), predicateFactory, false, Collections.emptySet());
		final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs = new TaCheckAndRefinementPreferences<>(
				services, prefs, prefs.interpolation(), prefs.getSimplificationTechnique(), toolkit, predicateFactory,
				icfg);
		final boolean coordinatorComputesProof = prefs.getHoareSettings().computeHoareAnnotation();
		mProcessor = new TaJobProcessor<>(logger, prefs, services, toolkit, predicateFactory,
				taCheckAndRefinementPrefs, mPredicateFactoryInterpolantAutomata, stateFactoryForRefinement,
				coordinatorComputesProof, transitionClazz, new PathProgramCache<>(logger), taskIdentifier);
	}

	/**
	 * @return the statistics of this session, for {@code out/statistics.json}
	 */
	public SessionStatistics getStatistics() {
		return mStatistics;
	}

	/**
	 * Works on the messages of {@code in/} until the session is asked to shut down or reaches its time limit.
	 *
	 * @return how the session ended
	 */
	public SessionStatistics.End run() {
		final long deadlineMillis = mServices.getProgressMonitorService().getDeadline();
		if (deadlineMillis <= 0) {
			throw new IllegalArgumentException("A TA_WORKER session needs a time limit (the toolchain timeout)");
		}
		final Instant deadline = Instant.ofEpochMilli(deadlineMillis);
		int jobs = 0;
		while (true) {
			final Optional<ExchangeMessage> next;
			try {
				next = mExchange.take(deadline);
			} catch (final DeadlineExpiredException e) {
				mLogger.info("TA worker reached its time limit after " + jobs + " jobs");
				return SessionStatistics.End.TIME_LIMIT;
			}
			if (next.isEmpty()) {
				mLogger.info("TA worker shuts down after " + jobs + " jobs");
				return SessionStatistics.End.SHUTDOWN;
			}
			final ExchangeMessage message = next.get();
			switch (message.type()) {
			case ABSTRACTION:
				installAbstraction(message);
				break;
			case COUNTEREXAMPLE:
				if (!runJob(message)) {
					return mExchange.isShutdownRequested() ? SessionStatistics.End.SHUTDOWN
							: SessionStatistics.End.TIME_LIMIT;
				}
				jobs++;
				break;
			case CANCEL:
				mCancelledJobs.add(JsonCodec.decode(message.body(), JsonCodec.Cancel.class).job());
				break;
			default:
				throw new IllegalArgumentException("A TA_WORKER does not accept " + message.type());
			}
		}
	}

	private void installAbstraction(final ExchangeMessage message) {
		final long generation = message.requireGeneration();
		if (generation <= mGeneration) {
			mLogger.info("Ignoring abstraction generation %s, generation %s is installed", generation, mGeneration);
			return;
		}
		final NestedWordAutomaton<L, IPredicate> abstraction =
				mAts.parseAbstraction(message.body(), mLocations, mPredicateFactory::newDontCarePredicate,
						mPredicateFactoryInterpolantAutomata);
		mLogger.info("Installed abstraction generation %s with %s states", generation, abstraction.size());
		mStatistics.increment("abstractionsInstalled");
		mAbstraction = abstraction;
		mGeneration = generation;
	}

	/**
	 * @return false if the session must end (time limit or shutdown during the job)
	 */
	private boolean runJob(final ExchangeMessage message) {
		final JsonCodec.Counterexample cex = JsonCodec.decode(message.body(), JsonCodec.Counterexample.class);
		final long job = cex.job();
		if (message.job().isPresent() && message.job().getAsLong() != job) {
			throw new IllegalArgumentException(
					"Counterexample file of job " + message.job().getAsLong() + " contains job " + job);
		}
		if (mCancelledJobs.remove(job)) {
			mLogger.info("Skipping job %s, it was cancelled before it started", job);
			mStatistics.increment("jobsSkipped");
			return true;
		}
		mStatistics.increment("jobs");
		final long jobStart = System.nanoTime();
		final NestedWord<L> word = WordCodec.decode(new WordCodec.EncodedWord(cex.word(), cex.nesting()), mLetters);
		final NestedRun<L, IPredicate> run = RunReplay.replay(mAbstraction, word);
		// as the threaded worker: the count of this check is added again by the strategy
		mProcessor.getPathProgramCache().setPathProgramCount(word, cex.pathProgramCount() - 1);
		final long generation = mGeneration;
		mLogger.info("Job %s: checking a counterexample of length %s against generation %s", job, word.length(),
				generation);

		final RetirementTimer stopTimer = new RetirementTimer(mServices.getProgressMonitorService());
		final TaskScopedServices jobServices = new TaskScopedServices(
				mServices.getProgressMonitorService().registerChildTimer(mServices, stopTimer));
		final AtomicReference<Throwable> watcherFailure = new AtomicReference<>();
		final Thread watcher = startStopWatcher(job, stopTimer, watcherFailure);
		try {
			final Feasibility<L> feasibility;
			try {
				feasibility = mProcessor.checkFeasibility(jobServices, run, mAbstraction, Math.toIntExact(job),
						stopTimer::isRetired);
			} catch (final ToolchainCanceledException e) {
				return endStoppedJob(job, generation, stopTimer, e);
			} finally {
				mStatistics.add("traceCheckTimeMs", (System.nanoTime() - jobStart) / 1_000_000);
			}
			final long automatonStart = System.nanoTime();
			sendResult(job, generation, feasibility, word);
			final RefinementAutomaton<L> automaton;
			try {
				automaton = mProcessor.constructAutomaton(jobServices, feasibility);
			} catch (final ToolchainCanceledException e) {
				return endStoppedJob(job, generation, stopTimer, e);
			} catch (final AutomataOperationCanceledException e) {
				// a stop during the difference comes as this subclass of AutomataLibraryException
				return endStoppedJob(job, generation, stopTimer, e);
			} catch (final AutomataLibraryException e) {
				throw new IllegalStateException("Job " + job + ": cannot build the automaton", e);
			} finally {
				mStatistics.add("automatonTimeMs", (System.nanoTime() - automatonStart) / 1_000_000);
			}
			final NestedWordAutomaton<L, IPredicate> explored = ExploredAutomaton.copy(
					new AutomataLibraryServices(jobServices), automaton.automaton(),
					mPredicateFactoryInterpolantAutomata);
			mExchange.send(MessageType.INTERPOLANT_AUTOMATON, OptionalLong.of(job), OptionalLong.of(generation),
					mAts.printInterpolantAutomaton(AUTOMATON_NAME, explored));
			mLogger.info("Job %s: sent a %s automaton with %s states", job, automaton.type(), explored.size());
			return true;
		} finally {
			watcher.interrupt();
			try {
				watcher.join();
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
			jobServices.destroyAll(mLogger);
			mStatistics.max("maxJobTimeMs", (System.nanoTime() - jobStart) / 1_000_000);
			if (watcherFailure.get() != null) {
				// overrides the outcome of the job: the session cannot see cancellations any more
				throw new IllegalStateException("Job " + job + ": watching for a cancellation failed",
						watcherFailure.get());
			}
		}
	}

	/**
	 * A job stopped by a cancellation, a shutdown or the time limit sends nothing more.
	 *
	 * @return false if the session must end
	 */
	private boolean endStoppedJob(final long job, final long generation, final RetirementTimer stopTimer,
			final Exception cause) {
		if (stopTimer.isRetired()) {
			mStatistics.increment("jobsStopped");
			mLogger.info("Job %s (generation %s) stopped: %s", job, generation, stopTimer.getReason());
			return !mExchange.isShutdownRequested();
		}
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			mStatistics.increment("jobsStopped");
			mLogger.info("Job %s (generation %s) stopped by the time limit", job, generation);
			return false;
		}
		if (cause instanceof RuntimeException) {
			throw (RuntimeException) cause;
		}
		throw new IllegalStateException("Job " + job + " was cancelled, but not by a stop", cause);
	}

	private void sendResult(final long job, final long generation, final Feasibility<L> feasibility,
			final NestedWord<L> checkedWord) {
		final ResultStatus status;
		final JsonCodec.AutomatonType automatonType;
		WordCodec.EncodedWord word = null;
		String reason = null;
		if (feasibility.status() == LBool.UNSAT) {
			status = ResultStatus.UNSAT;
			mStatistics.increment("jobsUnsat");
			automatonType = JsonCodec.AutomatonType.FLOYD_HOARE;
		} else if (feasibility.status() == LBool.SAT) {
			status = ResultStatus.SAT;
			mStatistics.increment("jobsSat");
			automatonType = JsonCodec.AutomatonType.ERROR;
			word = WordCodec.encode(checkedWord, mLetters);
		} else {
			status = ResultStatus.UNKNOWN;
			mStatistics.increment("jobsUnknown");
			automatonType = JsonCodec.AutomatonType.ERROR;
			reason = "unable to decide satisfiability of path constraint";
		}
		mExchange.send(MessageType.RESULT, OptionalLong.of(job), OptionalLong.of(generation),
				JsonCodec.encode(new JsonCodec.Result(job, generation, status, automatonType,
						word == null ? null : word.word(), word == null ? null : word.nesting(), reason)));
		mLogger.info("Job %s: %s", job, status);
	}

	/**
	 * Starts a thread that retires {@code stopTimer} when a {@code CANCEL} for the job arrives or the session is asked
	 * to shut down. Interrupting the thread ends it.
	 */
	private Thread startStopWatcher(final long job, final RetirementTimer stopTimer,
			final AtomicReference<Throwable> failure) {
		final Thread watcher = new Thread(() -> {
			try {
				while (!Thread.currentThread().isInterrupted()) {
					if (mExchange.waitForStop(job, STOP_WATCH_INTERVAL)) {
						stopTimer.retire(mExchange.isShutdownRequested() ? "shutdown" : "cancelled");
						return;
					}
				}
			} catch (final InterruptedException e) {
				// the job is done
			} catch (final RuntimeException | Error e) {
				// stop the job; the session thread rethrows
				failure.set(e);
				stopTimer.retire("watching for a cancellation failed");
			}
		}, "Stop watcher for job " + job);
		watcher.setDaemon(true);
		watcher.start();
		return watcher;
	}
}
