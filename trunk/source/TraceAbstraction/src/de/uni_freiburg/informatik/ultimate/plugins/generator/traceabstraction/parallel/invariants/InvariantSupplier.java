/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.function.BooleanSupplier;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermClassifier;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ParallelNwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantMessage.InterpolantSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantMessage.Sample;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantMessage.SamplePoints;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantMessage.TrustedInvariants;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantSubscription.RunningQuery;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInduction;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CounterSort;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystemFactory;

/**
 * Collects invariants for the workers of {@link ParallelNwaCegarLoop}, on a thread of its own.
 * <p>
 * <b>Incoming</b>: producers {@link IInvariantSink#submit} messages without waiting. {@link TrustedInvariants} (the
 * fixpoint of abstract interpretation) are taken as they are. An {@link InterpolantSequence} (the interpolants of an
 * infeasible trace) only yields candidates: every conjunct of an interpolant at a loop head or waypoint of the
 * program. {@link InductivenessChecker} keeps the ones that are inductive relative to everything known so far, on the
 * same {@link KInduction} transition system of the initial abstraction.
 * <p>
 * <b>Sampling</b>: if enabled, the supplier also proposes candidates TA does not produce. It collects reachable states
 * at the loop heads, from bounded unrollings of the transition system ({@link ReachableStateSampler}), from
 * interpolants that fix the values of variables, and from {@link SamplePoints} of producers such as the value
 * analysis; {@link SampleCandidates} turns them into the equalities, bounds and orderings they satisfy. The comparisons
 * in the conditions of the loops are candidates too ({@link GuardTemplates}). All of them go through the same check.
 * <p>
 * <b>Outgoing</b>: every {@link #subscribe subscriber} gets its own channel. Whenever the invariant of a location got
 * stronger, it receives the location's whole current invariant, the conjunction of all trusted and all proven
 * conjuncts. A candidate that was not inductive is kept (up to {@link #MAX_RETRY_POOL}) and tried again once more is
 * known, since a new invariant may be exactly what it was missing.
 * <p>
 * <b>Probation</b>: if enabled, the supplier watches the queries of k-induction through the subscriptions. When one runs
 * much longer than the query of its kind before, it asks the same query with the invariants of other versions: the
 * newest, if it arrived after the query started, then earlier ones (see {@link InvariantProbation}). If one answers
 * within the limit, the supplier interrupts k-induction, which takes the probe's answer (or asks again for a violation,
 * whose witness it needs from its own solver). When a version is on probation for the second time, the supplier also
 * rolls back to the earlier version that answered, and never publishes the conjuncts it dropped again.
 * <p>
 * <b>Nonlinear programs</b>: if a transition of the program has nonlinear arithmetic, only the conjuncts over a
 * single variable are published. On such programs bounds keep the queries of k-induction tractable, while a single
 * relation between two variables can make the solver hang, even one over variables that only occur linearly. The
 * supplier itself keeps every conjunct, so relations still help to prove candidates; each conjunct of an invariant is
 * an invariant, so any subset may be published.
 * <p>
 * <b>Scripts</b>: the supplier owns its script and is the only one to build terms in it. It copies the producers' terms
 * into it on its own thread; subscribers copy from it on theirs.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class InvariantSupplier<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements Runnable {

	/** How many rejected candidates are kept to be tried again; beyond that the oldest are forgotten. */
	private static final int MAX_RETRY_POOL = 1000;
	/** How often the supplier looks at the queries of k-induction when no message arrives, in ms. */
	private static final long WATCH_INTERVAL_MILLIS = 1000;
	/** How many earlier versions a probation tries, newest first. */
	private static final int PROBED_VERSIONS = 3;

	/**
	 * The settings of the probation.
	 *
	 * @param factor
	 *            a query is on probation once it runs this many times longer than the previous one of its kind
	 * @param minimumMillis
	 *            ... and at least this long
	 * @param solverTimeoutMillis
	 *            the per-query timeout of the supplier's solver, restored after a probe
	 */
	public record Probation(int factor, long minimumMillis, long solverTimeoutMillis) {
	}

	/**
	 * The settings of the candidates from sampled loop-head states, see {@link SampleCandidates}.
	 *
	 * @param depth
	 *            how many pc steps the bounded unrollings that sample states take at most
	 * @param perDepth
	 *            how many states are sampled per head node and depth
	 */
	public record Sampling(int depth, int perDepth) {
	}

	private record Candidate(IcfgLocation location, Term term) {
	}

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCsToolkit;
	private final ManagedScript mScript;
	// Set once, on the main thread, before the supplier runs.
	private INestedWordAutomaton<L, IPredicate> mAbstraction;
	// Whether a transition of the abstraction has nonlinear arithmetic; set with mAbstraction.
	private boolean mNonlinear;
	private final BlockingQueue<WorkerThreadResult<L, A>> mResultQueue;

	private final BlockingQueue<InvariantMessage> mInbox = new LinkedBlockingQueue<>();
	private volatile boolean mStopped;
	// True once the CEGAR loop is done, before it shuts the supplier down and destroys its solver.
	private final BooleanSupplier mShuttingDown;
	// Guards mSubscriptions, mTaSubscriptions, mPublished and mTaLocations, the only state shared with other threads
	// besides the inbox.
	private final List<InvariantSubscription> mSubscriptions = new ArrayList<>();
	// The subscriptions of TA workers. They only get the invariants of mTaLocations and are never on probation.
	private final List<InvariantSubscription> mTaSubscriptions = new ArrayList<>();
	private final Map<IcfgLocation, Term> mPublished = new HashMap<>();
	private int mPublishedVersion;
	// The locations every pc node of which is a loop head, empty until the transition system is built. A waypoint is
	// a checkpoint only for some of the paths through its location, so what is proven there is no location invariant:
	// k-induction assumes it only at loop heads, and a TA worker, which assumes it at the location, must not get it.
	private Set<IcfgLocation> mTaLocations = Collections.emptySet();

	// Everything below is only touched by the supplier thread.
	private final Map<ManagedScript, TermTransferrer> mTransferrers = new IdentityHashMap<>();
	private final Map<IcfgLocation, Set<Term>> mTrusted = new HashMap<>();
	private final Map<IcfgLocation, Set<Term>> mProven = new HashMap<>();
	private final Map<IcfgLocation, Set<Term>> mTried = new HashMap<>();
	private final Set<Candidate> mRetryPool = new LinkedHashSet<>();
	private boolean mKnownGrew;
	private InductivenessChecker mChecker;
	// null unless probation is enabled
	private final InvariantProbation mProbation;
	// Version i: the conjuncts published per location after the i-th publication; version 0 is empty.
	private final List<Map<IcfgLocation, Set<Term>>> mVersions = new ArrayList<>(List.of(Map.of()));
	// Conjuncts that a rollback dropped, never published again at their location.
	private final Map<IcfgLocation, Set<Term>> mRolledBack = new HashMap<>();
	// Version -> how many of its queries were on probation.
	private final Map<Integer, Integer> mStalls = new HashMap<>();
	// null unless candidates from sampled states are enabled
	private final Sampling mSampling;
	private final SampleCandidates mSamples;
	// The locations of the loop heads, set with mChecker.
	private Set<IcfgLocation> mHeadLocations = Collections.emptySet();
	// Candidates that wait for the next round of checks, e.g. from the conditions of the loops.
	private final Map<IcfgLocation, Set<Term>> mPendingCandidates = new LinkedHashMap<>();
	private int mCandidatesFromSamples;
	private int mCandidatesFromGuards;

	/**
	 * Must be called on the main thread. The channels exist from here on, the abstraction follows with
	 * {@link #setAbstraction}: transferring it adds edges to the ICFG, which other workers must have read before.
	 *
	 * @param csToolkit
	 *            the supplier's own toolkit, whose script nobody else builds terms in
	 * @param resultQueue
	 *            where a crash is reported
	 * @param shuttingDown
	 *            whether the CEGAR loop is done, which is why a query may fail
	 * @param probation
	 *            the settings of the probation, or {@code null} to disable it
	 * @param sampling
	 *            the settings of the candidates from sampled loop-head states, or {@code null} to disable them
	 */
	public InvariantSupplier(final ILogger logger, final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final BlockingQueue<WorkerThreadResult<L, A>> resultQueue,
			final BooleanSupplier shuttingDown, final Probation probation, final Sampling sampling) {
		mLogger = logger;
		mServices = services;
		mCsToolkit = csToolkit;
		mScript = csToolkit.getManagedScript();
		mResultQueue = resultQueue;
		mShuttingDown = shuttingDown;
		mProbation = probation == null ? null
				: new InvariantProbation(logger, mScript, probation.factor(), probation.minimumMillis(),
						probation.solverTimeoutMillis());
		mSampling = sampling;
		mSamples = sampling == null ? null : new SampleCandidates(mScript.getScript());
	}

	/**
	 * Must be called on the main thread, before the supplier runs.
	 *
	 * @param abstraction
	 *            the initial abstraction, transferred to the supplier's script
	 */
	public void setAbstraction(final INestedWordAutomaton<L, IPredicate> abstraction) {
		if (mAbstraction != null) {
			throw new IllegalStateException("the invariant supplier already has an abstraction");
		}
		mAbstraction = abstraction;
		final TermClassifier classifier = new TermClassifier();
		final VpAlphabet<L> alphabet = abstraction.getVpAlphabet();
		for (final Set<L> letters : List.of(alphabet.getInternalAlphabet(), alphabet.getCallAlphabet(),
				alphabet.getReturnAlphabet())) {
			for (final L letter : letters) {
				classifier.checkTerm(letter.getTransformula().getFormula());
			}
		}
		mNonlinear = classifier.hasNonlinearArithmetic();
		if (mNonlinear) {
			mLogger.info("InvariantSupplier: the program has nonlinear arithmetic, only single-variable conjuncts "
					+ "are published");
		}
	}

	/**
	 * @return the program location of an abstraction state
	 */
	public static IcfgLocation locationOf(final IPredicate state) {
		if (!(state instanceof ISLPredicate)) {
			throw new UnsupportedOperationException("abstraction state " + state + " is a "
					+ state.getClass().getSimpleName() + ", not an ISLPredicate, so it has no single program location");
		}
		return ((ISLPredicate) state).getProgramPoint();
	}

	/**
	 * @return the incoming channel, for producers
	 */
	public IInvariantSink sink() {
		return message -> {
			if (!mStopped) {
				mInbox.add(message);
			}
		};
	}

	/**
	 * @param target
	 *            the consumer's script
	 * @return a new outgoing channel, which starts with everything published so far
	 */
	public InvariantSubscription subscribe(final ManagedScript target) {
		final InvariantSubscription subscription = new InvariantSubscription(mScript, target, mProbation != null);
		synchronized (mSubscriptions) {
			if (!mPublished.isEmpty()) {
				subscription.offer(mPublishedVersion, Map.copyOf(mPublished));
			}
			mSubscriptions.add(subscription);
		}
		return subscription;
	}

	/**
	 * A channel for a TA worker: it only delivers the invariants of loop-head locations, see {@link #mTaLocations},
	 * and is never on probation.
	 *
	 * @param target
	 *            the worker's script
	 * @return a new outgoing channel, which starts with everything published so far at loop heads
	 */
	public InvariantSubscription subscribeForTa(final ManagedScript target) {
		final InvariantSubscription subscription = new InvariantSubscription(mScript, target, false);
		synchronized (mSubscriptions) {
			final Map<IcfgLocation, Term> published = forTa(mPublished);
			if (!published.isEmpty()) {
				subscription.offer(mPublishedVersion, published);
			}
			mTaSubscriptions.add(subscription);
		}
		return subscription;
	}

	/**
	 * Must hold the lock of {@link #mSubscriptions}.
	 *
	 * @return the invariants of {@code update} that a TA worker may assume
	 */
	private Map<IcfgLocation, Term> forTa(final Map<IcfgLocation, Term> update) {
		final Map<IcfgLocation, Term> result = new HashMap<>();
		for (final Map.Entry<IcfgLocation, Term> entry : update.entrySet()) {
			if (mTaLocations.contains(entry.getKey())) {
				result.put(entry.getKey(), entry.getValue());
			}
		}
		return Map.copyOf(result);
	}

	@Override
	public void run() {
		Thread.currentThread().setName("Invariant Supplier Thread");
		try {
			if (mAbstraction == null) {
				throw new IllegalStateException("the invariant supplier was started without an abstraction");
			}
			if (mSamples != null) {
				// Needs no message: the conditions of the loops and the sampled states are there from the start.
				proposeInitialCandidates();
				process(Collections.emptyList());
			}
			while (true) {
				final List<InvariantMessage> batch = new ArrayList<>();
				if (mProbation == null) {
					batch.add(mInbox.take());
				} else {
					// Wakes up now and then without a message, to watch the queries of k-induction.
					final InvariantMessage first = mInbox.poll(WATCH_INTERVAL_MILLIS, TimeUnit.MILLISECONDS);
					if (first != null) {
						batch.add(first);
					}
				}
				mInbox.drainTo(batch);
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					mLogger.info("InvariantSupplier: stopping, the time is up");
					return;
				}
				if (!batch.isEmpty()) {
					process(batch);
				}
				if (mProbation != null) {
					watch();
				}
			}
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
		} catch (final ToolchainCanceledException e) {
			mLogger.info("InvariantSupplier: stopping, " + e.getMessage());
		} catch (final Throwable t) {
			if (mShuttingDown.getAsBoolean()) {
				// The CEGAR loop is done and destroyed the solver under a query that was still running. The interrupt
				// flag is no evidence, it does not survive every library on the way. Nobody waits for a result.
				mLogger.info("InvariantSupplier: stopping, shut down during a query (" + t + ")");
				return;
			}
			mLogger.error("InvariantSupplier crashed: " + t);
			for (final StackTraceElement element : t.getStackTrace()) {
				mLogger.error("\tat " + element);
			}
			try {
				mResultQueue.put(WorkerThreadResult.crashed(WorkerType.INVARIANT, t));
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
		} finally {
			mStopped = true;
			mInbox.clear();
			logStatistics();
		}
	}

	/**
	 * Logs per location what the supplier saw and proved, to tell whether it proves anything at the loop heads at all.
	 * Only touches the supplier's own state, so it never asks the solver, which may already be destroyed.
	 */
	private void logStatistics() {
		if (mChecker == null) {
			mLogger.info("InvariantSupplier statistics: no interpolant arrived, %d location(s) with trusted invariants",
					mTrusted.size());
			return;
		}
		final Set<IcfgLocation> heads = new LinkedHashSet<>();
		for (final CallNode<IPredicate> node : mChecker.getSystem().getHeadNodes().keySet()) {
			heads.add(locationOf(node.getState()));
		}
		final Map<IcfgLocation, Integer> pooled = new HashMap<>();
		for (final Candidate candidate : mRetryPool) {
			pooled.merge(candidate.location(), 1, Integer::sum);
		}
		final Set<IcfgLocation> locations = new LinkedHashSet<>(mTried.keySet());
		locations.addAll(mTrusted.keySet());
		locations.addAll(mProven.keySet());
		int provenAtHeads = 0;
		int provenAtWaypoints = 0;
		for (final IcfgLocation location : locations) {
			final int proven = mProven.getOrDefault(location, Collections.emptySet()).size();
			final boolean head = heads.contains(location);
			if (head) {
				provenAtHeads += proven;
			} else {
				provenAtWaypoints += proven;
			}
			mLogger.info("InvariantSupplier statistics: %s %s - %d candidate(s) seen, %d proven, %d trusted, %d in the "
					+ "retry pool%s%s", head ? "loop head" : "waypoint", location,
					mTried.getOrDefault(location, Collections.emptySet()).size(), proven,
					mTrusted.getOrDefault(location, Collections.emptySet()).size(), pooled.getOrDefault(location, 0),
					mSamples == null ? "" : ", " + mSamples.count(location) + " sampled state(s)",
					proven == 0 ? "" : ", proven: " + mProven.get(location));
		}
		mLogger.info("InvariantSupplier statistics: %d conjunct(s) proven at %d loop head(s), %d at waypoints, %d "
				+ "version(s) published, %d conjunct(s) rolled back", provenAtHeads, heads.size(), provenAtWaypoints,
				mVersions.size() - 1, mRolledBack.values().stream().mapToInt(Set::size).sum());
		if (mSamples != null) {
			mLogger.info("InvariantSupplier statistics: %d sampled state(s), %d candidate(s) from sampled states, %d "
					+ "from the conditions of the loops", mSamples.count(), mCandidatesFromSamples,
					mCandidatesFromGuards);
		}
	}

	private void process(final List<InvariantMessage> batch) {
		// Trusted invariants first and published at once: they need no transition system, which may take long to
		// build the first time an interpolant arrives.
		final Set<IcfgLocation> changed = new LinkedHashSet<>();
		for (final InvariantMessage message : batch) {
			if (message instanceof final TrustedInvariants trusted) {
				takeTrusted(trusted, changed);
			}
		}
		publish(changed);
		changed.clear();

		final Map<IcfgLocation, Set<Term>> candidates = new LinkedHashMap<>();
		int sequences = 0;
		for (final InvariantMessage message : batch) {
			if (message instanceof final InterpolantSequence sequence) {
				takeCandidates(sequence, candidates);
				sequences++;
			} else if (message instanceof final SamplePoints points) {
				takeSamples(points);
			}
		}
		if (mChecker == null) {
			// No interpolant arrived yet, so there is nothing to check and nothing was rejected.
			return;
		}
		for (final Map.Entry<IcfgLocation, Set<Term>> pending : mPendingCandidates.entrySet()) {
			for (final Term candidate : pending.getValue()) {
				offerCandidate(pending.getKey(), candidate, candidates);
			}
		}
		mPendingCandidates.clear();
		if (mSamples != null) {
			for (final IcfgLocation location : mSamples.takeChanged()) {
				for (final Term candidate : mSamples.candidates(location)) {
					if (offerCandidate(location, candidate, candidates)) {
						mCandidatesFromSamples++;
					}
				}
			}
		}
		int checked = 0;
		int proven = 0;
		Map<IcfgLocation, Set<Term>> round = candidates;
		while (true) {
			if (mKnownGrew) {
				mKnownGrew = false;
				takeRetryPool(round);
			}
			final int size = count(round);
			if (size == 0) {
				break;
			}
			checked += size;
			final int newlyProven = checkAndRemember(round, changed);
			proven += newlyProven;
			if (newlyProven == 0) {
				break;
			}
			// What was just proven may be what a rejected candidate was missing.
			round = new LinkedHashMap<>();
		}
		if (sequences > 0 || checked > 0) {
			mLogger.info("InvariantSupplier: %d interpolant sequence(s), %d candidate check(s), %d proven, "
					+ "%d waiting for a retry", sequences, checked, proven, mRetryPool.size());
		}
		publish(changed);
	}

	private void takeTrusted(final TrustedInvariants message, final Set<IcfgLocation> changed) {
		for (final Map.Entry<IcfgLocation, Term> entry : message.invariants().entrySet()) {
			for (final Term conjunct : SmtUtils.getConjuncts(transfer(message.source(), entry.getValue()))) {
				if (SmtUtils.isTrueLiteral(conjunct)) {
					continue;
				}
				if (mTrusted.computeIfAbsent(entry.getKey(), x -> new LinkedHashSet<>()).add(conjunct)) {
					changed.add(entry.getKey());
					mKnownGrew = true;
				}
			}
		}
		mLogger.info("InvariantSupplier: took invariants of %d location(s) from %s", message.invariants().size(),
				message.origin());
	}

	private void takeCandidates(final InterpolantSequence message,
			final Map<IcfgLocation, Set<Term>> candidates) {
		final InductivenessChecker checker = getChecker();
		for (int i = 0; i < message.locations().size(); i++) {
			final IcfgLocation location = message.locations().get(i);
			if (!checker.hasNode(location)) {
				continue;
			}
			final List<Term> conjuncts =
					List.of(SmtUtils.getConjuncts(transfer(message.source(), message.interpolants().get(i))));
			for (final Term conjunct : conjuncts) {
				offerCandidate(location, conjunct, candidates);
			}
			if (mSamples != null && mHeadLocations.contains(location)) {
				// An interpolant that fixes values, e.g. i = 3 and x = 6 in an unwinding of a loop, is a reachable
				// state on this trace, or the trace is infeasible before; either way a state worth fitting.
				addPoint(location, SampleCandidates.pointOf(conjuncts));
			}
		}
	}

	/**
	 * Adds {@code candidate} to {@code candidates} unless it is trivial, known, tried before or not expressible.
	 *
	 * @return whether it was added
	 */
	private boolean offerCandidate(final IcfgLocation location, final Term candidate,
			final Map<IcfgLocation, Set<Term>> candidates) {
		final Set<Term> tried = mTried.computeIfAbsent(location, x -> new LinkedHashSet<>());
		if (SmtUtils.isTrueLiteral(candidate) || isKnown(location, candidate) || !tried.add(candidate)) {
			return false;
		}
		if (!mChecker.isExpressible(candidate)) {
			return false;
		}
		candidates.computeIfAbsent(location, x -> new LinkedHashSet<>()).add(candidate);
		return true;
	}

	/**
	 * Takes the states of a producer, e.g. the value analysis, at the loop heads.
	 */
	private void takeSamples(final SamplePoints message) {
		if (mSamples == null) {
			return;
		}
		getChecker();
		int added = 0;
		for (final Sample sample : message.samples()) {
			if (!mHeadLocations.contains(sample.location())) {
				continue;
			}
			final Map<TermVariable, Rational> point = new LinkedHashMap<>();
			for (final Map.Entry<Term, Rational> value : sample.values().entrySet()) {
				final Term variable = transfer(message.source(), value.getKey());
				if (variable instanceof final TermVariable tv && SampleCandidates.isSampled(tv)) {
					point.put(tv, value.getValue());
				}
			}
			if (addPoint(sample.location(), point)) {
				added++;
			}
		}
		mLogger.info("InvariantSupplier: took %d new state(s) at loop heads from %s", added, message.origin());
	}

	/**
	 * Adds a point, restricted to the variables of the transition system.
	 *
	 * @return whether it was new
	 */
	private boolean addPoint(final IcfgLocation location, final Map<TermVariable, Rational> point) {
		final Map<TermVariable, Rational> restricted = new LinkedHashMap<>();
		for (final Map.Entry<TermVariable, Rational> entry : point.entrySet()) {
			if (mChecker.isExpressible(entry.getKey())) {
				restricted.put(entry.getKey(), entry.getValue());
			}
		}
		return mSamples.add(location, restricted);
	}

	/**
	 * Samples states at the loop heads by bounded unrollings, and proposes the comparisons in the conditions of the
	 * loops; the candidates are checked by the next call of {@link #process}.
	 */
	private void proposeInitialCandidates() {
		final InductivenessChecker checker = getChecker();
		for (final Map.Entry<IcfgLocation, Set<Term>> entry : GuardTemplates
				.compute(mScript, mAbstraction, mHeadLocations).entrySet()) {
			mPendingCandidates.computeIfAbsent(entry.getKey(), x -> new LinkedHashSet<>()).addAll(entry.getValue());
			mCandidatesFromGuards += entry.getValue().size();
		}
		final long start = System.nanoTime();
		final int sampled = new ReachableStateSampler(mLogger, mServices, mScript, checker.getSystem(),
				checker.constants("smp")).sample(mSampling.depth(), mSampling.perDepth(), mSamples);
		mLogger.info("InvariantSupplier: sampled %d state(s) at %d loop head location(s) in %d ms, %d candidate(s) "
				+ "from the conditions of the loops", sampled, mSamples.locations(),
				(System.nanoTime() - start) / 1_000_000, mCandidatesFromGuards);
	}

	private void takeRetryPool(final Map<IcfgLocation, Set<Term>> round) {
		for (final Candidate candidate : mRetryPool) {
			if (isKnown(candidate.location(), candidate.term())) {
				continue;
			}
			round.computeIfAbsent(candidate.location(), x -> new LinkedHashSet<>()).add(candidate.term());
		}
		mRetryPool.clear();
	}

	/**
	 * Checks {@code candidates}, adds what is inductive to the proven invariants and the rest to the retry pool.
	 *
	 * @return how many were proven
	 */
	private int checkAndRemember(final Map<IcfgLocation, Set<Term>> candidates, final Set<IcfgLocation> changed) {
		final Map<IcfgLocation, Set<Term>> inductive = mChecker.check(known(), candidates);
		if (inductive == null) {
			mLogger.warn("InvariantSupplier: the solver could not decide whether %d candidate(s) are inductive, "
					+ "they wait for a retry", count(candidates));
		}
		int proven = 0;
		for (final Map.Entry<IcfgLocation, Set<Term>> entry : candidates.entrySet()) {
			final Set<Term> good = inductive == null ? Collections.emptySet()
					: inductive.getOrDefault(entry.getKey(), Collections.emptySet());
			for (final Term candidate : entry.getValue()) {
				if (good.contains(candidate)) {
					mProven.computeIfAbsent(entry.getKey(), x -> new LinkedHashSet<>()).add(candidate);
					changed.add(entry.getKey());
					proven++;
					mLogger.info("InvariantSupplier: proven at %s: %s", entry.getKey(), candidate);
				} else {
					addToRetryPool(new Candidate(entry.getKey(), candidate));
				}
			}
		}
		if (proven > 0) {
			mKnownGrew = true;
		}
		return proven;
	}

	private void addToRetryPool(final Candidate candidate) {
		mRetryPool.add(candidate);
		final Iterator<Candidate> oldest = mRetryPool.iterator();
		while (mRetryPool.size() > MAX_RETRY_POOL) {
			oldest.next();
			oldest.remove();
		}
	}

	private void publish(final Set<IcfgLocation> changed) {
		if (changed.isEmpty()) {
			return;
		}
		final Map<IcfgLocation, Set<Term>> version = new HashMap<>(mVersions.get(mVersions.size() - 1));
		final Map<IcfgLocation, Term> update = new HashMap<>();
		int withheld = 0;
		for (final IcfgLocation location : changed) {
			final Set<Term> published = new LinkedHashSet<>();
			final Set<Term> rolledBack = mRolledBack.getOrDefault(location, Collections.emptySet());
			for (final Term conjunct : knownAt(location)) {
				if (mNonlinear && conjunct.getFreeVars().length > 1) {
					withheld++;
				} else if (!rolledBack.contains(conjunct)) {
					published.add(conjunct);
				}
			}
			if (published.equals(version.getOrDefault(location, Collections.emptySet()))) {
				continue;
			}
			if (published.isEmpty()) {
				version.remove(location);
			} else {
				version.put(location, published);
			}
			// An empty invariant is published as true, to replace one that was rolled back.
			update.put(location, SmtUtils.and(mScript.getScript(), published));
		}
		if (withheld > 0) {
			mLogger.info("InvariantSupplier: withheld %d conjunct(s) relating several variables", withheld);
		}
		if (update.isEmpty()) {
			return;
		}
		mVersions.add(version);
		final int number = mVersions.size() - 1;
		synchronized (mSubscriptions) {
			mPublished.putAll(update);
			mPublishedVersion = number;
			for (final InvariantSubscription subscription : mSubscriptions) {
				subscription.offer(number, Map.copyOf(update));
			}
			if (!mTaSubscriptions.isEmpty()) {
				final Map<IcfgLocation, Term> taUpdate = forTa(update);
				if (!taUpdate.isEmpty()) {
					for (final InvariantSubscription subscription : mTaSubscriptions) {
						subscription.offer(number, taUpdate);
					}
				}
			}
		}
		mLogger.info("InvariantSupplier: published version %d, invariants of %d location(s)", number, update.size());
	}

	// ------------------------------------------------------------------------------------------------------------
	// Probation
	// ------------------------------------------------------------------------------------------------------------

	private void watch() {
		final List<InvariantSubscription> subscriptions;
		synchronized (mSubscriptions) {
			subscriptions = new ArrayList<>(mSubscriptions);
		}
		for (final InvariantSubscription subscription : subscriptions) {
			final RunningQuery query = mProbation.due(subscription);
			if (query != null) {
				probe(subscription, query);
			}
		}
	}

	/**
	 * Asks the slow query with other invariants: first the newest version, if the query runs with an older one (e.g. new
	 * interpolants arrived meanwhile), then earlier versions, newest first. The first one that answers within the limit
	 * gives k-induction its answer, and k-induction is interrupted. The published invariants are rolled back only if
	 * the version of the query was already on probation before, and never to an empty version: a single fast probe says
	 * little about the next queries.
	 */
	private void probe(final InvariantSubscription subscription, final RunningQuery query) {
		final long limit = mProbation.limitMillis(subscription, query.kind());
		final Map<IcfgLocation, Set<Term>> current = mVersions.get(query.version());
		final int stalls = mStalls.merge(query.version(), 1, Integer::sum);
		mLogger.info("InvariantSupplier: probation, the %s case at k=%d with version %d runs longer than %d ms",
				query.kind(), query.k(), query.version(), limit);
		final List<Integer> candidates = new ArrayList<>();
		final int newest = mVersions.size() - 1;
		if (newest > query.version()) {
			candidates.add(newest);
		}
		for (int earlier = query.version() - 1; earlier >= Math.max(0, query.version() - PROBED_VERSIONS); earlier--) {
			candidates.add(earlier);
		}
		for (final int version : candidates) {
			final Map<IcfgLocation, Set<Term>> candidate = mVersions.get(version);
			if (candidate.equals(current) || containsRolledBack(candidate)) {
				continue;
			}
			final long start = System.nanoTime();
			final LBool answer =
					mProbation.ask(getChecker(), query.kind(), query.k(), candidate, limit);
			mLogger.info("InvariantSupplier: probation, version %d answers %s in %d ms", version, answer,
					(System.nanoTime() - start) / 1_000_000);
			if (answer == LBool.UNKNOWN) {
				continue;
			}
			if (!query.equals(subscription.runningQuery())) {
				mLogger.info("InvariantSupplier: probation, k-induction answered meanwhile");
				return;
			}
			if (version < query.version() && stalls > 1 && !candidate.isEmpty()) {
				rollBack(current, candidate, version);
			}
			if (subscription.interrupt(query.kind(), query.k(), answer)) {
				mLogger.info("InvariantSupplier: probation, interrupted k-induction and handed it the answer");
			} else {
				mLogger.info("InvariantSupplier: probation, k-induction answered before the interrupt");
			}
			return;
		}
		mLogger.info("InvariantSupplier: probation, no other version answers within %d ms, k-induction goes on",
				limit);
	}

	private boolean containsRolledBack(final Map<IcfgLocation, Set<Term>> version) {
		for (final Map.Entry<IcfgLocation, Set<Term>> entry : version.entrySet()) {
			final Set<Term> rolledBack = mRolledBack.getOrDefault(entry.getKey(), Collections.emptySet());
			if (!Collections.disjoint(rolledBack, entry.getValue())) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Drops what {@code current} has beyond {@code target}, for good, and publishes the result.
	 */
	private void rollBack(final Map<IcfgLocation, Set<Term>> current, final Map<IcfgLocation, Set<Term>> target,
			final int targetVersion) {
		final Set<IcfgLocation> changed = new LinkedHashSet<>(current.keySet());
		changed.addAll(target.keySet());
		int dropped = 0;
		for (final Map.Entry<IcfgLocation, Set<Term>> entry : current.entrySet()) {
			final Set<Term> beyond = new LinkedHashSet<>(entry.getValue());
			beyond.removeAll(target.getOrDefault(entry.getKey(), Collections.emptySet()));
			dropped += beyond.size();
			mRolledBack.computeIfAbsent(entry.getKey(), x -> new LinkedHashSet<>()).addAll(beyond);
		}
		mLogger.warn("InvariantSupplier: probation, rolling back to version %d, dropping %d conjunct(s)",
				targetVersion, dropped);
		publish(changed);
	}

	private InductivenessChecker getChecker() {
		if (mChecker == null) {
			final PcTransitionSystemFactory.Result<L, IPredicate> encoding =
					PcTransitionSystemFactory.build(mServices, mLogger, mCsToolkit, mScript, mAbstraction,
						CounterSort.forProgram(mScript.getScript(), mCsToolkit));
			mChecker = new InductivenessChecker(mLogger, mScript, encoding.system());
			final Set<IcfgLocation> taLocations = new LinkedHashSet<>();
			for (final CallNode<IPredicate> head : encoding.system().getHeadNodes().keySet()) {
				taLocations.add(locationOf(head.getState()));
			}
			mHeadLocations = Set.copyOf(taLocations);
			for (final CallNode<IPredicate> waypoint : encoding.system().getWaypointNodes().keySet()) {
				taLocations.remove(locationOf(waypoint.getState()));
			}
			synchronized (mSubscriptions) {
				mTaLocations = Set.copyOf(taLocations);
			}
			mLogger.info("InvariantSupplier: transition system with %d pc value(s), %d loop head(s), %d waypoint(s)",
					encoding.system().getNumNodes(), encoding.system().getHeadNodes().size(),
					encoding.system().getWaypointNodes().size());
		}
		return mChecker;
	}

	private Term transfer(final ManagedScript source, final Term term) {
		if (source == mScript) {
			return term;
		}
		return mTransferrers.computeIfAbsent(source, s -> new TermTransferrer(s.getScript(), mScript.getScript()))
				.transform(term);
	}

	private boolean isKnown(final IcfgLocation location, final Term conjunct) {
		return mTrusted.getOrDefault(location, Collections.emptySet()).contains(conjunct)
				|| mProven.getOrDefault(location, Collections.emptySet()).contains(conjunct);
	}

	private Set<Term> knownAt(final IcfgLocation location) {
		final Set<Term> result = new LinkedHashSet<>(mTrusted.getOrDefault(location, Collections.emptySet()));
		result.addAll(mProven.getOrDefault(location, Collections.emptySet()));
		return result;
	}

	private Map<IcfgLocation, Set<Term>> known() {
		final Map<IcfgLocation, Set<Term>> result = new HashMap<>();
		for (final IcfgLocation location : mTrusted.keySet()) {
			result.put(location, knownAt(location));
		}
		for (final IcfgLocation location : mProven.keySet()) {
			result.put(location, knownAt(location));
		}
		return result;
	}

	private static int count(final Map<IcfgLocation, Set<Term>> candidates) {
		return candidates.values().stream().mapToInt(Set::size).sum();
	}
}
