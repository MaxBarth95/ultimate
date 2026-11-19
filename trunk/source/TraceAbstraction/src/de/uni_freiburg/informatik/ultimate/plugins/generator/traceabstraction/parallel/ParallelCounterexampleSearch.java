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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IsEmptyParallel;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * The counterexample search of a CEGAR loop whose counterexamples are checked by several workers at once: the
 * threaded {@link ParallelNwaCegarLoop} and the coordinator of the multi-process trace abstraction.
 *
 * It remembers the counterexamples in flight, keyed by the hash of their word, so that it does not hand out the same
 * one twice. On a newly refined abstraction it first tries a breadth-first search; otherwise, or if that finds a
 * counterexample in flight, it uses {@link IsEmptyParallel}, which avoids the counterexamples in flight.
 *
 * @param <L>
 *            the letter type
 */
public final class ParallelCounterexampleSearch<L extends IIcfgTransition<?>> {

	private final ILogger mLogger;
	private final TAPreferences mPref;
	private final HashMap<Integer, NestedRun<L, ?>> mActiveCounterexamples = new HashMap<>();
	private int mBfsFoundCex = 1;
	private int mFailedToFindCex;
	private long mSearchTimeSeconds;

	public ParallelCounterexampleSearch(final ILogger logger, final TAPreferences pref) {
		mLogger = logger;
		mPref = pref;
	}

	/**
	 * Searches for an accepting run of the abstraction that is not in flight.
	 *
	 * @param onlyIsEmptyParallel
	 *            false for the first search on a newly refined abstraction, which then tries a breadth-first search
	 *            first
	 * @return the run, or null if no run outside the ones in flight was found
	 */
	public NestedRun<L, IPredicate> search(final IUltimateServiceProvider services,
			final INestedWordAutomaton<L, IPredicate> abstraction, final PredicateFactoryRefinement stateFactory,
			final boolean onlyIsEmptyParallel) throws AutomataOperationCanceledException {
		final long time = System.nanoTime() / 1000000000;
		IsEmpty<L, IPredicate> search;
		if (!onlyIsEmptyParallel) {
			search = new IsEmpty<>(new AutomataLibraryServices(services), abstraction, IsEmpty.SearchStrategy.BFS);
			if (isCorrectAndFresh(search, stateFactory)) {
				mBfsFoundCex += 1;
				mLogger.info("Found new Counterexample via BFS!");
				return search.getNestedRun();
			}
		}
		search = new IsEmptyParallel<>(new AutomataLibraryServices(services), abstraction,
				abstraction.getInitialStates(), Collections.emptySet(), null, true, IsEmpty.SearchStrategy.BFS,
				mActiveCounterexamples, mPref.getSearchLoopBound());
		if (isCorrectAndFresh(search, stateFactory)) {
			mLogger.info("Found new Counterexample via IsEmptyParallel!");
			return search.getNestedRun();
		}
		mLogger.info("Did not Find a Counterexample!");
		mFailedToFindCex += 1;
		mSearchTimeSeconds += System.nanoTime() / 1000000000 - time;
		return null;
	}

	// If search was BFS, the counterexample might not be fresh.
	private boolean isCorrectAndFresh(final IsEmpty<L, IPredicate> search,
			final PredicateFactoryRefinement stateFactory) {
		boolean correct = false;
		try {
			correct = search.checkResult(stateFactory);
		} catch (final AutomataLibraryException e) {
			throw new IllegalStateException("Cannot check the result of the counterexample search", e);
		}
		final NestedRun<L, IPredicate> run = search.getNestedRun();
		if (run == null) {
			return false;
		}
		return correct && !mActiveCounterexamples.containsKey(hash(run));
	}

	/**
	 * Remembers a counterexample that a worker now checks.
	 *
	 * @throws AssertionError
	 *             if it is already in flight
	 */
	public void add(final IRun<L, ?> counterexample) {
		final int traceHash = hash(counterexample);
		if (mActiveCounterexamples.containsKey(traceHash)) {
			throw new AssertionError("IsEmpty(Parallel) Found the same counterexample twice!");
		}
		mActiveCounterexamples.put(traceHash, (NestedRun<L, ?>) counterexample);
	}

	/**
	 * A worker's result for a counterexample is about to be refined with. Depending on the setting
	 * {@link TAPreferences#considerOnlyActiveCounterexamplesInIsEmptyParallel()}, the search forgets it, or keeps
	 * avoiding it.
	 */
	public void refinedWith(final IRun<L, ?> counterexample) {
		final int traceHash = hash(counterexample);
		mLogger.info("Subtrahend traceHash: " + traceHash);
		if (mPref.considerOnlyActiveCounterexamplesInIsEmptyParallel()) {
			mActiveCounterexamples.remove(traceHash);
		}
	}

	/**
	 * Forgets a counterexample that will not be refined with (its worker retired, or its job was cancelled).
	 */
	public void forget(final IRun<L, ?> counterexample) {
		mActiveCounterexamples.remove(hash(counterexample));
	}

	/**
	 * Forgets every counterexample.
	 */
	public void clear() {
		mActiveCounterexamples.clear();
	}

	/**
	 * @return the counterexamples the search avoids
	 */
	public Set<Integer> activeHashes() {
		return Collections.unmodifiableSet(mActiveCounterexamples.keySet());
	}

	public int getBfsFoundCex() {
		return mBfsFoundCex;
	}

	public int getFailedToFindCex() {
		return mFailedToFindCex;
	}

	public long getSearchTimeSeconds() {
		return mSearchTimeSeconds;
	}

	private static <L> int hash(final IRun<L, ?> run) {
		final List<L> trace = run.getWord().asList();
		return trace.hashCode();
	}
}
