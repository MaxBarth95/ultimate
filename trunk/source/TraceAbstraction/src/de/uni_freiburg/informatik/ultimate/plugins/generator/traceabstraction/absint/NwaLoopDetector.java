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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.absint;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLoopDetector;

/**
 * Loop heads of an {@link NwaTransitionProvider}, from the automaton's structure.
 * <p>
 * The fixpoint engine widens only at the heads its loop detector reports, so a cycle without one makes a domain of
 * infinite height, e.g. intervals, climb forever. {@link RcfgLoopDetector} relies on {@code LoopEntryAnnotation}s on
 * edges, which the IcfgBuilder only puts on goto loops: it marks the head of a while loop, not its edges. So this
 * detector takes the targets of the back edges of a depth-first search instead, started at the initial states and at
 * every callee's entry. The search follows the internal transitions and steps over a call from its call site straight
 * to its return sites, so a loop whose body calls a procedure is a cycle too. Every such cycle has a back edge, so
 * every one gets a head. Cycles through a call into the callee are recursion, which the engine bounds by scope
 * widening.
 * <p>
 * The engine counts the iterations of a loop when it takes an internal transition out of the head: a call switches to
 * the callee's scope first, which would lose the count. So a head whose only successor is a call is moved to the call's
 * return site, which lies on the same cycles.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class NwaLoopDetector implements ILoopDetector<IcfgEdge> {

	private final NwaTransitionProvider mTransitionProvider;
	private final Set<IPredicate> mLoopHeads;

	public NwaLoopDetector(final NwaTransitionProvider transitionProvider) {
		mTransitionProvider = transitionProvider;
		final Map<IPredicate, Set<IPredicate>> returnSites = computeReturnSites(transitionProvider);
		final Set<IPredicate> heads = new HashSet<>();
		for (final IPredicate head : computeLoopHeads(transitionProvider, returnSites)) {
			heads.addAll(moveToInternalSuccessor(transitionProvider, returnSites, head));
		}
		mLoopHeads = Collections.unmodifiableSet(heads);
	}

	public Set<IPredicate> getLoopHeads() {
		return mLoopHeads;
	}

	/**
	 * Any transition out of a head enters its loop, including the one that leaves it again. That only makes the
	 * engine count one more iteration of a loop it is done with, the head is never reached again on that path.
	 */
	@Override
	public boolean isEnteringLoop(final IcfgEdge transition) {
		return isInternal(transition) && mLoopHeads.contains(mTransitionProvider.getSource(transition));
	}

	/**
	 * The forward fixpoint engine never asks, and the back edges alone do not tell which transition leaves a loop.
	 */
	@Override
	public boolean isLeavingLoop(final IcfgEdge transition) {
		throw new UnsupportedOperationException(getClass().getSimpleName() + " does not know where loops are left");
	}

	private static boolean isInternal(final IcfgEdge edge) {
		return !(edge instanceof IIcfgCallTransition<?>) && !(edge instanceof IIcfgReturnTransition<?, ?>);
	}

	/**
	 * @return the return sites of every call site, i.e. the targets of the returns of the calls out of it
	 */
	private static Map<IPredicate, Set<IPredicate>>
			computeReturnSites(final NwaTransitionProvider transitionProvider) {
		final Map<IPredicate, Set<IPredicate>> returnSites = new HashMap<>();
		for (final IcfgEdge action : transitionProvider.getActions()) {
			if (!(action instanceof IIcfgReturnTransition<?, ?>)) {
				continue;
			}
			final IPredicate callSite = transitionProvider
					.getSource((IcfgEdge) ((IIcfgReturnTransition<?, ?>) action).getCorrespondingCall());
			if (callSite == null) {
				// the call is not a letter of the automaton, e.g. of an unreachable part
				continue;
			}
			returnSites.computeIfAbsent(callSite, x -> new LinkedHashSet<>()).add(transitionProvider.getTarget(action));
		}
		return returnSites;
	}

	/**
	 * Successors of the search: targets of internal transitions, and for a call its return sites.
	 */
	private static Iterator<IPredicate> successors(final NwaTransitionProvider transitionProvider,
			final Map<IPredicate, Set<IPredicate>> returnSites, final IPredicate state) {
		final List<IPredicate> internal = transitionProvider.getSuccessorActions(state).stream()
				.filter(NwaLoopDetector::isInternal).map(transitionProvider::getTarget).collect(Collectors.toList());
		return Stream.concat(internal.stream(), returnSites.getOrDefault(state, Set.of()).stream()).iterator();
	}

	/**
	 * A head without an internal successor has only calls as successors: moves it along them to their return sites,
	 * until each has an internal successor.
	 */
	private static Set<IPredicate> moveToInternalSuccessor(final NwaTransitionProvider transitionProvider,
			final Map<IPredicate, Set<IPredicate>> returnSites, final IPredicate head) {
		final Set<IPredicate> result = new HashSet<>();
		final Set<IPredicate> visited = new HashSet<>();
		final Deque<IPredicate> worklist = new ArrayDeque<>();
		worklist.add(head);
		visited.add(head);
		while (!worklist.isEmpty()) {
			final IPredicate state = worklist.pop();
			if (transitionProvider.getSuccessorActions(state).stream().anyMatch(NwaLoopDetector::isInternal)) {
				result.add(state);
				continue;
			}
			for (final IPredicate returnSite : returnSites.getOrDefault(state, Set.of())) {
				if (visited.add(returnSite)) {
					worklist.add(returnSite);
				}
			}
		}
		if (result.isEmpty()) {
			throw new UnsupportedOperationException(
					"The loop at " + head + " consists of calls only, it has no transition to widen at");
		}
		return result;
	}

	private static Set<IPredicate> computeLoopHeads(final NwaTransitionProvider transitionProvider,
			final Map<IPredicate, Set<IPredicate>> returnSites) {
		final Set<IPredicate> roots = new LinkedHashSet<>(transitionProvider.getInitialStates());
		for (final IcfgEdge action : transitionProvider.getActions()) {
			if (action instanceof IIcfgCallTransition<?>) {
				roots.add(transitionProvider.getTarget(action));
			}
		}
		final Set<IPredicate> heads = new HashSet<>();
		final Set<IPredicate> visited = new HashSet<>();
		final Set<IPredicate> onStack = new HashSet<>();
		// Iterative, a program with long straight-line code would overflow the call stack.
		final Deque<Frame> stack = new ArrayDeque<>();
		for (final IPredicate root : roots) {
			if (!visited.add(root)) {
				continue;
			}
			onStack.add(root);
			stack.push(new Frame(root, successors(transitionProvider, returnSites, root)));
			while (!stack.isEmpty()) {
				final Frame frame = stack.peek();
				if (!frame.successors().hasNext()) {
					onStack.remove(frame.state());
					stack.pop();
					continue;
				}
				final IPredicate succ = frame.successors().next();
				if (onStack.contains(succ)) {
					heads.add(succ);
				} else if (visited.add(succ)) {
					onStack.add(succ);
					stack.push(new Frame(succ, successors(transitionProvider, returnSites, succ)));
				}
			}
		}
		return heads;
	}

	private record Frame(IPredicate state, Iterator<IPredicate> successors) {
	}
}
