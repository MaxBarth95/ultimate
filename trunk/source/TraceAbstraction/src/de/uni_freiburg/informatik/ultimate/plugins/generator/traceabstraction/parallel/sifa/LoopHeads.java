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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.sifa;

import java.util.ArrayDeque;
import java.util.ArrayList;
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

import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.LoopTreeFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * The loop heads of a program, found the way the loop tree of k-induction finds them (see
 * {@link LoopTreeFormulaBuilder}): the entries of every nontrivial strongly connected component, and then, recursively,
 * those of the components that remain once the heads are taken out. An irreducible loop has several heads, and a loop
 * made of gotos has heads too, unlike {@link IIcfg#getLoopLocations()}. The graph is intraprocedural: a call site is an
 * edge from the call's source to the return's target, and the entry of a procedure is an entry of a loop through it.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
final class LoopHeads {

	private final Map<IcfgLocation, Set<IcfgLocation>> mSuccessors = new HashMap<>();
	private final Map<IcfgLocation, Set<IcfgLocation>> mPredecessors = new HashMap<>();

	private LoopHeads(final IIcfg<IcfgLocation> program) {
		for (final IcfgLocation location : IcfgUtils.getAllLocations(program).collect(Collectors.toList())) {
			for (final IcfgEdge edge : location.getOutgoingEdges()) {
				if (edge instanceof IIcfgCallTransition<?>) {
					// Leaves the procedure, the return's call-site edge stands for it.
					continue;
				}
				final IcfgLocation source = edge instanceof IIcfgReturnTransition<?, ?>
						? ((IIcfgReturnTransition<?, ?>) edge).getCallerProgramPoint()
						: location;
				mSuccessors.computeIfAbsent(source, x -> new LinkedHashSet<>()).add(edge.getTarget());
				mPredecessors.computeIfAbsent(edge.getTarget(), x -> new LinkedHashSet<>()).add(source);
			}
		}
	}

	static Set<IcfgLocation> of(final IIcfg<IcfgLocation> program) {
		final Set<IcfgLocation> entries = new HashSet<>(program.getInitialNodes());
		entries.addAll(program.getProcedureEntryNodes().values());
		final Set<IcfgLocation> heads = new LinkedHashSet<>();
		new LoopHeads(program).collect(IcfgUtils.getAllLocations(program).collect(Collectors.toSet()), entries,
				heads);
		return heads;
	}

	/**
	 * Adds the heads of the loops in {@code region}, and of the loops nested in them, to {@code heads}.
	 *
	 * @param entries
	 *            locations that count as entered from outside, wherever their predecessors are
	 */
	private void collect(final Set<IcfgLocation> region, final Set<IcfgLocation> entries,
			final Set<IcfgLocation> heads) {
		for (final Set<IcfgLocation> loop : nontrivialSccs(region)) {
			final Set<IcfgLocation> loopHeads = new LinkedHashSet<>();
			for (final IcfgLocation location : loop) {
				if (entries.contains(location) || !loop.containsAll(predecessors(location))) {
					loopHeads.add(location);
				}
			}
			heads.addAll(loopHeads);
			final Set<IcfgLocation> inner = new HashSet<>(loop);
			inner.removeAll(loopHeads);
			collect(inner, Collections.emptySet(), heads);
		}
	}

	private Set<IcfgLocation> predecessors(final IcfgLocation location) {
		return mPredecessors.getOrDefault(location, Collections.emptySet());
	}

	/**
	 * Tarjan's algorithm on the subgraph of {@code nodes}, without recursion: a program can have many locations.
	 */
	private List<Set<IcfgLocation>> nontrivialSccs(final Set<IcfgLocation> nodes) {
		final List<Set<IcfgLocation>> result = new ArrayList<>();
		final Map<IcfgLocation, Integer> index = new HashMap<>();
		final Map<IcfgLocation, Integer> lowLink = new HashMap<>();
		final Deque<IcfgLocation> sccStack = new ArrayDeque<>();
		final Set<IcfgLocation> onStack = new HashSet<>();
		for (final IcfgLocation start : nodes) {
			if (index.containsKey(start)) {
				continue;
			}
			final Deque<IcfgLocation> dfsNodes = new ArrayDeque<>();
			final Deque<Iterator<IcfgLocation>> dfsIterators = new ArrayDeque<>();
			visit(start, nodes, index, lowLink, sccStack, onStack, dfsNodes, dfsIterators);
			while (!dfsNodes.isEmpty()) {
				final IcfgLocation node = dfsNodes.peek();
				final Iterator<IcfgLocation> it = dfsIterators.peek();
				if (it.hasNext()) {
					final IcfgLocation next = it.next();
					if (!index.containsKey(next)) {
						visit(next, nodes, index, lowLink, sccStack, onStack, dfsNodes, dfsIterators);
					} else if (onStack.contains(next)) {
						lowLink.put(node, Math.min(lowLink.get(node), index.get(next)));
					}
					continue;
				}
				dfsNodes.pop();
				dfsIterators.pop();
				if (!dfsNodes.isEmpty()) {
					final IcfgLocation parent = dfsNodes.peek();
					lowLink.put(parent, Math.min(lowLink.get(parent), lowLink.get(node)));
				}
				if (lowLink.get(node).equals(index.get(node))) {
					final Set<IcfgLocation> scc = new LinkedHashSet<>();
					IcfgLocation member;
					do {
						member = sccStack.pop();
						onStack.remove(member);
						scc.add(member);
					} while (member != node);
					if (scc.size() > 1 || successors(node, nodes).contains(node)) {
						result.add(scc);
					}
				}
			}
		}
		return result;
	}

	private void visit(final IcfgLocation node, final Set<IcfgLocation> nodes, final Map<IcfgLocation, Integer> index,
			final Map<IcfgLocation, Integer> lowLink, final Deque<IcfgLocation> sccStack,
			final Set<IcfgLocation> onStack, final Deque<IcfgLocation> dfsNodes,
			final Deque<Iterator<IcfgLocation>> dfsIterators) {
		index.put(node, index.size());
		lowLink.put(node, index.get(node));
		sccStack.push(node);
		onStack.add(node);
		dfsNodes.push(node);
		dfsIterators.push(successors(node, nodes).iterator());
	}

	private Set<IcfgLocation> successors(final IcfgLocation location, final Set<IcfgLocation> nodes) {
		final Set<IcfgLocation> result = new LinkedHashSet<>(mSuccessors.getOrDefault(location, Collections.emptySet()));
		result.retainAll(nodes);
		return result;
	}
}
