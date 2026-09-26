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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.icfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.lib.icfg.Summary;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.IcfgTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgUtils;

/**
 * {@link IcfgTransitionProvider} over a nested word automaton: locations are its states, actions are its letters
 * themselves (so the engine's {@code instanceof} tests on actions keep working), which requires every letter to label
 * exactly one transition, as in the initial abstraction. All automaton access happens in the constructor; afterwards
 * only immutable indices are read, never the ICFG locations' edge lists, which other workers mutate concurrently.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class NwaTransitionProvider implements ITransitionProvider<IcfgEdge, IPredicate> {

	private final Map<IcfgEdge, IPredicate> mSource = new HashMap<>();
	private final Map<IcfgEdge, IPredicate> mTarget = new HashMap<>();
	private final Map<IPredicate, List<IcfgEdge>> mOutgoing = new HashMap<>();
	private final Map<IPredicate, List<IcfgEdge>> mIncoming = new HashMap<>();
	private final Set<IPredicate> mInitialStates;
	private final Set<IPredicate> mFinalStates;

	public <L extends IIcfgTransition<?>> NwaTransitionProvider(final INestedWordAutomaton<L, IPredicate> nwa) {
		for (final IPredicate state : nwa.getStates()) {
			for (final OutgoingInternalTransition<L, IPredicate> trans : nwa.internalSuccessors(state)) {
				addTransition(state, trans.getLetter(), trans.getSucc());
			}
			for (final OutgoingCallTransition<L, IPredicate> trans : nwa.callSuccessors(state)) {
				addTransition(state, trans.getLetter(), trans.getSucc());
			}
			// The hierarchical predecessor is not needed: a return is matched to its call by the scope predicates.
			for (final OutgoingReturnTransition<L, IPredicate> trans : nwa.returnSuccessors(state)) {
				addTransition(state, trans.getLetter(), trans.getSucc());
			}
		}
		mInitialStates = Collections.unmodifiableSet(new HashSet<>(nwa.getInitialStates()));
		mFinalStates = Collections.unmodifiableSet(new HashSet<>(nwa.getFinalStates()));
	}

	private void addTransition(final IPredicate source, final IIcfgTransition<?> letter, final IPredicate target) {
		if (!(letter instanceof IcfgEdge)) {
			throw new UnsupportedOperationException(
					"Letter " + letter + " is a " + letter.getClass().getSimpleName() + ", not an IcfgEdge");
		}
		final IcfgEdge edge = (IcfgEdge) letter;
		if (RcfgUtils.isSummaryWithImplementation(edge)) {
			// The fixpoint engine skips such summaries in favor of the call, which this automaton does not have.
			throw new UnsupportedOperationException("The abstraction contains the summary " + edge
					+ " of an implemented procedure, i.e. it is not interprocedural");
		}
		final IPredicate oldSource = mSource.putIfAbsent(edge, source);
		if (oldSource != null) {
			throw new UnsupportedOperationException("Letter " + edge + " labels more than one transition (from "
					+ oldSource + " and from " + source + "), so it cannot serve as an action");
		}
		mTarget.put(edge, target);
		mOutgoing.computeIfAbsent(source, x -> new ArrayList<>()).add(edge);
		mIncoming.computeIfAbsent(target, x -> new ArrayList<>()).add(edge);
	}

	public Set<IPredicate> getInitialStates() {
		return mInitialStates;
	}

	/**
	 * @return every letter of the automaton
	 */
	public Set<IcfgEdge> getActions() {
		return Collections.unmodifiableSet(mSource.keySet());
	}

	@Override
	public Collection<IcfgEdge> getSuccessors(final IcfgEdge action, final IcfgEdge scope) {
		final IPredicate target = mTarget.get(action);
		if (target == null) {
			return Collections.emptyList();
		}
		return getSuccessorActions(target).stream()
				.filter(a -> !(a instanceof IReturnAction) || isLeavingScope(a, scope)).collect(Collectors.toList());
	}

	@Override
	public Collection<IcfgEdge> getPredecessors(final IcfgEdge action, final IcfgEdge scope) {
		final IPredicate source = mSource.get(action);
		if (source == null) {
			return Collections.emptyList();
		}
		return getPredecessorActions(source).stream()
				.filter(a -> !(a instanceof ICallAction) || isEnteringScope(a, scope)).collect(Collectors.toList());
	}

	@Override
	public Collection<IcfgEdge> getSuccessorActions(final IPredicate loc) {
		return Collections.unmodifiableList(mOutgoing.getOrDefault(loc, Collections.emptyList()));
	}

	@Override
	public Collection<IcfgEdge> getPredecessorActions(final IPredicate loc) {
		return Collections.unmodifiableList(mIncoming.getOrDefault(loc, Collections.emptyList()));
	}

	@Override
	public boolean isErrorLocation(final IPredicate loc) {
		return mFinalStates.contains(loc);
	}

	@Override
	public boolean isEnteringScope(final IcfgEdge action) {
		return action instanceof IIcfgCallTransition<?>;
	}

	@Override
	public boolean isEnteringScope(final IcfgEdge action, final IcfgEdge scope) {
		if (action instanceof IIcfgCallTransition<?> && scope instanceof IIcfgReturnTransition<?, ?>) {
			return ((IIcfgReturnTransition<?, ?>) scope).getCorrespondingCall().equals(action);
		}
		return false;
	}

	@Override
	public boolean isLeavingScope(final IcfgEdge action, final IcfgEdge scope) {
		if (action instanceof IIcfgReturnTransition<?, ?>) {
			return RcfgUtils.isAllowedReturn((IIcfgReturnTransition<?, ?>) action, scope);
		}
		return false;
	}

	@Override
	public boolean isLeavingScope(final IcfgEdge action) {
		return action instanceof IIcfgReturnTransition<?, ?>;
	}

	@Override
	public boolean isSummaryForCall(final IcfgEdge action, final IcfgEdge call) {
		if (action instanceof CodeBlock && call instanceof CodeBlock) {
			return RcfgUtils.isSummaryForCall(action, call);
		}
		return false;
	}

	@Override
	public boolean isSummaryWithImplementation(final IcfgEdge action) {
		return RcfgUtils.isSummaryWithImplementation(action);
	}

	@Override
	public IPredicate getSource(final IcfgEdge action) {
		return mSource.get(action);
	}

	@Override
	public IPredicate getTarget(final IcfgEdge action) {
		return mTarget.get(action);
	}

	/**
	 * Always {@code null}: an interprocedural automaton has no summary letter for an implemented procedure. The
	 * engine then has no summary to reuse and analyzes the callee again, which costs time but not soundness.
	 */
	@Override
	public IcfgEdge getSummaryForCall(final IcfgEdge call) {
		if (!(call instanceof ICallAction)) {
			throw new IllegalArgumentException("call is not a Call");
		}
		return null;
	}

	@Override
	public String getProcedureName(final IcfgEdge action) {
		if (action == null) {
			return null;
		}
		if (action instanceof Summary) {
			return ((Summary) action).getCallStatement().getMethodName();
		}
		return action.getSucceedingProcedure();
	}

	@Override
	public String toLogString(final IcfgEdge action) {
		return action.toString();
	}
}
