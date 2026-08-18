/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction;

import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Extension point for an independent, CEGAR-agnostic analysis that can supply a loop invariant to strengthen
 * {@link KInduction}'s inductive step. A supplied invariant is used purely as a hypothesis (never re-proven by
 * {@link KInduction} itself), so it must already be sound on its own - a genuine over-approximation of every state
 * reachable at {@code loopHead}, e.g. as computed by an abstract-interpretation-style analysis. Assuming a sound
 * invariant can only prune the step-case search space (letting a smaller {@code k} become inductive); it can never
 * introduce unsoundness.
 *
 * @param <STATE>
 *            the automaton state type identifying a loop head, matching {@link KInduction}'s own {@code STATE}.
 */
public interface IInvariantSupplier<STATE> {

	/**
	 * @param loopHead
	 *            the loop head to supply an invariant for.
	 * @param targetScript
	 *            the {@link ManagedScript} the returned {@link Term} must already be native to (no cross-script
	 *            transfer is performed by the caller).
	 * @return a state predicate over {@code loopHead}'s own {@code IProgramVar}s, known to hold whenever control
	 *         reaches {@code loopHead}, or {@link Optional#empty()} if none is available.
	 */
	Optional<Term> getInvariant(STATE loopHead, ManagedScript targetScript);

	/**
	 * @return a supplier that never provides an invariant, i.e. plain (unstrengthened) k-induction.
	 */
	static <STATE> IInvariantSupplier<STATE> none() {
		return (loopHead, targetScript) -> Optional.empty();
	}
}
