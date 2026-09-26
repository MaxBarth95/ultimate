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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.invariants;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.CallNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.kinduction.IInvariantSupplier;

/**
 * The outgoing channel of an {@link InvariantSupplier} for one consumer. The supplier puts the locations whose
 * invariant got stronger, each with its whole current invariant, into the queue; {@link #update()} takes them without
 * waiting, and {@link #getInvariant} copies the latest invariant of a location into the consumer's script.
 * <p>
 * Everything but {@link #offer} must be called by the thread that owns {@code target}.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class InvariantSubscription implements IInvariantSupplier<CallNode<IPredicate>> {

	private final ManagedScript mSource;
	private final ManagedScript mTarget;
	private final BlockingQueue<Map<IcfgLocation, Term>> mQueue = new LinkedBlockingQueue<>();
	// the invariants taken so far, as terms of mSource
	private final Map<IcfgLocation, Term> mInvariants = new HashMap<>();
	// term of mSource -> its copy in mTarget, so that an unchanged invariant is always the very same object
	private final Map<Term, Term> mTransferred = new HashMap<>();
	private TermTransferrer mTransferrer;

	InvariantSubscription(final ManagedScript source, final ManagedScript target) {
		mSource = source;
		mTarget = target;
	}

	/**
	 * Called by the supplier.
	 */
	void offer(final Map<IcfgLocation, Term> invariants) {
		mQueue.add(invariants);
	}

	@Override
	public boolean update() {
		boolean changed = false;
		Map<IcfgLocation, Term> invariants;
		while ((invariants = mQueue.poll()) != null) {
			mInvariants.putAll(invariants);
			changed = true;
		}
		return changed;
	}

	@Override
	public Optional<Term> getInvariant(final CallNode<IPredicate> loopHead, final ManagedScript targetScript) {
		if (targetScript != mTarget) {
			throw new IllegalArgumentException(
					"this subscription delivers terms of " + mTarget + ", but they were asked for " + targetScript);
		}
		// A location invariant holds in every calling context, hence for every call node of the location.
		final Term invariant = mInvariants.get(InvariantSupplier.locationOf(loopHead.getState()));
		if (invariant == null) {
			return Optional.empty();
		}
		return Optional.of(mTransferred.computeIfAbsent(invariant, this::transfer));
	}

	private Term transfer(final Term invariant) {
		if (mTransferrer == null) {
			mTransferrer = new TermTransferrer(mSource.getScript(), mTarget.getScript());
		}
		return mTransferrer.transform(invariant);
	}
}
