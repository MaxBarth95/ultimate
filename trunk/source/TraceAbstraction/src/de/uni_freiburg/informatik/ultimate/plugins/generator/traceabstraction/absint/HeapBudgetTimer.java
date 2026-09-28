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

import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * A timer that also expires when the JVM uses more heap than a budget allows. It bounds a domain of the AbsInt worker
 * in memory the way the wrapped timer bounds it in time: everything that polls {@link #continueProcessing()} (the
 * fixpoint engine between posts, the nonrelational evaluators inside a post) stops once either budget is exceeded.
 * <p>
 * The used heap of the whole JVM counts, garbage included, so the heap of other workers counts as well. That is
 * intended: a domain that allocates faster than the collector frees makes the JVM grow its heap, which it does not
 * return, and that is what exceeds the memory limit of the process.
 *
 * @author Max Barth (Max.Barth@lmu.de)
 */
public final class HeapBudgetTimer implements IProgressAwareTimer {

	private final IProgressAwareTimer mTimer;
	private final long mBudgetBytes;
	// Timers created from this one report to the same root, so the caller only has to ask the timer it created.
	private final HeapBudgetTimer mRoot;
	private long mHeapUsedWhenExceeded = -1;

	public HeapBudgetTimer(final IProgressAwareTimer timer, final long budgetBytes) {
		this(timer, budgetBytes, null);
	}

	private HeapBudgetTimer(final IProgressAwareTimer timer, final long budgetBytes, final HeapBudgetTimer root) {
		if (budgetBytes <= 0) {
			throw new IllegalArgumentException("The heap budget must be positive, but is " + budgetBytes);
		}
		mTimer = timer;
		mBudgetBytes = budgetBytes;
		mRoot = root == null ? this : root;
	}

	@Override
	public boolean continueProcessing() {
		if (!mTimer.continueProcessing()) {
			return false;
		}
		final Runtime runtime = Runtime.getRuntime();
		final long used = runtime.totalMemory() - runtime.freeMemory();
		if (used > mBudgetBytes) {
			mRoot.mHeapUsedWhenExceeded = used;
			return false;
		}
		return true;
	}

	/**
	 * @return whether this timer, or one created from it, expired because of the heap budget
	 */
	public boolean isHeapBudgetExceeded() {
		return mRoot.mHeapUsedWhenExceeded >= 0;
	}

	/**
	 * @return the used heap in bytes that exceeded the budget, or -1 if the budget was not exceeded
	 */
	public long getHeapUsedWhenExceeded() {
		return mRoot.mHeapUsedWhenExceeded;
	}

	@Override
	public IProgressAwareTimer getChildTimer(final long timeout) {
		return new HeapBudgetTimer(mTimer.getChildTimer(timeout), mBudgetBytes, mRoot);
	}

	@Override
	public IProgressAwareTimer getChildTimer(final double percentage) {
		return new HeapBudgetTimer(mTimer.getChildTimer(percentage), mBudgetBytes, mRoot);
	}

	@Override
	public IProgressAwareTimer getTimer(final long timeout) {
		return new HeapBudgetTimer(mTimer.getTimer(timeout), mBudgetBytes, mRoot);
	}

	@Override
	public IProgressAwareTimer getParent() {
		return mTimer.getParent();
	}

	@Override
	public long getDeadline() {
		return mTimer.getDeadline();
	}

	@Override
	public long remainingTime() {
		return mTimer.remainingTime();
	}
}
