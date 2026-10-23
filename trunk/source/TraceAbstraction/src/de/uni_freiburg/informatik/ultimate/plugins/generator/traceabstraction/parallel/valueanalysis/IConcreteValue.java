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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.valueanalysis;

import java.util.Map.Entry;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.FunctionalMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;

/**
 * A concrete value of an SMT sort, as the value analysis worker computes it without a solver. Values are immutable
 * and compare by value, so that a valuation of them can be hashed into the visited set of a search.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public sealed interface IConcreteValue
		permits IConcreteValue.BoolValue, IConcreteValue.NumberValue, IConcreteValue.BitvectorValue,
		IConcreteValue.ArrayValue {

	/**
	 * A value of sort Bool.
	 */
	record BoolValue(boolean value) implements IConcreteValue {
		public static final BoolValue TRUE = new BoolValue(true);
		public static final BoolValue FALSE = new BoolValue(false);

		public static BoolValue of(final boolean value) {
			return value ? TRUE : FALSE;
		}

		@Override
		public String toString() {
			return Boolean.toString(value);
		}
	}

	/**
	 * A value of sort Int or Real. An Int value is always integral.
	 */
	record NumberValue(Rational value) implements IConcreteValue {
		public NumberValue {
			Objects.requireNonNull(value);
		}

		@Override
		public String toString() {
			return value.toString();
		}
	}

	/**
	 * A value of a bitvector sort.
	 */
	record BitvectorValue(BitvectorConstant value) implements IConcreteValue {
		public BitvectorValue {
			Objects.requireNonNull(value);
		}

		@Override
		public String toString() {
			return value.toString();
		}
	}

	/**
	 * A value of an array sort: a default for every index plus finitely many indices that differ from it. The
	 * representation is canonical, no explicit entry equals the default, so that two arrays that agree on every index
	 * this representation can tell apart are equal. (For a finite index sort an array that lists every index
	 * explicitly differs from the constant array with the same values. That costs at most a missed equality, which
	 * only makes the analysis drop a successor.)
	 * <p>
	 * The entries are a persistent map, so a store shares all other entries with the array it was made from. Every
	 * configuration of a search keeps its own arrays, and copying them on each store made a loop that fills an array
	 * use memory quadratic in its length. The hash is that of a {@link java.util.Map} of the entries, updated per
	 * store.
	 * <p>
	 * An array also remembers the array and the index it was stored from. A transition formula such as
	 * {@code a' = (store a i v)} compares the array it computed with one computed the same way; such two arrays are
	 * equal if they agree at that index, which spares comparing all entries in every step.
	 */
	final class ArrayValue implements IConcreteValue {
		private final IConcreteValue mDefault;
		private final FunctionalMap<IConcreteValue, IConcreteValue> mEntries;
		// Sum of key.hashCode() ^ value.hashCode() over the entries, as Map.hashCode; FunctionalMap's own hashCode
		// recurses into its subtrees, because each node is a map and an entry at once.
		private final int mEntriesHash;
		private final int mHash;
		// The array this one was stored from, and at which index; both null for a constant array
		private final ArrayValue mStoredFrom;
		private final IConcreteValue mStoredAt;

		private ArrayValue(final IConcreteValue defaultValue,
				final FunctionalMap<IConcreteValue, IConcreteValue> entries, final int entriesHash,
				final ArrayValue storedFrom, final IConcreteValue storedAt) {
			mDefault = Objects.requireNonNull(defaultValue);
			mEntries = entries;
			mEntriesHash = entriesHash;
			mHash = 31 * mDefault.hashCode() + mEntriesHash;
			mStoredFrom = storedFrom;
			mStoredAt = storedAt;
		}

		/**
		 * @return the array that maps every index to {@code value}
		 */
		public static ArrayValue constant(final IConcreteValue value) {
			return new ArrayValue(value, FunctionalMap.empty(), 0, null, null);
		}

		public IConcreteValue select(final IConcreteValue index) {
			final IConcreteValue value = mEntries.get(index);
			return value == null ? mDefault : value;
		}

		public ArrayValue store(final IConcreteValue index, final IConcreteValue value) {
			final IConcreteValue old = mEntries.get(index);
			if (value.equals(old == null ? mDefault : old)) {
				return this;
			}
			FunctionalMap<IConcreteValue, IConcreteValue> entries = mEntries;
			int entriesHash = mEntriesHash;
			if (old != null) {
				// insert does not replace an entry, it would add a second one for the index
				entries = entries.delete(index);
				entriesHash -= index.hashCode() ^ old.hashCode();
			}
			if (!value.equals(mDefault)) {
				entries = entries.insert(index, value);
				entriesHash += index.hashCode() ^ value.hashCode();
			}
			return new ArrayValue(mDefault, entries, entriesHash, this, index);
		}

		@Override
		public int hashCode() {
			return mHash;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (!(obj instanceof final ArrayValue other)) {
				return false;
			}
			if (mHash != other.mHash || !mDefault.equals(other.mDefault) || mEntries.size() != other.mEntries.size()) {
				return false;
			}
			if (mEntries == other.mEntries) {
				return true;
			}
			if (mStoredFrom != null && mStoredFrom == other.mStoredFrom && mStoredAt.equals(other.mStoredAt)) {
				// both are the same array with one index overwritten
				return select(mStoredAt).equals(other.select(mStoredAt));
			}
			for (final Entry<IConcreteValue, IConcreteValue> entry : mEntries.entrySet()) {
				if (!entry.getValue().equals(other.mEntries.get(entry.getKey()))) {
					return false;
				}
			}
			return true;
		}

		@Override
		public String toString() {
			if (mEntries.isEmpty()) {
				return "(const " + mDefault + ")";
			}
			final StringBuilder sb = new StringBuilder("(const " + mDefault + "){");
			String separator = "";
			for (final Entry<IConcreteValue, IConcreteValue> entry : mEntries.entrySet()) {
				sb.append(separator).append(entry.getKey()).append('=').append(entry.getValue());
				separator = ", ";
			}
			return sb.append('}').toString();
		}
	}
}
