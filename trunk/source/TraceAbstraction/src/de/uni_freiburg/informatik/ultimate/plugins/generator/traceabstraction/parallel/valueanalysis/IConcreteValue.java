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

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
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
	 */
	final class ArrayValue implements IConcreteValue {
		private final IConcreteValue mDefault;
		private final Map<IConcreteValue, IConcreteValue> mEntries;
		private final int mHash;

		private ArrayValue(final IConcreteValue defaultValue, final Map<IConcreteValue, IConcreteValue> entries) {
			mDefault = Objects.requireNonNull(defaultValue);
			mEntries = entries;
			mHash = 31 * mDefault.hashCode() + mEntries.hashCode();
		}

		/**
		 * @return the array that maps every index to {@code value}
		 */
		public static ArrayValue constant(final IConcreteValue value) {
			return new ArrayValue(value, Collections.emptyMap());
		}

		public IConcreteValue select(final IConcreteValue index) {
			return mEntries.getOrDefault(index, mDefault);
		}

		public ArrayValue store(final IConcreteValue index, final IConcreteValue value) {
			if (value.equals(select(index))) {
				return this;
			}
			final Map<IConcreteValue, IConcreteValue> entries = new HashMap<>(mEntries);
			if (value.equals(mDefault)) {
				entries.remove(index);
			} else {
				entries.put(index, value);
			}
			return new ArrayValue(mDefault, Collections.unmodifiableMap(entries));
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
			return mHash == other.mHash && mDefault.equals(other.mDefault) && mEntries.equals(other.mEntries);
		}

		@Override
		public String toString() {
			return "(const " + mDefault + ")" + (mEntries.isEmpty() ? "" : mEntries.toString());
		}
	}
}
