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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * The affine hull of a set of points in Q^n, as the linear equalities that every point satisfies. Pure linear algebra,
 * no solver.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class AffineHull {

	/**
	 * An equality {@code sum_i coefficients[i] * x_i = constant} with coprime integer coefficients, the first nonzero
	 * one positive.
	 */
	public record Equality(BigInteger[] coefficients, BigInteger constant) {
		/** @return how many coefficients are nonzero */
		public int support() {
			return (int) Arrays.stream(coefficients).filter(c -> c.signum() != 0).count();
		}
	}

	/**
	 * The result of {@link #compute}.
	 *
	 * @param equalities
	 *            a basis of the equalities every point satisfies, one per free column of the reduced row echelon form,
	 *            so each one is sparse: its free variable and the pivot variables
	 * @param rank
	 *            the dimension of the hull; the points are evidence for the equalities only if there are more than
	 *            {@code rank + 1} of them, otherwise every set of points in general position has such a hull
	 */
	public record Result(List<Equality> equalities, int rank) {
	}

	private AffineHull() {
	}

	/**
	 * @param points
	 *            at least one point, each with the same dimension
	 */
	public static Result compute(final List<Rational[]> points) {
		if (points.isEmpty()) {
			throw new IllegalArgumentException("the affine hull of no point");
		}
		final Rational[] base = points.get(0);
		final int n = base.length;
		// rows: the differences of the other points to the first one
		final List<Rational[]> rows = new ArrayList<>();
		for (int i = 1; i < points.size(); i++) {
			final Rational[] point = points.get(i);
			if (point.length != n) {
				throw new IllegalArgumentException("points of different dimensions");
			}
			final Rational[] row = new Rational[n];
			for (int j = 0; j < n; j++) {
				row[j] = point[j].sub(base[j]);
			}
			rows.add(row);
		}
		final int[] pivotColumnOfRow = reduce(rows, n);
		final int rank = pivotColumnOfRow.length;
		final boolean[] isPivot = new boolean[n];
		for (final int column : pivotColumnOfRow) {
			isPivot[column] = true;
		}
		final List<Equality> equalities = new ArrayList<>();
		for (int free = 0; free < n; free++) {
			if (isPivot[free]) {
				continue;
			}
			// x_free = 1, x_pivot(r) = -rows[r][free]: a vector orthogonal to every difference
			final Rational[] vector = new Rational[n];
			Arrays.fill(vector, Rational.ZERO);
			vector[free] = Rational.ONE;
			for (int r = 0; r < rank; r++) {
				vector[pivotColumnOfRow[r]] = rows.get(r)[free].negate();
			}
			equalities.add(toEquality(vector, base));
		}
		return new Result(equalities, rank);
	}

	/**
	 * Brings {@code rows} into reduced row echelon form, in place; rows that become zero are removed.
	 *
	 * @return the pivot column of each remaining row
	 */
	private static int[] reduce(final List<Rational[]> rows, final int n) {
		final List<Integer> pivots = new ArrayList<>();
		int row = 0;
		for (int column = 0; column < n && row < rows.size(); column++) {
			int pivot = -1;
			for (int r = row; r < rows.size(); r++) {
				if (rows.get(r)[column].signum() != 0) {
					pivot = r;
					break;
				}
			}
			if (pivot < 0) {
				continue;
			}
			final Rational[] tmp = rows.get(row);
			rows.set(row, rows.get(pivot));
			rows.set(pivot, tmp);
			final Rational[] pivotRow = rows.get(row);
			final Rational inverse = pivotRow[column].inverse();
			for (int j = 0; j < n; j++) {
				pivotRow[j] = pivotRow[j].mul(inverse);
			}
			for (int r = 0; r < rows.size(); r++) {
				if (r == row || rows.get(r)[column].signum() == 0) {
					continue;
				}
				final Rational factor = rows.get(r)[column];
				final Rational[] other = rows.get(r);
				for (int j = 0; j < n; j++) {
					other[j] = other[j].sub(factor.mul(pivotRow[j]));
				}
			}
			pivots.add(column);
			row++;
		}
		while (rows.size() > row) {
			rows.remove(rows.size() - 1);
		}
		return pivots.stream().mapToInt(Integer::intValue).toArray();
	}

	private static Equality toEquality(final Rational[] vector, final Rational[] point) {
		BigInteger lcm = BigInteger.ONE;
		for (final Rational r : vector) {
			lcm = lcm(lcm, r.denominator());
		}
		final BigInteger[] coefficients = new BigInteger[vector.length];
		BigInteger gcd = BigInteger.ZERO;
		for (int j = 0; j < vector.length; j++) {
			coefficients[j] = vector[j].mul(lcm).numerator();
			gcd = gcd.gcd(coefficients[j]);
		}
		int sign = 1;
		for (final BigInteger c : coefficients) {
			if (c.signum() != 0) {
				sign = c.signum();
				break;
			}
		}
		final BigInteger divisor = sign < 0 ? gcd.negate() : gcd;
		Rational constant = Rational.ZERO;
		for (int j = 0; j < vector.length; j++) {
			coefficients[j] = coefficients[j].divide(divisor);
			constant = constant.add(point[j].mul(coefficients[j]));
		}
		if (!constant.isIntegral()) {
			// Cannot happen for integer points, which are the only ones the supplier collects.
			throw new IllegalArgumentException("an integer equality with a non-integer constant " + constant);
		}
		return new Equality(coefficients, constant.numerator());
	}

	private static BigInteger lcm(final BigInteger a, final BigInteger b) {
		return a.divide(a.gcd(b)).multiply(b);
	}
}
