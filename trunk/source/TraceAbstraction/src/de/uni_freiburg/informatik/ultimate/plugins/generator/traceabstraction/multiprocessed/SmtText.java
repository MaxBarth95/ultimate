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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 * Reads the SMT-LIB pieces of a {@link ProgramPackage}: s-expressions, sorts and the declaration commands. Formulas are
 * parsed by the SMT-LIB parser itself, see {@link ProgramPackageReader}.
 */
final class SmtText {

	/**
	 * An s-expression: an atom (a symbol without its {@code |} quotes, or a numeral) or a list, with its source text.
	 */
	record SExpr(String atom, List<SExpr> list, String text) {
		boolean isAtom() {
			return atom != null;
		}

		String atomOrThrow() {
			if (atom == null) {
				throw new IllegalArgumentException("Expected an atom, got " + this);
			}
			return atom;
		}

		List<SExpr> listOrThrow() {
			if (list == null) {
				throw new IllegalArgumentException("Expected a list, got " + atom);
			}
			return list;
		}

		@Override
		public String toString() {
			return atom != null ? atom : list.toString();
		}
	}

	private final String mText;
	private int mPos;

	private SmtText(final String text) {
		mText = text;
	}

	/**
	 * @return the one s-expression of {@code text}
	 * @throws IllegalArgumentException
	 *             if the text is not exactly one s-expression
	 */
	static SExpr parse(final String text) {
		final SmtText reader = new SmtText(text);
		final SExpr result = reader.next();
		reader.skipSpace();
		if (reader.mPos != text.length()) {
			throw new IllegalArgumentException("Trailing text after an s-expression: " + text);
		}
		return result;
	}

	private void skipSpace() {
		while (mPos < mText.length() && Character.isWhitespace(mText.charAt(mPos))) {
			mPos++;
		}
	}

	private SExpr next() {
		skipSpace();
		if (mPos >= mText.length()) {
			throw new IllegalArgumentException("Unexpected end of an s-expression: " + mText);
		}
		final int begin = mPos;
		final char c = mText.charAt(mPos);
		if (c == '(') {
			mPos++;
			final List<SExpr> items = new ArrayList<>();
			while (true) {
				skipSpace();
				if (mPos >= mText.length()) {
					throw new IllegalArgumentException("Unbalanced parentheses: " + mText);
				}
				if (mText.charAt(mPos) == ')') {
					mPos++;
					return new SExpr(null, items, mText.substring(begin, mPos));
				}
				items.add(next());
			}
		}
		if (c == ')') {
			throw new IllegalArgumentException("Unexpected ')' in " + mText);
		}
		if (c == '|') {
			final int end = mText.indexOf('|', mPos + 1);
			if (end < 0) {
				throw new IllegalArgumentException("Unterminated quoted symbol in " + mText);
			}
			final String symbol = mText.substring(mPos + 1, end);
			mPos = end + 1;
			return new SExpr(symbol, null, mText.substring(begin, mPos));
		}
		if (c == '"') {
			throw new IllegalArgumentException("String literals are not supported in declarations: " + mText);
		}
		final int start = mPos;
		while (mPos < mText.length() && !Character.isWhitespace(mText.charAt(mPos)) && mText.charAt(mPos) != '('
				&& mText.charAt(mPos) != ')') {
			mPos++;
		}
		return new SExpr(mText.substring(start, mPos), null, mText.substring(start, mPos));
	}

	/**
	 * @return the sort of an s-expression: {@code Int}, {@code (Array Int Int)}, {@code (_ BitVec 32)}, ...
	 */
	static Sort sort(final Script script, final SExpr expr) {
		if (expr.isAtom()) {
			return script.sort(expr.atom());
		}
		final List<SExpr> items = expr.list();
		if (items.isEmpty()) {
			throw new IllegalArgumentException("Empty sort");
		}
		if (items.get(0).isAtom() && "_".equals(items.get(0).atom())) {
			// an indexed sort without arguments
			return script.sort(items.get(1).atomOrThrow(), indices(items.subList(2, items.size())));
		}
		final Sort[] args = new Sort[items.size() - 1];
		for (int i = 1; i < items.size(); i++) {
			args[i - 1] = sort(script, items.get(i));
		}
		final SExpr head = items.get(0);
		if (head.isAtom()) {
			return script.sort(head.atom(), args);
		}
		final List<SExpr> indexed = head.listOrThrow();
		if (indexed.size() < 2 || !"_".equals(indexed.get(0).atom())) {
			throw new IllegalArgumentException("Malformed sort " + expr);
		}
		return script.sort(indexed.get(1).atomOrThrow(), indices(indexed.subList(2, indexed.size())), args);
	}

	static Sort sort(final Script script, final String text) {
		return sort(script, parse(text));
	}

	private static String[] indices(final List<SExpr> items) {
		final String[] result = new String[items.size()];
		for (int i = 0; i < items.size(); i++) {
			result[i] = items.get(i).atomOrThrow();
		}
		return result;
	}

	private static Sort[] sorts(final Script script, final List<SExpr> items) {
		final Sort[] result = new Sort[items.size()];
		for (int i = 0; i < items.size(); i++) {
			result[i] = sort(script, items.get(i));
		}
		return result;
	}

	/**
	 * A declaration command: {@code declare-sort}, {@code declare-fun} or {@code define-fun}.
	 *
	 * @param command
	 *            the command name
	 * @param name
	 *            the declared symbol
	 * @param parts
	 *            the s-expression of the whole command
	 */
	record Declaration(String command, String name, List<SExpr> parts) {
	}

	static Declaration declaration(final String text) {
		final List<SExpr> parts = parse(text).listOrThrow();
		if (parts.size() < 3) {
			throw new IllegalArgumentException("Malformed declaration " + text);
		}
		return new Declaration(parts.get(0).atomOrThrow(), parts.get(1).atomOrThrow(), parts);
	}

	/**
	 * Executes a {@code declare-sort} or {@code declare-fun} on the script.
	 */
	static void declare(final Script script, final Declaration declaration) {
		final List<SExpr> parts = declaration.parts();
		switch (declaration.command()) {
		case "declare-sort":
			require(parts.size() == 3, declaration);
			script.declareSort(declaration.name(), Integer.parseInt(parts.get(2).atomOrThrow()));
			break;
		case "declare-fun":
			require(parts.size() == 4, declaration);
			script.declareFun(declaration.name(), sorts(script, parts.get(2).listOrThrow()), sort(script, parts.get(3)));
			break;
		default:
			throw new IllegalArgumentException("Not a declaration: " + declaration.command());
		}
	}

	/**
	 * @return the parameters {@code ((p s) ...)} of a {@code define-fun}, each as its name and sort expression
	 */
	static List<SExpr[]> parameters(final Declaration declaration) {
		require("define-fun".equals(declaration.command()) && declaration.parts().size() == 5, declaration);
		final List<SExpr[]> result = new ArrayList<>();
		for (final SExpr param : declaration.parts().get(2).listOrThrow()) {
			final List<SExpr> pair = param.listOrThrow();
			require(pair.size() == 2, declaration);
			result.add(new SExpr[] { pair.get(0), pair.get(1) });
		}
		return result;
	}

	private static void require(final boolean condition, final Declaration declaration) {
		if (!condition) {
			throw new IllegalArgumentException("Malformed " + declaration.command() + " " + declaration.parts());
		}
	}
}
