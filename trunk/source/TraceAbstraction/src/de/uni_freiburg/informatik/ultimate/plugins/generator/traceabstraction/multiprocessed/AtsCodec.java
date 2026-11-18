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

import java.io.StringReader;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.AutomataDefinitionInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AutomataScriptParserRun;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedwordAutomatonAST;

/**
 * Prints and parses the automata of the exchange (format ATS_V1).
 *
 * <ul>
 * <li>Letters are {@link LetterNaming} names.</li>
 * <li>A state of an abstraction is {@code q<n>@<location>}: only its program point, as a {@link LocationNaming}
 * name. The receiver builds its own predicates for it.</li>
 * <li>A state of an interpolant automaton is {@code q<n>#<formula>}: only its formula, in SMT-LIB over the program
 * variables.</li>
 * </ul>
 *
 * The number {@code n} comes from a breadth-first search from the initial states that visits the outgoing
 * transitions of a state ordered by letter name. It does not depend on predicate serial numbers or on hash order, so
 * equal deterministic automata print to equal bytes. That makes the print of the initial abstraction a fingerprint of
 * the program. The printer writes no header and no timestamp.
 *
 * @param <L>
 *            the letter type
 */
public final class AtsCodec<L extends IIcfgTransition<?>> {

	private static final Pattern ABSTRACTION_STATE = Pattern.compile("q(\\d+)@(.+)");
	private static final Pattern INTERPOLANT_STATE = Pattern.compile("q(\\d+)#(.+)", Pattern.DOTALL);
	private static final String SOURCE_NAME = "exchange.ats";

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final LetterNaming<L> mLetters;

	public AtsCodec(final IUltimateServiceProvider services, final ILogger logger, final LetterNaming<L> letters) {
		mServices = services;
		mLogger = logger;
		mLetters = letters;
	}

	/**
	 * Prints an abstraction whose states are program points.
	 *
	 * @throws IllegalArgumentException
	 *             if a state is not an {@link ISLPredicate}, or a letter is not in the alphabet
	 */
	public String printAbstraction(final String name, final INestedWordAutomaton<L, IPredicate> abstraction,
			final LocationNaming locations) {
		return print(name, abstraction, state -> {
			if (!(state instanceof ISLPredicate)) {
				throw new IllegalArgumentException("Abstraction state without a single program point: " + state);
			}
			return "@" + locations.name(((ISLPredicate) state).getProgramPoint());
		});
	}

	/**
	 * Prints an interpolant automaton whose states are formulas.
	 */
	public String printInterpolantAutomaton(final String name, final INestedWordAutomaton<L, IPredicate> automaton) {
		return print(name, automaton, state -> "#" + state.getFormula().toStringDirect());
	}

	/**
	 * Parses an abstraction. Each state gets the predicate {@code stateForLocation} builds for its program point; the
	 * states stay distinct even if they share a program point.
	 *
	 * @throws IllegalArgumentException
	 *             if the text is no nested word automaton, a letter or program point is unknown, or the alphabet
	 *             differs from the local one
	 */
	public NestedWordAutomaton<L, IPredicate> parseAbstraction(final String ats, final LocationNaming locations,
			final Function<IcfgLocation, IPredicate> stateForLocation,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		final INestedWordAutomaton<String, String> raw = parseRaw(ats);
		final Map<String, IPredicate> states = new HashMap<>();
		for (final String state : raw.getStates()) {
			final Matcher match = ABSTRACTION_STATE.matcher(state);
			if (!match.matches()) {
				throw new IllegalArgumentException("Malformed abstraction state: " + state);
			}
			states.put(state, stateForLocation.apply(locations.resolve(match.group(2))));
		}
		return translate(raw, states, emptyStackFactory);
	}

	/**
	 * Parses an interpolant automaton. Each formula becomes the predicate {@code formulaToPredicate} returns for it,
	 * which is expected to unify equal formulas.
	 *
	 * @throws IllegalArgumentException
	 *             if the text is no nested word automaton, a letter is unknown, or the alphabet differs from the local
	 *             one; {@code formulaToPredicate} throws if a formula does not parse
	 */
	public NestedWordAutomaton<L, IPredicate> parseInterpolantAutomaton(final String ats,
			final Function<String, IPredicate> formulaToPredicate,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		final INestedWordAutomaton<String, String> raw = parseRaw(ats);
		final Map<String, IPredicate> states = new HashMap<>();
		for (final String state : raw.getStates()) {
			final Matcher match = INTERPOLANT_STATE.matcher(state);
			if (!match.matches()) {
				throw new IllegalArgumentException("Malformed interpolant automaton state: " + state);
			}
			states.put(state, formulaToPredicate.apply(match.group(2)));
		}
		return translate(raw, states, emptyStackFactory);
	}

	private String print(final String name, final INestedWordAutomaton<L, IPredicate> nwa,
			final Function<IPredicate, String> stateSuffix) {
		final Map<IPredicate, String> stateNames = numberStates(nwa, stateSuffix);
		final VpAlphabet<L> alphabet = nwa.getVpAlphabet();
		final VpAlphabet<String> stringAlphabet = new VpAlphabet<>(escapedNames(alphabet.getInternalAlphabet()),
				escapedNames(alphabet.getCallAlphabet()), escapedNames(alphabet.getReturnAlphabet()));
		final AutomataLibraryServices services = new AutomataLibraryServices(mServices);
		final NestedWordAutomaton<String, String> printable =
				new NestedWordAutomaton<>(services, stringAlphabet, new StringFactory());
		// the same automaton with unescaped names, to check the round trip
		final List<String> signature = new ArrayList<>();
		for (final Map.Entry<IPredicate, String> entry : stateNames.entrySet()) {
			final boolean isInitial = nwa.isInitial(entry.getKey());
			final boolean isFinal = nwa.isFinal(entry.getKey());
			printable.addState(isInitial, isFinal, escape(entry.getValue()));
			signature.add(entry(STATE_ENTRY, entry.getValue(), String.valueOf(isInitial), String.valueOf(isFinal)));
		}
		for (final IPredicate state : stateNames.keySet()) {
			final String pred = stateNames.get(state);
			for (final OutgoingInternalTransition<L, IPredicate> t : sortedInternal(nwa, state)) {
				final String succ = stateNames.get(t.getSucc());
				printable.addInternalTransition(escape(pred), escapedName(t.getLetter()), escape(succ));
				signature.add(entry(INTERNAL_ENTRY, pred, mLetters.name(t.getLetter()), succ));
			}
			for (final OutgoingCallTransition<L, IPredicate> t : sortedCall(nwa, state)) {
				final String succ = stateNames.get(t.getSucc());
				printable.addCallTransition(escape(pred), escapedName(t.getLetter()), escape(succ));
				signature.add(entry(CALL_ENTRY, pred, mLetters.name(t.getLetter()), succ));
			}
			for (final OutgoingReturnTransition<L, IPredicate> t : sortedReturn(nwa, state, stateNames)) {
				final String hier = stateNames.get(t.getHierPred());
				final String succ = stateNames.get(t.getSucc());
				printable.addReturnTransition(escape(pred), escape(hier), escapedName(t.getLetter()), escape(succ));
				signature.add(entry(RETURN_ENTRY, pred, hier, mLetters.name(t.getLetter()), succ));
			}
		}
		final String result = AutomatonDefinitionPrinter.toString(services, name, printable);
		assert sameSignature(signature, parseRaw(result)) : "ATS round trip changed the automaton " + name;
		return result;
	}

	private static final String STATE_ENTRY = "S";
	private static final String INTERNAL_ENTRY = "I";
	private static final String CALL_ENTRY = "C";
	private static final String RETURN_ENTRY = "R";

	private static String entry(final String... parts) {
		return String.join("\u0000", parts);
	}

	/**
	 * Checks that a parsed automaton has exactly the states, flags and transitions of the printed one.
	 */
	private static boolean sameSignature(final List<String> expected, final INestedWordAutomaton<String, String> raw) {
		final List<String> actual = new ArrayList<>();
		for (final String state : raw.getStates()) {
			actual.add(entry(STATE_ENTRY, state, String.valueOf(raw.isInitial(state)), String.valueOf(raw.isFinal(state))));
			raw.internalSuccessors(state)
					.forEach(t -> actual.add(entry(INTERNAL_ENTRY, state, t.getLetter(), t.getSucc())));
			raw.callSuccessors(state).forEach(t -> actual.add(entry(CALL_ENTRY, state, t.getLetter(), t.getSucc())));
			raw.returnSuccessors(state).forEach(
					t -> actual.add(entry(RETURN_ENTRY, state, t.getHierPred(), t.getLetter(), t.getSucc())));
		}
		final List<String> sortedExpected = new ArrayList<>(expected);
		sortedExpected.sort(null);
		actual.sort(null);
		return sortedExpected.equals(actual);
	}

	/**
	 * Numbers the states by a breadth-first search from the initial states, visiting the outgoing transitions of a
	 * state ordered by letter name. States the search does not reach come last, ordered by their suffix.
	 */
	private LinkedHashMap<IPredicate, String> numberStates(final INestedWordAutomaton<L, IPredicate> nwa,
			final Function<IPredicate, String> stateSuffix) {
		final LinkedHashMap<IPredicate, String> names = new LinkedHashMap<>();
		final Map<IPredicate, String> suffixes = new HashMap<>();
		final Function<IPredicate, String> suffix = s -> suffixes.computeIfAbsent(s, stateSuffix);
		final Deque<IPredicate> queue = new ArrayDeque<>();
		final List<IPredicate> initial = new ArrayList<>(nwa.getInitialStates());
		initial.sort(Comparator.comparing(suffix));
		for (final IPredicate state : initial) {
			visit(state, names, queue, suffix);
		}
		while (!queue.isEmpty()) {
			final IPredicate state = queue.poll();
			for (final OutgoingInternalTransition<L, IPredicate> t : sortedInternal(nwa, state)) {
				visit(t.getSucc(), names, queue, suffix);
			}
			for (final OutgoingCallTransition<L, IPredicate> t : sortedCall(nwa, state)) {
				visit(t.getSucc(), names, queue, suffix);
			}
			for (final OutgoingReturnTransition<L, IPredicate> t : sortedReturn(nwa, state, names)) {
				visit(t.getHierPred(), names, queue, suffix);
				visit(t.getSucc(), names, queue, suffix);
			}
		}
		final List<IPredicate> unreached = new ArrayList<>();
		for (final IPredicate state : nwa.getStates()) {
			if (!names.containsKey(state)) {
				unreached.add(state);
			}
		}
		unreached.sort(Comparator.comparing(suffix));
		for (final IPredicate state : unreached) {
			visit(state, names, queue, suffix);
		}
		return names;
	}

	private static void visit(final IPredicate state, final Map<IPredicate, String> names,
			final Deque<IPredicate> queue, final Function<IPredicate, String> suffix) {
		if (!names.containsKey(state)) {
			names.put(state, "q" + names.size() + suffix.apply(state));
			queue.add(state);
		}
	}

	private List<OutgoingInternalTransition<L, IPredicate>>
			sortedInternal(final INestedWordAutomaton<L, IPredicate> nwa, final IPredicate state) {
		final List<OutgoingInternalTransition<L, IPredicate>> result = new ArrayList<>();
		nwa.internalSuccessors(state).forEach(result::add);
		result.sort(Comparator.comparing(t -> mLetters.name(t.getLetter())));
		return result;
	}

	private List<OutgoingCallTransition<L, IPredicate>> sortedCall(final INestedWordAutomaton<L, IPredicate> nwa,
			final IPredicate state) {
		final List<OutgoingCallTransition<L, IPredicate>> result = new ArrayList<>();
		nwa.callSuccessors(state).forEach(result::add);
		result.sort(Comparator.comparing(t -> mLetters.name(t.getLetter())));
		return result;
	}

	private List<OutgoingReturnTransition<L, IPredicate>> sortedReturn(
			final INestedWordAutomaton<L, IPredicate> nwa, final IPredicate state,
			final Map<IPredicate, String> names) {
		final List<OutgoingReturnTransition<L, IPredicate>> result = new ArrayList<>();
		nwa.returnSuccessors(state).forEach(result::add);
		// hierarchical predecessors that are not numbered yet sort last
		final Comparator<OutgoingReturnTransition<L, IPredicate>> byLetter =
				Comparator.comparing(t -> mLetters.name(t.getLetter()));
		result.sort(byLetter.thenComparing(t -> number(names.get(t.getHierPred()))));
		return result;
	}

	private static int number(final String name) {
		if (name == null) {
			return Integer.MAX_VALUE;
		}
		int end = 1;
		while (end < name.length() && Character.isDigit(name.charAt(end))) {
			end++;
		}
		return Integer.parseInt(name.substring(1, end));
	}

	private Set<String> escapedNames(final Set<L> letters) {
		final Set<String> result = new HashSet<>();
		for (final L letter : letters) {
			result.add(escapedName(letter));
		}
		return result;
	}

	private String escapedName(final L letter) {
		return escape(mLetters.name(letter));
	}

	/**
	 * Escapes a name for a string literal of the automata script. The printer quotes names but does not escape them;
	 * the lexer turns {@code \\} and {@code \"} back.
	 */
	static String escape(final String name) {
		return name.replace("\\", "\\\\").replace("\"", "\\\"");
	}

	private INestedWordAutomaton<String, String> parseRaw(final String ats) {
		final AutomataTestFileAST ast =
				new AutomataScriptParserRun(mServices, mLogger, new StringReader(ats), SOURCE_NAME, SOURCE_NAME)
						.getResult();
		if (ast == null || ast.getAutomataDefinitions() == null) {
			throw new IllegalArgumentException("Cannot parse the automaton:\n" + ats);
		}
		final List<AutomatonAST> definitions = ast.getAutomataDefinitions().getListOfAutomataDefinitions();
		if (definitions.size() != 1 || !(definitions.get(0) instanceof NestedwordAutomatonAST)) {
			throw new IllegalArgumentException("Expected exactly one nested word automaton, got " + definitions.size()
					+ " definitions");
		}
		return AutomataDefinitionInterpreter.constructNestedWordAutomaton((NestedwordAutomatonAST) definitions.get(0),
				mServices);
	}

	/**
	 * Builds an automaton over the local letters from a parsed one and the predicates of its states.
	 */
	private NestedWordAutomaton<L, IPredicate> translate(final INestedWordAutomaton<String, String> raw,
			final Map<String, IPredicate> states, final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		final VpAlphabet<String> rawAlphabet = raw.getVpAlphabet();
		final VpAlphabet<L> alphabet = mLetters.getAlphabet();
		checkAlphabet("internal", rawAlphabet.getInternalAlphabet(), alphabet.getInternalAlphabet());
		checkAlphabet("call", rawAlphabet.getCallAlphabet(), alphabet.getCallAlphabet());
		checkAlphabet("return", rawAlphabet.getReturnAlphabet(), alphabet.getReturnAlphabet());
		final NestedWordAutomaton<L, IPredicate> result =
				new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), alphabet, emptyStackFactory);
		final Map<IPredicate, Boolean> initial = new LinkedHashMap<>();
		final Map<IPredicate, Boolean> accepting = new HashMap<>();
		for (final String state : raw.getStates()) {
			final IPredicate pred = states.get(state);
			initial.merge(pred, raw.isInitial(state), Boolean::logicalOr);
			accepting.merge(pred, raw.isFinal(state), Boolean::logicalOr);
		}
		for (final Map.Entry<IPredicate, Boolean> entry : initial.entrySet()) {
			result.addState(entry.getValue(), accepting.get(entry.getKey()), entry.getKey());
		}
		final Map<String, L> letters = new HashMap<>();
		final Function<String, L> letter = n -> letters.computeIfAbsent(n, mLetters::resolve);
		for (final String state : raw.getStates()) {
			final IPredicate pred = states.get(state);
			for (final OutgoingInternalTransition<String, String> t : raw.internalSuccessors(state)) {
				result.addInternalTransition(pred, letter.apply(t.getLetter()), states.get(t.getSucc()));
			}
			for (final OutgoingCallTransition<String, String> t : raw.callSuccessors(state)) {
				result.addCallTransition(pred, letter.apply(t.getLetter()), states.get(t.getSucc()));
			}
			for (final OutgoingReturnTransition<String, String> t : raw.returnSuccessors(state)) {
				result.addReturnTransition(pred, states.get(t.getHierPred()), letter.apply(t.getLetter()),
						states.get(t.getSucc()));
			}
		}
		return result;
	}

	private void checkAlphabet(final String kind, final Set<String> rawNames, final Set<L> local) {
		final Set<L> resolved = new HashSet<>();
		for (final String name : rawNames) {
			resolved.add(mLetters.resolve(name));
		}
		if (!resolved.equals(local)) {
			throw new IllegalArgumentException("The " + kind + " alphabet of the automaton (" + resolved.size()
					+ " letters) differs from the local one (" + local.size() + " letters)");
		}
	}
}
