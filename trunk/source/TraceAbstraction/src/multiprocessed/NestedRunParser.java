package multiprocessed;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardWatchEventKinds;
import java.nio.file.WatchEvent;
import java.nio.file.WatchKey;
import java.nio.file.WatchService;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.icfg.Call;
import de.uni_freiburg.informatik.ultimate.lib.icfg.Return;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;

public class NestedRunParser<LETTER, STATE> {

	public NestedRunParser() {

	}

	/*
	 * Thread Blocking!!! Checks the given path, looks for a json if none exists sleeps.
	 *
	 */
	// "./input/counterexamples" // TODO as setting i guess
	// reads the latest added json in the given path
	// then deletes it
	public static List<String> readNestedRunFromFile(final String pathToRun) throws Exception {
		final Path folder = Path.of(pathToRun);

		final Path jsonFile = waitForFile(folder);
		final List<String> symbols = readNestedRun(jsonFile);
		// Files.delete(jsonFile);
		return symbols;

	}

	public static List<String> readNestedRun(final Path jsonFile) throws IOException {
		return parseSymbols(Files.readString(jsonFile));
	}

	private static List<String> parseSymbols(final String json) {
		final List<String> result = new ArrayList<>();

		final String key = "\"symbols\"";
		final int keyPos = json.indexOf(key);
		if (keyPos < 0) {
			return result;
		}

		final int colon = json.indexOf(':', keyPos + key.length());
		if (colon < 0) {
			return result;
		}

		final int arrayStart = json.indexOf('[', colon + 1);
		if (arrayStart < 0) {
			return result;
		}

		int i = arrayStart + 1;

		while (i < json.length()) {
			// skip whitespace and commas
			while (i < json.length() && (Character.isWhitespace(json.charAt(i)) || json.charAt(i) == ',')) {
				i++;
			}

			if (i >= json.length() || json.charAt(i) == ']') {
				break;
			}

			if (json.charAt(i) != '"') {
				throw new IllegalArgumentException("Expected string in symbols array at index " + i);
			}

			i++; // skip opening quote
			final StringBuilder sb = new StringBuilder();

			while (i < json.length()) {
				final char c = json.charAt(i);
				i++;

				if (c == '\\') {
					if (i >= json.length()) {
						throw new IllegalArgumentException("Invalid escape sequence");
					}

					final char escaped = json.charAt(i);
					i++;
					switch (escaped) {
					case '"':
						sb.append('"');
						break;
					case '\\':
						sb.append('\\');
						break;
					case '/':
						sb.append('/');
						break;
					case 'b':
						sb.append('\b');
						break;
					case 'f':
						sb.append('\f');
						break;
					case 'n':
						sb.append('\n');
						break;
					case 'r':
						sb.append('\r');
						break;
					case 't':
						sb.append('\t');
						break;
					case 'u':
						if (i + 4 > json.length()) {
							throw new IllegalArgumentException("Invalid unicode escape");
						}
						final String hex = json.substring(i, i + 4);
						sb.append((char) Integer.parseInt(hex, 16));
						i += 4;
						break;
					default:
						throw new IllegalArgumentException("Unknown escape: \\" + escaped);
					}
				} else if (c == '"') {
					result.add(sb.toString());
					break;
				} else {
					sb.append(c);
				}
			}
		}

		return result;
	}

	private static Path waitForFile(final Path folder) throws IOException, InterruptedException {
		Files.createDirectories(folder);
		try (WatchService watchService = FileSystems.getDefault().newWatchService()) {
			folder.register(watchService, StandardWatchEventKinds.ENTRY_CREATE);

			// Register before scanning. Otherwise a file created between the initial scan and registration is missed.
			try (var stream = Files.list(folder)) {
				final Path existing = stream.filter(Files::isRegularFile).findFirst().orElse(null);
				if (existing != null) {
					return existing;
				}
			}

			while (true) {
				final WatchKey key = watchService.take();

				for (final WatchEvent<?> event : key.pollEvents()) {
					if (event.kind() == StandardWatchEventKinds.ENTRY_CREATE) {
						final Path createdFile = folder.resolve((Path) event.context());

						if (Files.isRegularFile(createdFile)) {
							return createdFile;
						}
					}
				}

				if (!key.reset()) {
					throw new IOException("Watch key is no longer valid");
				}
			}
		}
	}

	/*
	 * Check if the current trace is in the given abstraction, if not we backtrack to the point where it still was. This
	 * means we remove all branchings from the queue when backtracking.
	 *
	 * Updates mCurrentRun to be of the new Abstraction
	 *
	 */
	public NestedRun<LETTER, STATE> getTraceInAbstractionFromStrings(final List<String> runAsStrings,
			final INestedWordAutomaton<LETTER, STATE> iNestedWordAutomaton) {
		assert iNestedWordAutomaton.getInitialStates().size() == 1;

		final long time = System.nanoTime() / 1000000000;
		STATE initial = null;
		for (final STATE start : iNestedWordAutomaton.getInitialStates()) {
			initial = start;
		}
		assert iNestedWordAutomaton.getInitialStates().size() == 1 : "Only Supporting 1 inital state atm";
		NestedRun<LETTER, STATE> newRun = new NestedRun<>(initial);
		STATE stateK = iNestedWordAutomaton.getEmptyStackState();

		if (runAsStrings.isEmpty()) {
			return newRun;
		}
		for (int i = 0; i < runAsStrings.size(); i++) {

			final NestedRun<LETTER, STATE> subrun =
					getNewSubRun(newRun.getStateAtPosition(i), stateK, runAsStrings.get(i), iNestedWordAutomaton);

			// until state i, the trace is still in the abstraction, letter i no more
			if (subrun == null) {
				throw new AssertionError("cannot find run in abstraction");
			}
			if (subrun.getSymbol(0) instanceof Call) {
				stateK = newRun.getStateAtPosition(i);
			}
			if (subrun.getSymbol(0) instanceof Return) {
				stateK = getCallerOfStateK(newRun, stateK, iNestedWordAutomaton.getEmptyStackState());
			}
			newRun = newRun.concatenate(subrun);

		}
		return newRun;

	}

	private NestedRun<LETTER, STATE> getNewSubRun(final STATE newState, final STATE newStateK, final String oldLetter,
			final INestedWordAutomaton<LETTER, STATE> iNestedWordAutomaton) {
		NestedRun<LETTER, STATE> run = null;
		int countOutgoing = 0;

		for (final SummaryReturnTransition<LETTER, STATE> transition : iNestedWordAutomaton
				.summarySuccessors(newState)) {
			final STATE succ = transition.getSucc();
			final LETTER letter = transition.getLetter();
			if (oldLetter.equals(letter.toString())) {
				countOutgoing += 1;
				run = new NestedRun<>(newState, letter, NestedWord.MINUS_INFINITY, succ);
				return run;
			}
		}

		for (final OutgoingInternalTransition<LETTER, STATE> transition : iNestedWordAutomaton
				.internalSuccessors(newState)) {
			final STATE succ = transition.getSucc();
			final LETTER letter = transition.getLetter();
			if (oldLetter.equals(letter.toString())) {

				countOutgoing += 1;
				run = new NestedRun<>(newState, letter, NestedWord.INTERNAL_POSITION, succ);
			}
		}

		for (final OutgoingCallTransition<LETTER, STATE> transition : iNestedWordAutomaton.callSuccessors(newState)) {
			final STATE succ = transition.getSucc();
			final LETTER letter = transition.getLetter();
			if (oldLetter.equals(letter.toString())) {

				countOutgoing += 1;
				run = new NestedRun<>(newState, letter, NestedWord.PLUS_INFINITY, succ);
			}

		}

		for (final OutgoingReturnTransition<LETTER, STATE> transition : iNestedWordAutomaton
				.returnSuccessorsGivenHier(newState, newStateK)) {
			final STATE succ = transition.getSucc();
			final LETTER letter = transition.getLetter();
			if (oldLetter.equals(letter.toString())) {
				countOutgoing += 1;
				run = new NestedRun<>(newState, letter, NestedWord.MINUS_INFINITY, succ);
			}
		}
		assert countOutgoing <= 1;
		return run;
	}

	private boolean twoStateHaveSameProgramPoint(final STATE a, final STATE b) {
		IcfgLocation programPoint = null;
		if (a instanceof ISLPredicate && b instanceof ISLPredicate) {
			programPoint = ((ISLPredicate) a).getProgramPoint();
			if (programPoint.equals(((ISLPredicate) b).getProgramPoint())) {
				return true;
			}
		} else {
			throw new AssertionError("Unexpected Predicate");
		}

		return false;
	}

	private STATE getCallerOfStateK(final NestedRun<LETTER, STATE> trace, final STATE stateK, final STATE dummyState) {
		STATE stateKk = null;
		boolean foundStateK = false;

		int sawReturn = 0; // ensures there is a call not yet covered by a return
		int sawCalls = 0; // ensures there is a call in the trace
		for (int i = trace.getWord().length() - 1; i > 0; i--) {
			if (trace.isCallPosition(i)) {
				sawCalls += 1;
				final STATE stateOfthisCall = trace.getStateSequence().get(i);
				if (foundStateK && sawReturn == 0) {
					stateKk = stateOfthisCall;
					break;
				}
				if (sawReturn > 0) {
					sawReturn -= 1;
				} else if (stateK.equals(stateOfthisCall) && sawReturn == 0) {
					foundStateK = true;
				}
			} else if (trace.isReturnPosition(i)) {
				sawReturn += 1;
				sawCalls -= 1;
			}

		}
		if (sawCalls < 1) {
			return null;
		}
		if (stateKk == null) {
			return dummyState;
		}
		assert foundStateK;
		return stateKk;
	}
}
