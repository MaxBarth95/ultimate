/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by the Free Software Foundation,
 * either version 3 of the License, or (at your option) any later version.
 */
package multiprocessed;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.nio.file.StandardWatchEventKinds;
import java.nio.file.WatchEvent;
import java.nio.file.WatchKey;
import java.nio.file.WatchService;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * Persistent process worker. The Ultimate toolchain and its process-local CFG/SMT context are initialized once. The
 * worker then blocks for requests and handles them sequentially until the toolchain is cancelled.
 */
public final class MultiProcessedCegarWorker<L extends IIcfgTransition<?>>
		extends MultiProcessedCegarCoordinator<L, INestedWordAutomaton<L, IPredicate>> {
	private static final String REQUEST_PREFIX = "request-";
	private static final String JSON_SUFFIX = ".json";
	private static final String ATS_SUFFIX = ".ats";
	private static final String SHUTDOWN_FILE = "shutdown";

	private final Path mInbox;
	private final Set<Path> mConsumedRequests = new HashSet<>();
	private Path mCurrentRequest;
	private boolean mCurrentCounterexampleIsFresh = true;
	private final String mWorkerId;
	private int mInstalledAbstractionGeneration;
	private String mCurrentPathProgramHash;

	public MultiProcessedCegarWorker(final DebugIdentifier name,
			final INestedWordAutomaton<L, IPredicate> initialAbstraction, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<? extends IcfgLocation> errorLocs, final NwaHoareProofProducer<L> proofProducer,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, proofProducer,
				services, transitionClazz, stateFactoryForRefinement);
		mInbox = Path.of(taPrefs.getMultiProcessExchangeRoot()).toAbsolutePath().normalize();
		mWorkerId = taPrefs.getMultiProcessWorkerId();
		publishWorkerStatus("STARTING", null, null);
	}

	@Override
	protected boolean isAbstractionEmpty() {
		if (!loadNextJob()) {
			throw new IllegalStateException("Worker was shut down before receiving its first job");
		}
		return false;
	}

	@Override
	protected void iterate() throws AutomataLibraryException {
		while (getServices().getProgressMonitorService().continueProcessing()) {
			mIteration++;
			processCurrentJob();
			if (!loadNextJob()) {
				mLogger.info("Worker received the coordinator shutdown marker");
				return;
			}
		}
	}

	/**
	 * Replaces the worker-local abstraction with the automaton stored in {@code atsFile}. The ATS automaton is rebuilt
	 * against this worker's live alphabet and SMT context; no raw String automaton is cast to the live generic types.
	 * The old abstraction remains installed if parsing or validation fails.
	 *
	 * @param atsFile
	 *            ATS file containing exactly one nested-word automaton
	 * @throws IOException
	 *             if the file cannot be read
	 */
	public synchronized void updateAbstractionFromAts(final Path atsFile) throws IOException {
		updateAbstractionFromAts(atsFile, mInstalledAbstractionGeneration);
	}

	public synchronized void updateAbstractionFromAts(final Path atsFile, final int abstractionGeneration)
			throws IOException {
		final Path normalized = atsFile.toAbsolutePath().normalize();
		if (!Files.isRegularFile(normalized)) {
			throw new IOException("Abstraction ATS file does not exist: " + normalized);
		}
		final INestedWordAutomaton<L, IPredicate> updatedAbstraction;
		try {
			updatedAbstraction = readAutomatonFromAts(normalized);
		} catch (final IOException e) {
			throw e;
		} catch (final Exception e) {
			throw new IOException("Could not reconstruct worker abstraction from " + normalized, e);
		}
		if (updatedAbstraction.getInitialStates().isEmpty() || updatedAbstraction.getFinalStates().isEmpty()) {
			throw new IOException("Reconstructed worker abstraction is unusable: " + normalized);
		}
		final boolean currentCounterexampleIsFresh;
		try {
			currentCounterexampleIsFresh =
					mCounterexample == null || new Accepts<>(new AutomataLibraryServices(getServices()),
							updatedAbstraction, (NestedWord<L>) mCounterexample.getWord()).getResult();
		} catch (final AutomataLibraryException e) {
			throw new IOException("Could not validate the current counterexample against " + normalized, e);
		}
		mAbstraction = updatedAbstraction;
		mInstalledAbstractionGeneration = abstractionGeneration;
		mCurrentCounterexampleIsFresh = currentCounterexampleIsFresh;
		mLogger.info("Updated worker abstraction from %s (%s)", normalized, updatedAbstraction.sizeInformation());
		if (!currentCounterexampleIsFresh) {
			mLogger.info("The current counterexample is no longer accepted by the updated abstraction");
		}
		publishWorkerStatus(mCurrentRequest == null ? "IDLE" : "WORKING",
				mCurrentRequest == null ? null : jobId(mCurrentRequest), mCurrentPathProgramHash);
	}

	private void processCurrentJob() throws AutomataLibraryException {
		final String jobId = jobId(mCurrentRequest);
		try {
			if (publishCancellationIfRequested(jobId)) {
				return;
			}
			final LBool feasibility = isCounterexampleFeasible().getFirst();
			if (publishCancellationIfRequested(jobId)) {
				return;
			}
			if (feasibility == LBool.UNSAT) {
				constructInterpolantAutomaton();
				if (publishCancellationIfRequested(jobId)) {
					return;
				}
				publishAutomaton(jobId);
				if (publishCancellationIfRequested(jobId)) {
					return;
				}
				publishResult(jobId, "UNSAT", "automaton-" + jobId + ATS_SUFFIX, null);
			} else {
				publishResult(jobId, feasibility == LBool.SAT ? "SAT" : "UNKNOWN", null, null);
			}
		} catch (final RuntimeException | AssertionError e) {
			publishResult(jobId, "ERROR", null, e.toString());
			mLogger.error("Worker job " + jobId + " failed", e);
		} catch (final IOException e) {
			publishResult(jobId, "ERROR", null, e.toString());
			mLogger.error("Could not publish refinement automaton for " + jobId, e);
		} finally {
			mCurrentRequest = null;
			mCurrentPathProgramHash = null;
			publishWorkerStatus("IDLE", null, null);
		}
	}

	private boolean publishCancellationIfRequested(final String jobId) {
		final boolean cancelled = Files.isRegularFile(mInbox.resolve("cancel-" + jobId + JSON_SUFFIX));
		if (!cancelled && mCurrentCounterexampleIsFresh) {
			return false;
		}
		publishResult(jobId, "CANCELLED", null, cancelled ? "Coordinator cancelled stale counterexample"
				: "Counterexample is stale after the worker abstraction was updated");
		return true;
	}

	private boolean loadNextJob() {
		try {
			installLatestAbstractionIfNeeded();
			mCurrentRequest = waitForRequest();
			if (mCurrentRequest == null) {
				return false;
			}
			mConsumedRequests.add(mCurrentRequest);
			final String requestJson = Files.readString(mCurrentRequest);
			mCurrentPathProgramHash = jsonString(requestJson, "pathProgramHash");
			if (Files.isRegularFile(cancellationFile(jobId(mCurrentRequest)))) {
				publishResult(jobId(mCurrentRequest), "CANCELLED", null, "Coordinator cancelled stale counterexample");
				mCurrentRequest = null;
				mCurrentPathProgramHash = null;
				return loadNextJob();
			}
			final long parsingStarted = System.nanoTime();
			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.CounterexampleParsingTime);
			try {
				final List<String> symbols = NestedRunParser.readNestedRun(mCurrentRequest);
				final NestedRunParser<L, IPredicate> parser = new NestedRunParser<>();
				mCounterexample = parser.getTraceInAbstractionFromStrings(symbols, mAbstraction);
			} finally {
				mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.CounterexampleParsingTime);
				mLogger.info("Parsed counterexample %s in %.6f s", mCurrentRequest,
						(System.nanoTime() - parsingStarted) / 1_000_000_000.0);
			}
			mCurrentCounterexampleIsFresh = true;
			publishWorkerStatus("WORKING", jobId(mCurrentRequest), mCurrentPathProgramHash);
			return true;
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
			throw new IllegalStateException("Worker could not receive its next job", e);
		} catch (final IOException e) {
			throw new IllegalStateException("Worker could not read its next job", e);
		} catch (final RuntimeException | AssertionError e) {
			if (mCurrentRequest == null) {
				throw e;
			}
			final String failedJobId = jobId(mCurrentRequest);
			mLogger.error("Worker could not reconstruct counterexample for job " + failedJobId, e);
			publishResult(failedJobId, "ERROR", null, e.toString());
			mCurrentRequest = null;
			mCurrentPathProgramHash = null;
			publishWorkerStatus("IDLE", null, null);
			return loadNextJob();
		}
	}

	@Override
	protected void finish() {
		publishWorkerStatus("SHUTDOWN", null, null);
		super.finish();
		final long totalNanos = (long) mCegarLoopBenchmark.getValue(CegarLoopStatisticsDefinitions.OverallTime.name());
		final long atsNanos = (long) mCegarLoopBenchmark.getValue(CegarLoopStatisticsDefinitions.AtsParsingTime.name());
		final long counterexampleNanos =
				(long) mCegarLoopBenchmark.getValue(CegarLoopStatisticsDefinitions.CounterexampleParsingTime.name());
		logParsingTime("ATS automata", atsNanos, totalNanos);
		logParsingTime("counterexamples", counterexampleNanos, totalNanos);
		logParsingTime("all multiprocessing input", atsNanos + counterexampleNanos, totalNanos);
	}

	private void logParsingTime(final String inputKind, final long parsingNanos, final long totalNanos) {
		final double parsingSeconds = parsingNanos / 1_000_000_000.0;
		final double percentage = totalNanos == 0 ? 0 : 100.0 * parsingNanos / totalNanos;
		mLogger.info("Time spent parsing %s: %.6f s (%.2f%% of %.6f s total)", inputKind, parsingSeconds, percentage,
				totalNanos / 1_000_000_000.0);
	}

	private Path waitForRequest() throws IOException, InterruptedException {
		Files.createDirectories(mInbox);
		try (WatchService watcher = FileSystems.getDefault().newWatchService()) {
			mInbox.register(watcher, StandardWatchEventKinds.ENTRY_CREATE);
			while (true) {
				installLatestAbstractionIfNeeded();
				if (Files.isRegularFile(mInbox.resolve(SHUTDOWN_FILE))) {
					return null;
				}
				final Path existing = findUnconsumedRequest();
				if (existing != null && tryClaim(existing)) {
					return existing;
				}
				final WatchKey key = watcher.take();
				for (final WatchEvent<?> event : key.pollEvents()) {
					if (event.kind() == StandardWatchEventKinds.ENTRY_CREATE) {
						final Path candidate = mInbox.resolve((Path) event.context()).toAbsolutePath().normalize();
						if (candidate.getFileName().toString().equals(SHUTDOWN_FILE)) {
							return null;
						}
						if (isRequest(candidate) && Files.isRegularFile(candidate)
								&& !Files.exists(cancellationFile(jobId(candidate)))) {
							installLatestAbstractionIfNeeded();
							if (tryClaim(candidate)) {
								return candidate;
							}
						}
					}
				}
				if (!key.reset()) {
					throw new IOException("Worker inbox is no longer watchable: " + mInbox);
				}
			}
		}
	}

	private void installLatestAbstractionIfNeeded() {
		final Path directory = mInbox.resolve("abstractions");
		final Path manifest = directory.resolve("latest.json");
		if (!Files.isRegularFile(manifest)) {
			return;
		}
		try {
			final String json = Files.readString(manifest, StandardCharsets.UTF_8);
			final int generation = jsonInt(json, "abstractionGeneration");
			if (generation <= mInstalledAbstractionGeneration) {
				return;
			}
			final Path ats = directory.resolve(jsonString(json, "atsFile")).normalize();
			if (!ats.startsWith(directory.normalize())) {
				throw new IOException("Abstraction update escapes its exchange directory: " + ats);
			}
			updateAbstractionFromAts(ats, generation);
		} catch (final IOException e) {
			mLogger.error("Could not install the latest coordinator abstraction; keeping generation "
					+ mInstalledAbstractionGeneration, e);
		}
	}

	private Path findUnconsumedRequest() throws IOException {
		try (var files = Files.list(mInbox)) {
			return files.filter(this::isRequest).filter(Files::isRegularFile)
					.filter(x -> !mConsumedRequests.contains(x)).filter(x -> !Files.exists(cancellationFile(jobId(x))))
					.filter(x -> !Files.exists(claimFile(x))).sorted(Comparator.comparing(Path::getFileName))
					.findFirst().orElse(null);
		}
	}

	private boolean tryClaim(final Path request) throws IOException {
		try {
			Files.writeString(claimFile(request), Long.toString(ProcessHandle.current().pid()) + "\n",
					StandardCharsets.UTF_8, StandardOpenOption.CREATE_NEW, StandardOpenOption.WRITE);
			return true;
		} catch (final java.nio.file.FileAlreadyExistsException e) {
			return false;
		}
	}

	private Path claimFile(final Path request) {
		return request.resolveSibling(request.getFileName() + ".claim");
	}

	private Path cancellationFile(final String jobId) {
		return mInbox.resolve("cancel-" + jobId + JSON_SUFFIX);
	}

	private boolean isRequest(final Path path) {
		final String name = path.getFileName().toString();
		return name.startsWith(REQUEST_PREFIX) && name.endsWith(JSON_SUFFIX) && !name.endsWith(".tmp");
	}

	private void publishAutomaton(final String jobId) throws IOException {
		final String temporaryName = "automaton-" + jobId + ".tmp";
		new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(getServices()), "nwa",
				mInbox.resolve(temporaryName).toString(), Format.ATS, "", mInterpolAutomaton);
		atomicMove(mInbox.resolve(temporaryName + ATS_SUFFIX), mInbox.resolve("automaton-" + jobId + ATS_SUFFIX));
	}

	private void publishResult(final String jobId, final String outcome, final String atsFile,
			final String diagnostic) {
		final String json = "{\n" + "  \"schemaVersion\": 1,\n" + "  \"jobId\": \"" + escape(jobId) + "\",\n"
				+ "  \"outcome\": \"" + outcome + "\",\n" + "  \"atsFile\": "
				+ (atsFile == null ? "null" : "\"" + escape(atsFile) + "\"") + ",\n" + "  \"diagnostic\": "
				+ (diagnostic == null ? "null" : "\"" + escape(diagnostic) + "\"") + "\n}\n";
		final Path temporary = mInbox.resolve("result-" + jobId + ".json.tmp");
		final Path result = mInbox.resolve("result-" + jobId + JSON_SUFFIX);
		try {
			Files.writeString(temporary, json, StandardCharsets.UTF_8);
			atomicMove(temporary, result);
		} catch (final IOException e) {
			throw new IllegalStateException("Could not publish worker result for " + jobId, e);
		}
	}

	private static void atomicMove(final Path source, final Path target) throws IOException {
		try {
			Files.move(source, target, StandardCopyOption.ATOMIC_MOVE);
		} catch (final IOException e) {
			Files.move(source, target);
		}
	}

	private static String jobId(final Path request) {
		final String filename = request.getFileName().toString();
		return filename.substring(REQUEST_PREFIX.length(), filename.length() - JSON_SUFFIX.length());
	}

	private static String escape(final String input) {
		return input.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n").replace("\r", "\\r");
	}

	private void publishWorkerStatus(final String state, final String jobId, final String pathProgramHash) {
		final String json = "{\n" + "  \"schemaVersion\": 1,\n" + "  \"workerId\": \"" + escape(mWorkerId) + "\",\n"
				+ "  \"pid\": " + ProcessHandle.current().pid() + ",\n" + "  \"installedAbstractionGeneration\": "
				+ mInstalledAbstractionGeneration + ",\n" + "  \"state\": \"" + state + "\",\n" + "  \"jobId\": "
				+ (jobId == null ? "null" : "\"" + escape(jobId) + "\"") + ",\n" + "  \"pathProgramHash\": "
				+ (pathProgramHash == null ? "null" : "\"" + escape(pathProgramHash) + "\"") + "\n}\n";
		final String safeWorkerId = mWorkerId.replaceAll("[^A-Za-z0-9_.-]", "_");
		try {
			Files.createDirectories(mInbox);
			atomicWrite(mInbox.resolve("worker-status-" + safeWorkerId + ".json"), json);
		} catch (final IOException e) {
			throw new IllegalStateException("Could not publish status for worker " + mWorkerId, e);
		}
	}

	private static String jsonString(final String json, final String field) throws IOException {
		final String key = "\"" + field + "\"";
		final int keyPosition = json.indexOf(key);
		final int colon = keyPosition < 0 ? -1 : json.indexOf(':', keyPosition + key.length());
		final int start = colon < 0 ? -1 : json.indexOf('"', colon + 1);
		final int end = start < 0 ? -1 : json.indexOf('"', start + 1);
		if (start < 0 || end < 0) {
			throw new IOException("Missing JSON string field " + field);
		}
		return json.substring(start + 1, end);
	}

	private static int jsonInt(final String json, final String field) throws IOException {
		final String key = "\"" + field + "\"";
		final int keyPosition = json.indexOf(key);
		final int colon = keyPosition < 0 ? -1 : json.indexOf(':', keyPosition + key.length());
		int start = colon + 1;
		while (start > 0 && start < json.length() && Character.isWhitespace(json.charAt(start))) {
			start++;
		}
		int end = start;
		while (end < json.length() && Character.isDigit(json.charAt(end))) {
			end++;
		}
		if (colon < 0 || start == end) {
			throw new IOException("Missing JSON integer field " + field);
		}
		try {
			return Integer.parseInt(json.substring(start, end));
		} catch (final NumberFormatException e) {
			throw new IOException("Invalid JSON integer field " + field, e);
		}
	}
}
