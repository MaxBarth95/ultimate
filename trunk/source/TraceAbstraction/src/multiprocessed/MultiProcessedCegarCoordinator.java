package multiprocessed;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardWatchEventKinds;
import java.nio.file.WatchKey;
import java.nio.file.WatchService;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IEpsilonNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty.SearchStrategy;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyParallel;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.CachingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.ChainingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateParsingWrapperScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ReuseCegarLoop.ReuseStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionObserver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.MultiProcessComponent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuseEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AutomataScriptParserRun;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import multiprocessed.IActiveJobRegistry.InMemory;
import multiprocessed.IActiveJobRegistry.Job;

public class MultiProcessedCegarCoordinator<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		extends NwaCegarLoop<L> {
	private static final String EXISTING_STATE_MARKER = "@EXISTING_STATE@";
	TraceAbstractionObserver mObserver;
	private final List<Pair<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>, IPredicateUnifier>> mReuseAutomata =
			new ArrayList<>();
	public static boolean USE_AUTOMATA_WITH_UNMATCHED_PREDICATES = false;
	protected List<MultiProcessedCegarCoordinator<L, A>.ReuseAutomaton> mFloydHoareAutomataFromFile;
	protected final ReuseStatisticsGenerator mReuseStats;
	private final boolean mStatsAlreadyAggregated = false;
	private final Path mExchangeRoot;
	private final Set<String> mOutstandingJobs = new HashSet<>();
	private final IActiveJobRegistry<L> mActiveJobs = new InMemory();
	private final Map<String, Integer> mPublishedPathProgramCounts = new HashMap<>();
	private int mNextJobId;

	public MultiProcessedCegarCoordinator(final DebugIdentifier var1, final INestedWordAutomaton<L, IPredicate> var2, final IIcfg<?> var3,
			final CfgSmtToolkit var4, final PredicateFactory var5, final TAPreferences var6, final Set<? extends IcfgLocation> var7,
			final NwaHoareProofProducer<L> var8, final IUltimateServiceProvider var9, final Class<L> var10,
			final PredicateFactoryRefinement var11) {
		super(var1, var2, var3, var4, var5, var6, var7, var8, var9, var10, var11);
		mFloydHoareAutomataFromFile = new ArrayList<>();
		mReuseStats = new ReuseStatisticsGenerator();
		mObserver = new TraceAbstractionObserver(mServices);
		mExchangeRoot = Path.of(var6.getMultiProcessExchangeRoot()).toAbsolutePath().normalize();
		if (var6.getMultiProcessingComponent() == MultiProcessComponent.COORDINATOR) {
			this.publishCoordinatorStatus(0);
		}
	}

	private void todo() {
		if (mPref.dumpOnlyReuseAutomata()) {
			mLogger.info("Dumping reuse automata for " + mTaskIdentifier.toString());
			final String var1 = mTaskIdentifier + "-reuse";
			final String var2 =
					mPref.dumpPath() + File.separator + var1 + "." + mPrintAutomataLabeling.getFormat().getFileEnding();
			final File var3 = new File(var2);

			try {
				final FileWriter var4 = new FileWriter(var3, false);
				var4.close();
			} catch (final IOException var5) {
				if (mLogger.isErrorEnabled()) {
					mLogger.error("Creating FileWriter did not work.", var5);
				}
			}
		}
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		try {
			this.awaitOutstandingWorkerResults();
		} catch (InterruptedException | IOException var8) {
			if (var8 instanceof InterruptedException) {
				Thread.currentThread().interrupt();
			}

			throw new AssertionError("Failed while waiting for the current worker batch", var8);
		}

		final INwaOutgoingLetterAndTransitionProvider var1 = mAbstraction;
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.EmptinessCheckTime);

		try {
			mCounterexample =
					new IsEmpty(new AutomataLibraryServices(getServices()), var1, mSearchStrategy).getNestedRun();
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.EmptinessCheckTime);
		}

		if (mCounterexample == null) {
			return true;
		} else {
			try {
				this.publishCounterexampleBatch();
				return false;
			} catch (final IOException var6) {
				throw new AssertionError("Failed to publish counterexample request", var6);
			}
		}
	}

	private void publishCounterexampleBatch() throws IOException, AutomataOperationCanceledException {
		final NestedRun var1 = (NestedRun) mCounterexample;
		final HashMap var2 = new HashMap();
		var2.put(var1.getWord().asList().hashCode(), var1);
		this.publishCounterexampleRequest(var1);

		int var3;
		for (var3 = 1; var3 < mPref.getMultiProcessWorkerCount(); var3++) {
			final IsEmptyParallel var4 = new IsEmptyParallel(new AutomataLibraryServices(getServices()), mAbstraction,
					mAbstraction.getInitialStates(), Collections.emptySet(), null, true, SearchStrategy.BFS, var2,
					mPref.getSearchLoopBound());
			final NestedRun var5 = var4.getNestedRun();
			if (var5 == null) {
				break;
			}

			final int var6 = var5.getWord().asList().hashCode();
			if (var2.putIfAbsent(var6, var5) != null) {
				throw new AssertionError("Parallel counterexample search returned a duplicate trace");
			}

			this.publishCounterexampleRequest(var5);
		}

		mLogger.info("Dispatched %s distinct counterexamples for abstraction generation %s", var3, getIteration());
	}

	private void publishCounterexampleRequest(final NestedRun<L, IPredicate> var1) throws IOException {
		Files.createDirectories(mExchangeRoot);
		final String var2 = String.format("%08d", mNextJobId++);
		final String var3 = PathProgramCache.getPathProgramHash(var1.getWord());
		final int var4 = getPathProgramCache().getPathProgramCountOrZero(var1.getWord());
		final int var5 = mPublishedPathProgramCounts.merge(var3, var4 + 1, (var0, var1x) -> Math.max(var0 + 1, var1x));
		final StringBuilder var6 = new StringBuilder();
		var6.append("{\n");
		var6.append("  \"schemaVersion\": 1,\n");
		var6.append("  \"jobId\": \"").append(var2).append("\",\n");
		var6.append("  \"abstractionGeneration\": ").append(getIteration()).append(",\n");
		var6.append("  \"pathProgramHash\": \"").append(var3).append("\",\n");
		var6.append("  \"pathProgramCount\": ").append(var5).append(",\n");
		var6.append("  \"symbols\": [\n");

		for (int var7 = 0; var7 < var1.getWord().length(); var7++) {
			var6.append("    \"").append(escapeJson(String.valueOf(var1.getSymbol(var7)))).append("\"");
			if (var7 + 1 < var1.getWord().length()) {
				var6.append(',');
			}

			var6.append('\n');
		}

		var6.append("  ]\n}\n");
		final Path var10 = mExchangeRoot.resolve("request-" + var2 + ".json.tmp");
		final Path var8 = mExchangeRoot.resolve("request-" + var2 + ".json");
		Files.writeString(var10, var6, StandardCharsets.UTF_8);

		try {
			Files.move(var10, var8, StandardCopyOption.ATOMIC_MOVE);
		} catch (final IOException var9) {
			Files.move(var10, var8);
		}

		mOutstandingJobs.add(var2);
		mActiveJobs.register(var2, var1, getIteration(), var3);
		mLogger.info("Published worker request %s", var8);
	}

	// $VF: Could not inline inconsistent finally blocks
	// Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a
	// copy of the class file (if you have the rights to distribute it!)
	private void awaitOutstandingWorkerResults() throws IOException, InterruptedException {
		if (!mOutstandingJobs.isEmpty()) {
			Files.createDirectories(mExchangeRoot);
			Throwable var1 = null;
			final Object var2 = null;

			try {
				final WatchService var3 = FileSystems.getDefault().newWatchService();

				try {
					mExchangeRoot.register(var3, StandardWatchEventKinds.ENTRY_CREATE);

					while (!mOutstandingJobs.isEmpty()) {
						this.removePublishedResults();
						if (mOutstandingJobs.isEmpty()) {
							break;
						}

						final WatchKey var4 = var3.take();
						var4.pollEvents();
						if (!var4.reset()) {
							throw new IOException("Worker exchange directory is no longer watchable: " + mExchangeRoot);
						}
					}
				} finally {
					if (var3 != null) {
						var3.close();
					}
				}
			} catch (final Throwable var10) {
				if (var1 == null) {
					var1 = var10;
				} else if (var1 != var10) {
					var1.addSuppressed(var10);
				}

				if (var1 instanceof final IOException var11) {
					throw var11;
				}
				if (var1 instanceof final InterruptedException var12) {
					throw var12;
				}
				throw new IllegalStateException(var1);
			}

			mLogger.info("All worker results for the previous abstraction generation are ready");
		}
	}

	private void removePublishedResults() {
		mOutstandingJobs.removeIf(var1 -> {
			this.refreshWorkerAssignment(var1);
			if (!Files.isRegularFile(mExchangeRoot.resolve("result-" + var1 + ".json"))) {
				return false;
			} else {
				mActiveJobs.complete(var1);
				return true;
			}
		});
	}

	private void refreshWorkerAssignment(final String var1) {
		final Path var2 = mExchangeRoot.resolve("request-" + var1 + ".json.claim");
		if (Files.isRegularFile(var2)) {
			try {
				final long var3 = Long.parseLong(Files.readString(var2, StandardCharsets.UTF_8).trim());
				mActiveJobs.assign(var1, this.findWorkerId(var3), var3);
			} catch (NumberFormatException | IOException var5) {
				mLogger.warn("Could not read worker claim for job %s: %s", var1, var5.getMessage());
			}
		}
	}

	private void updateWorkersAfterAbstractionUpdate(final int var1, final int var2) throws AutomataLibraryException {
		this.removePublishedResults();

		for (final Job var3 : mActiveJobs.activeJobs()) {
			this.refreshWorkerAssignment(var3.jobId());
			final boolean var5 = new Accepts(new AutomataLibraryServices(getServices()), mAbstraction,
					var3.counterexample().getWord()).getResult();
			if (!var5) {
				this.publishCancellation(var3, var2);
			}
		}

		final int var6 = mAbstraction.size();
		if (var6 < var1) {
			this.publishAbstractionUpdate(var2, var6);
		}
	}

	private void publishCancellation(final Job<L> var1, final int var2) {
		final String var3 = "{\n  \"schemaVersion\": 1,\n  \"jobId\": \"" + escapeJson(var1.jobId())
				+ "\",\n  \"abstractionGeneration\": " + var1.abstractionGeneration()
				+ ",\n  \"cancellationGeneration\": " + var2
				+ ",\n  \"reason\": \"counterexample is not accepted by the updated abstraction\"\n}\n";

		try {
			atomicWrite(mExchangeRoot.resolve("cancel-" + var1.jobId() + ".json"), var3);
			mActiveJobs.cancel(var1.jobId());
			mOutstandingJobs.remove(var1.jobId());
			mLogger.info("Cancelled stale worker job %s after abstraction update %s", var1.jobId(), var2);
		} catch (final IOException var5) {
			throw new IllegalStateException("Could not publish cancellation for worker job " + var1.jobId(), var5);
		}
	}

	private void publishAbstractionUpdate(final int var1, final int var2) {
		final Path var3 = mExchangeRoot.resolve("abstractions");
		final String var4 = String.format("abstraction-%08d", var1);
		final Path var5 = var3.resolve(var4 + ".tmp");
		final Path var6 = var3.resolve(var4 + ".tmp.ats");
		final Path var7 = var3.resolve(var4 + ".ats");

		try {
			Files.createDirectories(var3);
			new AutomatonDefinitionPrinter(new AutomataLibraryServices(getServices()), "nwa", var5.toString(),
					Format.ATS, "", this.abstractionForExchange());

			try {
				Files.move(var6, var7, StandardCopyOption.ATOMIC_MOVE);
			} catch (final IOException var9) {
				Files.move(var6, var7);
			}

			final String var8 =
					"{\n  \"schemaVersion\": 1,\n  \"abstractionGeneration\": " + var1 + ",\n  \"abstractionSize\": "
							+ var2 + ",\n  \"atsFile\": \"" + escapeJson(var7.getFileName().toString()) + "\"\n}\n";
			atomicWrite(var3.resolve("latest.json"), var8);
			mLogger.info("Published abstraction update %s with %s states", var7, var2);
		} catch (final IOException var10) {
			throw new IllegalStateException("Could not publish abstraction update " + var1, var10);
		}
	}

	private INestedWordAutomaton<String, String> abstractionForExchange() {
		final INestedWordAutomaton<L, IPredicate> abstraction = mAbstraction;
		final VpAlphabet var1 = abstraction.getVpAlphabet();
		final HashSet var2 = new HashSet();
		final HashSet var3 = new HashSet();
		final HashSet var4 = new HashSet();
		var1.getInternalAlphabet().forEach(var1x -> var2.add(var1x.toString()));
		var1.getCallAlphabet().forEach(var1x -> var3.add(var1x.toString()));
		var1.getReturnAlphabet().forEach(var1x -> var4.add(var1x.toString()));
		final NestedWordAutomaton var5 = new NestedWordAutomaton(new AutomataLibraryServices(getServices()),
				new VpAlphabet(var2, var3, var4), () -> "unused");
		final HashMap var6 = new HashMap();
		int var7 = 0;

		for (final IPredicate var8 : abstraction.getStates()) {
			final String var10 = var8.getFormula().toStringDirect();
			final String var11 = "don't care".equals(var10) ? "@EXISTING_STATE@" + var8 : var10;
			final String var12 = var7 + "#" + var11;
			var7++;
			var6.put(var8, var12);
			var5.addState(abstraction.isInitial(var8), abstraction.isFinal(var8), var12);
		}

		for (final IPredicate var13 : abstraction.getStates()) {
			for (final OutgoingInternalTransition<L, IPredicate> var15 : abstraction.internalSuccessors(var13)) {
				var5.addInternalTransition(var6.get(var13), var15.getLetter().toString(), var6.get(var15.getSucc()));
			}

			for (final OutgoingCallTransition<L, IPredicate> var16 : abstraction.callSuccessors(var13)) {
				var5.addCallTransition(var6.get(var13), var16.getLetter().toString(), var6.get(var16.getSucc()));
			}

			for (final OutgoingReturnTransition<L, IPredicate> var17 : abstraction.returnSuccessors(var13)) {
				var5.addReturnTransition(var6.get(var13), var6.get(var17.getHierPred()), var17.getLetter().toString(),
						var6.get(var17.getSucc()));
			}
		}

		return var5;
	}

	private static String jsonStringValue(final String var0, final String var1) throws IOException {
		final String var2 = "\"" + var1 + "\"";
		final int var3 = var0.indexOf(var2);
		final int var4 = var3 < 0 ? -1 : var0.indexOf(58, var3 + var2.length());
		final int var5 = var4 < 0 ? -1 : var0.indexOf(34, var4 + 1);
		final int var6 = var5 < 0 ? -1 : var0.indexOf(34, var5 + 1);
		if (var5 >= 0 && var6 >= 0) {
			return var0.substring(var5 + 1, var6);
		} else {
			throw new IOException("Missing JSON string field " + var1);
		}
	}

	// $VF: Could not inline inconsistent finally blocks
	// Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a
	// copy of the class file (if you have the rights to distribute it!)
	private String findWorkerId(final long var1) throws IOException {
		Throwable var3 = null;
		final Object var4 = null;

		try {
			final Stream<Path> var5 = Files.list(mExchangeRoot);

			try {
				for (final Path var6 : var5.filter(var0 -> var0.getFileName().toString().startsWith("worker-status-"))
						.filter(var0 -> var0.getFileName().toString().endsWith(".json")).toList()) {
					final String var8 = Files.readString(var6, StandardCharsets.UTF_8);
					if (var8.contains("\"pid\": " + var1)) {
						return jsonStringValue(var8, "workerId");
					}
				}
			} finally {
				if (var5 != null) {
					var5.close();
				}
			}

			return null;
		} catch (final Throwable var14) {
			if (var3 == null) {
				var3 = var14;
			} else if (var3 != var14) {
				var3.addSuppressed(var14);
			}

			if (var3 instanceof final IOException var15) {
				throw var15;
			}
			throw new IllegalStateException(var3);
		}
	}

	private static String escapeJson(final String var0) {
		return var0.replace("\\", "\\\\").replace("\"", "\\\"").replace("\b", "\\b").replace("\f", "\\f")
				.replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t");
	}

	private void publishCoordinatorStatus(final int var1) {
		try {
			Files.createDirectories(mExchangeRoot);
			final String var2 = "{\n  \"schemaVersion\": 1,\n  \"abstractionGeneration\": " + var1 + "\n}\n";
			atomicWrite(mExchangeRoot.resolve("coordinator-status.json"), var2);
			mLogger.info("Published coordinator abstraction generation %s", var1);
		} catch (final IOException var3) {
			throw new IllegalStateException("Could not publish coordinator status", var3);
		}
	}

	protected static void atomicWrite(final Path var0, final String var1) throws IOException {
		final Path var2 = var0.resolveSibling(var0.getFileName() + "." + ProcessHandle.current().pid() + "."
				+ Thread.currentThread().threadId() + ".tmp");
		Files.writeString(var2, var1, StandardCharsets.UTF_8);

		try {
			Files.move(var2, var0, StandardCopyOption.ATOMIC_MOVE, StandardCopyOption.REPLACE_EXISTING);
		} catch (final IOException var3) {
			Files.move(var2, var0, StandardCopyOption.REPLACE_EXISTING);
		}
	}

	@Override
	protected void finish() {
		if (mPref.getMultiProcessingComponent() == MultiProcessComponent.COORDINATOR) {
			try {
				final Path var1 = mExchangeRoot.resolve("shutdown.tmp");
				final Path var2 = mExchangeRoot.resolve("shutdown");
				Files.writeString(var1, "coordinator completed\n", StandardCharsets.UTF_8);

				try {
					Files.move(var1, var2, StandardCopyOption.ATOMIC_MOVE);
				} catch (final IOException var3) {
					Files.move(var1, var2);
				}

				mLogger.info("Published worker shutdown marker %s", var2);
			} catch (final IOException var4) {
				throw new AssertionError("Failed to shut down multiprocess workers", var4);
			}
		}

		super.finish();
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		if (mPref.getMultiProcessingComponent() == MultiProcessComponent.COORDINATOR) {
			final int var24 = mAbstraction.size();
			final boolean var25 = super.refineAbstraction();
			if (var25) {
				final int var26 = getIteration();
				this.updateWorkersAfterAbstractionUpdate(var24, var26);
				this.publishCoordinatorStatus(var26);
			}

			return var25;
		} else {
			mStateFactoryForRefinement.setIteration(getIteration());
			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
			final INestedWordAutomaton var1 = mAbstraction;
			final IPredicateUnifier var2 = mRefinementResult.getPredicateUnifier();
			final IHoareTripleChecker var3 = getHoareTripleChecker();
			AutomatonType var4;
			boolean var5;
			NestedWordAutomaton var6;
			InterpolantAutomatonEnhancement var7;
			Object var8;
			boolean var9;
			if (mErrorGeneralizationEngine.hasAutomatonInIteration(getIteration())) {
				mErrorGeneralizationEngine.startDifference();
				var4 = AutomatonType.ERROR;
				var5 = true;
				var9 = false;
				var7 = mErrorGeneralizationEngine.getEnhancementMode();
				var6 = mErrorGeneralizationEngine.getResultBeforeEnhancement();
				var8 = mErrorGeneralizationEngine.getResultAfterEnhancement();
			} else {
				var4 = AutomatonType.FLOYD_HOARE;
				var5 = false;
				var9 = mProofUpdater == null || mProofUpdater.exploitSigmaStarConcatOfIa();
				var6 = mInterpolAutomaton;
				var7 = mPref.interpolantAutomatonEnhancement();
				var8 = enhanceInterpolantAutomaton(var7, var2, var3, var6);
			}

			super.computeAutomataDifference(var1, (INwaOutgoingLetterAndTransitionProvider) var8, var6, var2, var9,
					var3, var7, var5, var4);
			final String var10 =
					new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()) + "InterpolantAutomatonAfterDiff";
			long var11 = System.nanoTime();
			super.writeAutomatonToFile((IAutomaton) var8, var10);
			long var13 = System.nanoTime();
			double var15 = (var13 - var11) / 1.0E9;
			System.out.println("Read Time: " + var15 + " seconds");
			var11 = System.nanoTime();
			final Path var17 = Paths.get(var10 + ".ats");

			try {
				final List<INestedWordAutomaton<String, String>> var18 = mObserver
						.constructRawNestedWordAutomata(Collections.singletonList(this.parseFile(var17.toFile())));
				final PredicateParsingWrapperScript var19 = new PredicateParsingWrapperScript(mCsToolkit);

				for (final INestedWordAutomaton var20 : var18) {
					if (var20.getFinalStates().isEmpty()) {
						throw new AssertionError("A Floyd-Hoare automaton without accepting states is useless.");
					}

					this.buildFloydHoareAutomaton(var19, var20);
				}

				for (final MultiProcessedCegarCoordinator.ReuseAutomaton var32 : mFloydHoareAutomataFromFile) {
					mReuseAutomata.add(new Pair(var32.getAutomaton(), var32.getPredicateUnifier()));
				}

				INwaOutgoingLetterAndTransitionProvider var33 = null;

				for (final Pair var35 : mReuseAutomata) {
					var33 = (INwaOutgoingLetterAndTransitionProvider) var35.getFirst();
				}

				var13 = System.nanoTime();
				var15 = (var13 - var11) / 1.0E9;
				System.out.println("Read Time: " + var15 + " seconds");

				assert var33 != null;

				var6 = (NestedWordAutomaton) var33;
				var8 = var6;
			} catch (final Exception var23) {
				var23.printStackTrace();
			}

			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
			var7 = mPref.interpolantAutomatonEnhancement();
			mAbstraction = null;
			super.computeAutomataDifference(var1, (INwaOutgoingLetterAndTransitionProvider) var8, var6, var2, var9,
					var3, var7, var5, var4);
			minimizeAbstractionIfEnabled();
			final boolean var31 = new Accepts(new AutomataLibraryServices(getServices()),
					(INwaOutgoingLetterAndTransitionProvider) mAbstraction, (NestedWord) mCounterexample.getWord())
							.getResult();
			return !var31;
		}
	}

	protected final NestedWordAutomaton<L, IPredicate> readAutomatonFromAts(final Path var1) throws Exception {
		final long var2 = System.nanoTime();
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AtsParsingTime);

		List var4;
		try {
			var4 = mObserver.constructRawNestedWordAutomata(Collections.singletonList(this.parseFile(var1.toFile())));
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AtsParsingTime);
			mLogger.info("Parsed ATS automaton %s in %.6f s", var1, (System.nanoTime() - var2) / 1.0E9);
		}

		if (var4.size() != 1) {
			throw new IllegalArgumentException(
					"Expected exactly one automaton in " + var1 + " but found " + var4.size());
		} else {
			final INestedWordAutomaton var5 = (INestedWordAutomaton) var4.get(0);
			if (var5.getInitialStates().isEmpty()) {
				throw new IllegalArgumentException("An abstraction without an initial state is unusable: " + var1);
			} else if (var5.getFinalStates().isEmpty()) {
				throw new IllegalArgumentException("An abstraction without an accepting state is unusable: " + var1);
			} else {
				final int var6 = mFloydHoareAutomataFromFile.size();
				this.buildFloydHoareAutomaton(new PredicateParsingWrapperScript(mCsToolkit), var5);
				if (mFloydHoareAutomataFromFile.size() != var6 + 1) {
					throw new IllegalArgumentException("Could not reconstruct all predicates from " + var1);
				} else {
					return mFloydHoareAutomataFromFile.get(var6).mAutomaton;
				}
			}
		}
	}

	// $VF: Could not inline inconsistent finally blocks
	// Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a
	// copy of the class file (if you have the rights to distribute it!)
	protected AutomataTestFileAST parseFile(final File var1) throws Exception {
		Throwable var2 = null;
		final Object var3 = null;

		try {
			final BufferedReader var4 = Files.newBufferedReader(var1.toPath(), StandardCharsets.UTF_8);

			AutomataTestFileAST var10000;
			try {
				final String var5 = var1.getName();
				final String var6 = var1.getAbsolutePath();
				var10000 = new AutomataScriptParserRun(mServices, mLogger, var4, var5, var6).getResult();
			} finally {
				if (var4 != null) {
					var4.close();
				}
			}

			return var10000;
		} catch (final Throwable var12) {
			if (var2 == null) {
				var2 = var12;
			} else if (var2 != var12) {
				var2.addSuppressed(var12);
			}

			if (var2 instanceof final Exception var13) {
				throw var13;
			}
			throw new IllegalStateException(var2);
		}
	}

	protected void buildFloydHoareAutomaton(final PredicateParsingWrapperScript var1,
			final INestedWordAutomaton<String, String> var2) {
		final HashMap var3 = new HashMap();
		final VpAlphabet var4 = mAbstraction.getVpAlphabet();
		addLettersToStringMap(var3, var4.getCallAlphabet());
		addLettersToStringMap(var3, var4.getInternalAlphabet());
		addLettersToStringMap(var3, var4.getReturnAlphabet());
		this.countReusedAndRemovedLetters(var2.getVpAlphabet(), var3);
		final NestedWordAutomaton var5 = new NestedWordAutomaton(new AutomataLibraryServices(getServices()), var4,
				mPredicateFactoryInterpolantAutomata);
		final PredicateUnifier var6 = new PredicateUnifier(mLogger, getServices(), mCsToolkit.getManagedScript(),
				mPredicateFactory, mCsToolkit.getSymbolTable(), SimplificationTechnique.SIMPLIFY_DDA);
		final boolean var7 = var2 instanceof IEpsilonNestedWordAutomaton;
		Pair var8;
		if (var7) {
			final IEpsilonNestedWordAutomaton var9 = (IEpsilonNestedWordAutomaton) var2;
			var8 = constructImpliesExpliesStrings(var9);
		} else {
			var8 = null;
		}

		final Set<String> var24 = var2.getStates();
		final HashMap var10 = new HashMap();
		final HashMap<Term, String> var11 = new HashMap<>();
		final HashMap var12 = new HashMap();
		mAbstraction.getStates().forEach(var2x -> var12.put(this.removeSerialNumber(var2x.toString()), var2x));
		final HashMap<String, IPredicate> var13 = new HashMap<>();

		for (final String var14 : var24) {
			final String var16 = this.removeSerialNumber(var14);
			if (var16.startsWith("@EXISTING_STATE@")) {
				final String var17 = this.removeSerialNumber(var16.substring("@EXISTING_STATE@".length()));
				final IPredicate var18 = (IPredicate) var12.get(var17);
				if (var18 instanceof ISLPredicate) {
					var13.put(var14, mPredicateFactory.newDontCarePredicate(((ISLPredicate) var18).getProgramPoint()));
				} else if (var18 instanceof IMLPredicate) {
					var13.put(var14,
							mPredicateFactory.newMLDontCarePredicate(((IMLPredicate) var18).getProgramPoints()));
				}
			} else {
				final Term var28 = this.parseTerm(var1, var14);
				if (var28 != null) {
					var10.put(var14, var28);
					var11.put(var28, var14);
				}
			}
		}

		final int var25 = var11.size() + var13.size();
		final int var26 = var24.size() - var25;
		final HashMap var27 = new HashMap();
		final HashMap var29 = new HashMap();
		IPredicate var30 = var6.getTruePredicate();
		String var19 = var11.get(var30.getFormula());
		if (var19 != null) {
			this.addState(var2, var5, var27, var29, var30, var19);
			mapStateAliases(var10, var27, var30.getFormula(), var30);
		}

		var30 = var6.getFalsePredicate();
		var19 = var11.get(var30.getFormula());
		if (var19 != null) {
			this.addState(var2, var5, var27, var29, var30, var19);
			mapStateAliases(var10, var27, var30.getFormula(), var30);
		}

		for (final Entry<String, IPredicate> var32 : var13.entrySet()) {
			this.addState(var2, var5, var27, var29, var32.getValue(), var32.getKey());
		}

		for (final Entry<Term, String> var33 : var11.entrySet()) {
			final String var20 = var33.getValue();
			final Term var21 = var33.getKey();
			if (var21 != var6.getTruePredicate().getFormula() && var21 != var6.getFalsePredicate().getFormula()) {
				IPredicate var22;
				if (var7) {
					final Pair var23 = constructImpliesExpliesRelations(var5.getStates(), var20, var29, var8);
					var22 = var6.constructNewPredicate(var21, (Map) var23.getFirst(), (Map) var23.getSecond());
				} else {
					var22 = var6.getOrConstructPredicate(var21);
				}

				this.addState(var2, var5, var27, var29, var22, var20);
				mapStateAliases(var10, var27, var21, var22);
			}
		}

		final int var34 = var26 + var25;
		if (!USE_AUTOMATA_WITH_UNMATCHED_PREDICATES && var26 > 0) {
			mReuseStats.addDroppedAutomata(1);
		} else {
			mReuseStats.addReusedStates(var25);
			mReuseStats.addUselessPredicates(var26);
			mReuseStats.addTotalStates(var34);
			this.addTransitionsFromRawAutomaton(var5, var2, var3, var27);
			final MultiProcessedCegarCoordinator.ReuseAutomaton var38 =
					new MultiProcessedCegarCoordinator.ReuseAutomaton(var5, var4, var6);
			mFloydHoareAutomataFromFile.add(var38);
			mReuseStats.addAutomataFromFile(1);
		}
	}

	private static Pair<HashRelation<String, String>, HashRelation<String, String>>
			constructImpliesExpliesStrings(final IEpsilonNestedWordAutomaton<String, String> var0) {
		final HashRelation var1 = new HashRelation();
		final HashRelation var2 = new HashRelation();

		for (final String var3 : var0.getStates()) {
			for (final String var5 : var0.epsilonSuccessors(var3)) {
				var1.addPair(var3, var5);
				var2.addPair(var5, var3);
			}
		}

		return new Pair(var1, var2);
	}

	private static Pair<HashMap<IPredicate, Validity>, HashMap<IPredicate, Validity>> constructImpliesExpliesRelations(
			final Set<IPredicate> var0, final String var1, final HashMap<IPredicate, String> var2,
			final Pair<HashRelation<String, String>, HashRelation<String, String>> var3) {
		final HashRelation var4 = var3.getFirst();
		final HashRelation var5 = var3.getSecond();
		final HashMap var6 = new HashMap();
		final HashMap var7 = new HashMap();

		for (final IPredicate var8 : var0) {
			final String var10 = var2.get(var8);
			if (var4.containsPair(var1, var10)) {
				var6.put(var8, Validity.VALID);
			} else {
				var6.put(var8, Validity.INVALID);
			}

			if (var5.containsPair(var1, var10)) {
				var7.put(var8, Validity.VALID);
			} else {
				var7.put(var8, Validity.INVALID);
			}
		}

		return new Pair(var6, var7);
	}

	private void addState(final INestedWordAutomaton<String, String> var1, final NestedWordAutomaton<L, IPredicate> var2,
			final HashMap<String, IPredicate> var3, final HashMap<IPredicate, String> var4, final IPredicate var5, final String var6) {
		var3.put(var6, var5);
		var4.put(var5, var6);
		final boolean var7 = var1.isInitial(var6);
		final boolean var8 = var1.isFinal(var6);
		if (!var2.getStates().contains(var5)) {
			var2.addState(var7, var8, var5);
		}
	}

	private static void mapStateAliases(final Map<String, Term> var0, final Map<String, IPredicate> var1, final Term var2,
			final IPredicate var3) {
		var0.entrySet().stream().filter(var1x -> var1x.getValue().equals(var2))
				.forEach(var2x -> var1.put(var2x.getKey(), var3));
	}

	private Term parseTerm(final PredicateParsingWrapperScript var1, final String var2) {
		try {
			final String var4 = this.removeSerialNumber(var2);
			return TermParseUtils.parseTerm(var1, var4);
		} catch (final Exception var5) {
			mLogger.warn("Exception during parsing of " + var2 + ": " + var5.getMessage());
			return null;
		}
	}

	private String removeSerialNumber(final String var1) {
		final String[] var2 = var1.split("#", 2);
		if (var2.length == 1) {
			mLogger.warn("String " + var1 + " doesn't have a # symbol in it. Kepping entire string.");
			return var2[0];
		} else if (var2.length == 2) {
			return var2[1];
		} else {
			mLogger.warn("Unexpected result from String's split function. String parsing failed.");
			throw new UnsupportedOperationException("String parsing failed");
		}
	}

	private static final <LETTER> void addLettersToStringMap(final Map<String, Set<LETTER>> var0, final Set<LETTER> var1) {
		for (final Object var2 : var1) {
			final String var4 = var2.toString();
			final Set var5 = var0.get(var4);
			if (var5 == null) {
				final HashSet var6 = new HashSet();
				var6.add(var2);
				var0.put(var4, var6);
			} else {
				var5.add(var2);
			}
		}
	}

	private final void countReusedAndRemovedLetters(final VpAlphabet<String> var1, final Map<String, Set<L>> var2) {
		int var3 = 0;
		int var4 = 0;
		final HashSet<String> var5 = new HashSet<>(var1.getInternalAlphabet());
		var5.addAll(var1.getReturnAlphabet());
		var5.addAll(var1.getCallAlphabet());

		for (final String var6 : var5) {
			if (var2.containsKey(var6)) {
				var4++;
			} else {
				var3++;
			}
		}

		final int var8 = var3 + var4;
		mReuseStats.addReusedLetters(var4);
		mReuseStats.addTotalLetters(var8);
	}

	private final void addTransitionsFromRawAutomaton(final NestedWordAutomaton<L, IPredicate> var1,
			final INestedWordAutomaton<String, String> var2, final Map<String, Set<L>> var3, final Map<String, IPredicate> var4) {
		int var5 = 0;
		int var6 = 0;
		final Set<IPredicate> var7 = var1.getStates();

		for (final String var8 : var2.getStates()) {
			final IPredicate var10 = var4.get(var8);
			if (var10 != null) {
				for (final OutgoingCallTransition var11 : var2.callSuccessors(var8)) {
					final Pair<Set<L>, IPredicate> var13 = this.filterTransitions(var11, var3, var4, var7);
					if (var13 == null) {
						var5++;
					} else {
						for (final L var14 : var13.getFirst()) {
							var1.addCallTransition(var10, var14, var13.getSecond());
							var6++;
						}
					}
				}

				for (final OutgoingInternalTransition var18 : var2.internalSuccessors(var8)) {
					final Pair<Set<L>, IPredicate> var22 = this.filterTransitions(var18, var3, var4, var7);
					if (var22 == null) {
						var5++;
					} else {
						for (final L var24 : var22.getFirst()) {
							var1.addInternalTransition(var10, var24, var22.getSecond());
							var6++;
						}
					}
				}

				for (final OutgoingReturnTransition var19 : var2.returnSuccessors(var8)) {
					final Pair<Set<L>, IPredicate> var23 = this.filterTransitions(var19, var3, var4, var7);
					if (var23 == null) {
						var5++;
					} else {
						final IPredicate var25 = var4.get(var19.getHierPred());
						if (!var7.contains(var25)) {
							var5++;
						} else {
							for (final L var27 : var23.getFirst()) {
								var1.addReturnTransition(var10, var25, var27, var23.getSecond());
								var6++;
							}
						}
					}
				}
			}
		}

		final int var17 = var5 + var6;
		mReuseStats.addReusedTransitions(var6);
		mReuseStats.addTotalTransitions(var17);
	}

	private Pair<Set<L>, IPredicate> filterTransitions(final IOutgoingTransitionlet<String, String> var1,
			final Map<String, Set<L>> var2, final Map<String, IPredicate> var3, final Set<IPredicate> var4) {
		final Set var5 = var2.get(var1.getLetter());
		if (var5 == null) {
			return null;
		} else {
			final String var6 = var1.getSucc();
			final IPredicate var7 = var3.get(var6);
			return !var4.contains(var7) ? null : new Pair(var5, var7);
		}
	}

	public final class ReuseAutomaton {
		private final boolean mUseEnhancement;
		private final IPredicateUnifier mPredicateUnifier;
		private final NestedWordAutomaton<L, IPredicate> mAutomaton;
		private final VpAlphabet<L> mAbstractionAlphabet;
		private AbstractInterpolantAutomaton<L> mEnhancedAutomaton;
		private IHoareTripleChecker mHtc;

		private ReuseAutomaton(final NestedWordAutomaton<L, IPredicate> var2, final VpAlphabet<L> var3, final IPredicateUnifier var4) {
			mPredicateUnifier = var4;
			mAutomaton = var2;
			mAbstractionAlphabet = var3;
			mUseEnhancement = MultiProcessedCegarCoordinator.this.mPref
					.getFloydHoareAutomataReuseEnhancement() != FloydHoareAutomataReuseEnhancement.NONE;
		}

		public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getAutomaton() {
			return mUseEnhancement ? this.getEnhancedInterpolantAutomaton() : mAutomaton;
		}

		public IHoareTripleChecker getHtc() {
			if (!mUseEnhancement) {
				throw new UnsupportedOperationException("You should not need a Hoare Triple Checker in this mode");
			} else {
				if (mHtc == null) {
					mHtc = this.constructHtc();
				}

				return mHtc;
			}
		}

		private IHoareTripleChecker constructHtc() {
			final FloydHoareAutomataReuseEnhancement var1 =
					MultiProcessedCegarCoordinator.this.mPref.getFloydHoareAutomataReuseEnhancement();

			return switch (var1) {
			case NONE -> throw new UnsupportedOperationException("Illegal mode: " + var1);
			case AS_USUAL -> HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(getServices(),
					MultiProcessedCegarCoordinator.this.mPref.getHoareTripleChecks(),
					MultiProcessedCegarCoordinator.this.mCsToolkit, this.getPredicateUnifier());
			case ONLY_NEW_LETTERS -> this.constructEfficientIgnoringHtc(false);
			case ONLY_NEW_LETTERS_SOLVER -> this.constructEfficientIgnoringHtc(true);
			default -> throw new MatchException(null, null);
			};
		}

		private IHoareTripleChecker constructEfficientIgnoringHtc(final boolean var1) throws AssertionError {
			final Set var2 = this.constructOldAlphabet();
			final Predicate var3 = var2::contains;
			ChainingHoareTripleChecker var5 =
					HoareTripleCheckerUtils.constructSdHoareTripleChecker(MultiProcessedCegarCoordinator.this.mLogger,
							MultiProcessedCegarCoordinator.this.mCsToolkit, this.getPredicateUnifier());
			if (!var1) {
				var5 = var5.actionsProtectedBy(var3);
			}

			var5 = var5.andThen(HoareTripleCheckerUtils.constructSmtHoareTripleChecker(
					MultiProcessedCegarCoordinator.this.mLogger, HoareTripleChecks.INCREMENTAL,
					MultiProcessedCegarCoordinator.this.mCsToolkit, this.getPredicateUnifier()));
			return new CachingHoareTripleChecker(getServices(), var5, this.getPredicateUnifier());
		}

		private Set<L> constructOldAlphabet() {
			return DataStructureUtils.union(
					DataStructureUtils.intersection(mAbstractionAlphabet.getInternalAlphabet(),
							mAutomaton.getVpAlphabet().getInternalAlphabet()),
					DataStructureUtils.intersection(mAbstractionAlphabet.getCallAlphabet(),
							mAutomaton.getVpAlphabet().getCallAlphabet()),
					DataStructureUtils.intersection(mAbstractionAlphabet.getReturnAlphabet(),
							mAutomaton.getVpAlphabet().getReturnAlphabet()));
		}

		public IStatisticsDataProvider getEdgeCheckerBenchmark() {
			return mHtc == null ? new HoareTripleCheckerStatisticsGenerator() : mHtc.getStatistics();
		}

		public IPredicateUnifier getPredicateUnifier() {
			return mPredicateUnifier;
		}

		private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getEnhancedInterpolantAutomaton() {
			if (mEnhancedAutomaton == null) {
				mEnhancedAutomaton =
						constructInterpolantAutomatonForOnDemandEnhancement(mAutomaton, this.getPredicateUnifier(),
								this.getHtc(), InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION);
			}

			return mEnhancedAutomaton;
		}
	}
}
