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

import java.time.Instant;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.proofs.PrePostConditionSpecification;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.FloydHoareMapping;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.FloydHoareUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateParsingWrapperScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.JsonCodec.ResultStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.multiprocessed.JsonCodec.VerdictValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TaJobProcessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.MultiProcessComponent;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;

/**
 * The WITNESS session kind: the only kind that writes witnesses. It collects the evidence of the run while it goes on
 * (the words of {@code RESULT} SAT, the {@code PROOF_ANNOTATION}) and, when the {@code VERDICT} arrives, reports the
 * results from which the WitnessPrinter that follows in the toolchain writes {@code out/witness.yml}.
 * <ul>
 * <li>FALSE: the word of the verdict (or the newest SAT word) as a counterexample. The witness degrades step by step: a
 * run with values from a new trace check, the run without values, the target only. If none of them can be
 * backtranslated, there is no witness and the session throws; it never writes an empty one.</li>
 * <li>TRUE: the invariants of the newest proof annotation. Invariants that do not parse are dropped. Without an
 * annotation, or if none of its invariants parses, there is no witness and the session throws: it never stands in a
 * trivial correctness witness for a missing proof. (A program without loops has no invariant to report, as in plain
 * Automizer.)</li>
 * <li>UNKNOWN: no witness.</li>
 * </ul>
 * The verdict itself is fixed by the scheduler when it arrives, so a failure here never changes it.
 *
 * @param <L>
 *            the letter type
 */
public final class WitnessSession<L extends IIcfgTransition<?>> {

	/**
	 * How much of a violation witness could be built, also counted in the statistics as {@code witnessLevel}.
	 */
	public enum ViolationLevel {
		/** No witness. */
		NONE,
		/** Only the target. */
		TARGET_ONLY,
		/** The whole word, without values. */
		WITHOUT_VALUES,
		/** The whole word with the values of a trace check. */
		WITH_VALUES
	}

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IIcfg<IcfgLocation> mIcfg;
	private final IExchange mExchange;
	private final INestedWordAutomaton<L, IPredicate> mInitialAbstraction;
	private final PredicateFactory mPredicateFactory;
	private final Consumer<IResult> mReporter;
	private final LetterNaming<L> mLetters;
	private final LocationNaming mLocations;
	private final SessionStatistics mStatistics;
	private NestedWord<L> mNewestViolation;
	private JsonCodec.ProofAnnotation mNewestAnnotation;

	/**
	 * @param reporter
	 *            reports a result to the result service, where the WitnessPrinter finds it
	 */
	public WitnessSession(final IUltimateServiceProvider services, final ILogger logger, final TAPreferences prefs,
			final IIcfg<IcfgLocation> icfg, final IExchange exchange, final PredicateFactory predicateFactory,
			final INestedWordAutomaton<L, IPredicate> initialAbstraction, final Consumer<IResult> reporter) {
		mServices = services;
		mLogger = logger;
		mIcfg = icfg;
		mExchange = exchange;
		mInitialAbstraction = initialAbstraction;
		mPredicateFactory = predicateFactory;
		mReporter = reporter;
		mLetters = new LetterNaming<>(initialAbstraction.getVpAlphabet());
		mLocations = new LocationNaming(icfg);
		mStatistics = new SessionStatistics(MultiProcessComponent.WITNESS, prefs.getMultiProcessSessionId());
		mStatistics.declare("results", "resultsSat", "proofAnnotations", "invariantsReported", "invariantsDropped",
				"witnessLevel");
	}

	/**
	 * @return the statistics of this session, for {@code out/statistics.json}
	 */
	public SessionStatistics getStatistics() {
		return mStatistics;
	}

	/**
	 * Collects evidence until the verdict arrives, then reports the results of the witness.
	 *
	 * @return how the session ended
	 */
	public SessionStatistics.End run() {
		final long deadlineMillis = mServices.getProgressMonitorService().getDeadline();
		if (deadlineMillis <= 0) {
			throw new IllegalArgumentException("A WITNESS session needs a time limit (the toolchain timeout)");
		}
		final Instant deadline = Instant.ofEpochMilli(deadlineMillis);
		while (true) {
			final Optional<ExchangeMessage> next;
			try {
				next = mExchange.take(deadline);
			} catch (final DeadlineExpiredException e) {
				mLogger.info("WITNESS reached its time limit before a verdict");
				return SessionStatistics.End.TIME_LIMIT;
			}
			if (next.isEmpty()) {
				mLogger.info("WITNESS shuts down before a verdict");
				return SessionStatistics.End.SHUTDOWN;
			}
			final ExchangeMessage message = next.get();
			switch (message.type()) {
			case RESULT:
				collectResult(message);
				break;
			case PROOF_ANNOTATION:
				mNewestAnnotation = JsonCodec.decode(message.body(), JsonCodec.ProofAnnotation.class);
				mStatistics.increment("proofAnnotations");
				break;
			case VERDICT:
				produceWitness(JsonCodec.decode(message.body(), JsonCodec.Verdict.class));
				return SessionStatistics.End.DONE;
			default:
				throw new IllegalArgumentException("A WITNESS does not accept " + message.type());
			}
		}
	}

	private void collectResult(final ExchangeMessage message) {
		final JsonCodec.Result result = JsonCodec.decode(message.body(), JsonCodec.Result.class);
		mStatistics.increment("results");
		if (!result.isSynthetic() && result.status() == ResultStatus.SAT) {
			mNewestViolation = WordCodec.decode(new WordCodec.EncodedWord(result.word(), result.nesting()), mLetters);
			mStatistics.increment("resultsSat");
		}
	}

	private void produceWitness(final JsonCodec.Verdict verdict) {
		mLogger.info("WITNESS: verdict %s from %s", verdict.verdict(), verdict.decidedBy());
		if (verdict.verdict() == VerdictValue.FALSE) {
			final JsonCodec.Evidence evidence = verdict.evidence();
			final NestedWord<L> word = evidence.word() != null
					? WordCodec.decode(new WordCodec.EncodedWord(evidence.word(), evidence.nesting()), mLetters)
					: mNewestViolation;
			if (word == null) {
				throw new IllegalStateException("Verdict FALSE without a counterexample word: no violation witness");
			}
			reportViolation(word);
		} else if (verdict.verdict() == VerdictValue.TRUE) {
			reportCorrectness();
		} else {
			mLogger.info("WITNESS: no witness for an UNKNOWN verdict");
		}
	}

	private void reportViolation(final NestedWord<L> word) {
		final NestedRun<L, IPredicate> run = RunReplay.replay(mInitialAbstraction, word);
		final IcfgLocation errorLoc = run.getSymbol(run.getLength() - 2).getTarget();
		final IProgramExecution<L, Term> withValues = executionWithValues(word, run);
		if (withValues != null && tryReport(errorLoc, withValues, ViolationLevel.WITH_VALUES)) {
			return;
		}
		final IcfgProgramExecution<L> withoutValues = withOrigin(
				TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(word));
		if (tryReport(errorLoc, withoutValues, ViolationLevel.WITHOUT_VALUES)) {
			return;
		}
		final IcfgProgramExecution<L> targetOnly = withOrigin(TraceCheckUtils
				.computeSomeIcfgProgramExecutionWithoutValues(new NestedWord<>(word.getSymbol(word.length() - 1),
						NestedWord.INTERNAL_POSITION)));
		if (tryReport(errorLoc, targetOnly, ViolationLevel.TARGET_ONLY)) {
			return;
		}
		mStatistics.set("witnessLevel", ViolationLevel.NONE.ordinal());
		throw new IllegalStateException("No violation witness can be built for the counterexample of length "
				+ word.length() + ": every degradation failed to backtranslate");
	}

	/**
	 * @return the execution of a new trace check with values, or null if the check does not confirm the word
	 */
	private IProgramExecution<L, Term> executionWithValues(final NestedWord<L> word, final NestedRun<L, IPredicate> run) {
		final CfgSmtToolkit toolkit = mIcfg.getCfgSmtToolkit();
		try {
			final PredicateUnifier unifier = unifier();
			final List<IcfgLocation> locations = TaJobProcessor.getIcfgLocationsFromRun(run);
			final TraceCheck<L> traceCheck = new TraceCheck<>(unifier.getTruePredicate(),
					unifier.getFalsePredicate(), new TreeMap<>(), new Counterexample<>(word, locations), mServices,
					toolkit, AssertCodeBlockOrder.NOT_INCREMENTALLY, true, false);
			if (traceCheck.isCorrect() != LBool.SAT || !traceCheck.providesRcfgProgramExecution()) {
				mLogger.warn("WITNESS: the trace check answers %s, the witness goes without values",
						traceCheck.isCorrect());
				return null;
			}
			return withOrigin(traceCheck.getRcfgProgramExecution());
		} catch (final RuntimeException e) {
			// the verdict stays; the witness degrades
			mLogger.warn("WITNESS: the trace check failed, the witness goes without values: " + e);
			return null;
		}
	}

	private IcfgProgramExecution<L> withOrigin(final IcfgProgramExecution<L> execution) {
		execution.setOriginCfgScript(mIcfg.getCfgSmtToolkit().getManagedScript());
		return execution;
	}

	/**
	 * Reports a counterexample if its backtranslation works (the result backtranslates in its constructor).
	 */
	private boolean tryReport(final IcfgLocation errorLoc, final IProgramExecution<L, Term> execution,
			final ViolationLevel level) {
		final CounterExampleResult<IcfgLocation, L, Term> result;
		try {
			result = new CounterExampleResult<>(errorLoc, Activator.PLUGIN_NAME,
					mServices.getBacktranslationService(), execution);
		} catch (final RuntimeException e) {
			mLogger.warn("WITNESS: the %s witness cannot be backtranslated, degrading: %s", level, e);
			return false;
		}
		mReporter.accept(result);
		mStatistics.set("witnessLevel", level.ordinal());
		mLogger.info("WITNESS: reported a violation, witness level %s", level);
		return true;
	}

	private void reportCorrectness() {
		if (mNewestAnnotation == null) {
			throw new IllegalStateException("Verdict TRUE without a proof annotation: no correctness witness");
		}
		final PredicateUnifier unifier = unifier();
		final PredicateParsingWrapperScript parsingScript =
				new PredicateParsingWrapperScript(mIcfg.getCfgSmtToolkit());
		final Map<IcfgLocation, IPredicate> annotation = new HashMap<>();
		final SortedMap<String, String> invariants = mNewestAnnotation.invariants();
		for (final Map.Entry<String, String> entry : invariants.entrySet()) {
			final IcfgLocation loc = mLocations.resolve(entry.getKey());
			try {
				annotation.put(loc, unifier.getOrConstructPredicate(TermParseUtils.parseTerm(parsingScript,
						entry.getValue())));
			} catch (final RuntimeException e) {
				// a weaker annotation is still a proof annotation; the verdict stays
				mLogger.warn("WITNESS: dropping the invariant at %s, it does not parse: %s", entry.getKey(), e);
				mStatistics.increment("invariantsDropped");
			}
		}
		if (annotation.isEmpty() && !invariants.isEmpty()) {
			throw new IllegalStateException("No invariant of the proof annotation parses: no correctness witness");
		}
		final int[] count = { 0 };
		FloydHoareUtils.createInvariantResults(Activator.PLUGIN_NAME, mIcfg,
				new FloydHoareMapping<>(PrePostConditionSpecification.forIcfg(mIcfg, unifier), annotation),
				mServices.getBacktranslationService(), result -> {
					count[0]++;
					mReporter.accept(result);
				});
		// a program without loops has no invariant to report; that is the witness plain Automizer writes, too
		mStatistics.set("invariantsReported", count[0]);
		mReporter.accept(AllSpecificationsHoldResult.createAllSpecificationsHoldResult(Activator.PLUGIN_NAME,
				IcfgUtils.getErrorLocations(mIcfg).size()));
		mLogger.info("WITNESS: reported %s invariants of the proof annotation (generation %s)", count[0],
				mNewestAnnotation.generation());
	}

	private PredicateUnifier unifier() {
		final CfgSmtToolkit toolkit = mIcfg.getCfgSmtToolkit();
		return new PredicateUnifier(mLogger, mServices, toolkit.getManagedScript(), mPredicateFactory,
				toolkit.getSymbolTable(), SimplificationTechnique.SIMPLIFY_DDA);
	}
}
