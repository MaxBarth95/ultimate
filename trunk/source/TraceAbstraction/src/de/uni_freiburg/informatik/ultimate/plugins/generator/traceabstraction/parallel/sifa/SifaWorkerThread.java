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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.sifa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.function.BooleanSupplier;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.icfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.lib.icfg.PathProgram.PathProgramConstructionResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.RecursiveProgramException;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.HeapBudgetTimer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ICegarNwaWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ParallelNwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker.TransferMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.absint.AbsIntWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.IInvariantSink;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantMessage.TrustedInvariants;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantSupplier;
import de.uni_freiburg.informatik.ultimate.plugins.sifa.SifaBuilder;

/**
 * Single-shot worker of {@link ParallelNwaCegarLoop} running symbolic interpretation with fluid abstractions (SIFA) on
 * the whole program, with one domain after the other: SAFE as soon as one proves no error location reachable,
 * otherwise each result is submitted to the {@link InvariantSupplier} as invariants of the loop heads. Works like
 * {@link AbsIntWorkerThread}, but SIFA asks an SMT solver and walks an {@link IIcfg}. So the constructor (main thread)
 * transfers every letter of the initial abstraction into a solver of the worker's own and builds a {@link PathProgram}
 * of these copies: a graph of its own, which the edges other workers attach to the ICFG's locations do not change.
 * Each domain gets its own solver, so one that is stopped under a query leaves nothing behind for the next, and a time
 * and memory budget; one that runs out gives no result.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class SifaWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {

	/**
	 * @param script
	 *            the domain's own solver, which the program's transitions belong to
	 * @param toOriginal
	 *            the location of the original ICFG for each location of the program
	 * @param loopHeads
	 *            the locations of the program whose invariants are submitted
	 * @param errorLocations
	 *            the locations of the program that must be unreachable
	 */
	private record DomainRun(String domain, ManagedScript script, PathProgram program,
			Map<IcfgLocation, IcfgLocation> toOriginal, Set<IcfgLocation> loopHeads, Set<IcfgLocation> errorLocations) {
	}

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final long mDomainBudgetMs;
	private final long mHeapBudgetBytes;
	// True once the CEGAR loop is done, before it shuts the toolchain's services down.
	private final BooleanSupplier mShuttingDown;
	private final BlockingQueue<WorkerThreadResult<L, A>> mResultQueue;
	private final IInvariantSink mSink;
	private final List<DomainRun> mRuns;

	/**
	 * @param domains
	 *            the names of SIFA domains (see {@link SifaBuilder#DOMAINS}), in the order in which they run
	 * @param domainBudgetSeconds
	 *            how long each domain may run; one that runs out gives no result and the next one starts
	 * @param heapBudgetPercent
	 *            how much of the JVM's maximum heap may be in use while a domain runs; a domain that exceeds it is
	 *            stopped like one that runs out of time
	 * @param transfers
	 *            a fresh solver of the worker's own with each call, as a transfer from the main script
	 * @param shuttingDown
	 *            whether the CEGAR loop is done, which is why a service may be gone
	 */
	public SifaWorkerThread(final ILogger logger, final IUltimateServiceProvider services,
			final INestedWordAutomaton<L, IPredicate> abstraction, final IIcfg<?> icfg, final IInvariantSink sink,
			final List<String> domains, final int domainBudgetSeconds, final int heapBudgetPercent,
			final Supplier<TransferBetweenMainAndWorker<L, IPredicate>> transfers,
			final BlockingQueue<WorkerThreadResult<L, A>> resultQueue, final BooleanSupplier shuttingDown) {
		if (domainBudgetSeconds <= 0) {
			throw new IllegalArgumentException("The time budget per domain must be positive: " + domainBudgetSeconds);
		}
		if (heapBudgetPercent < 1 || heapBudgetPercent > 100) {
			throw new IllegalArgumentException(
					"The memory budget per domain must be 1 to 100 % of the maximum heap: " + heapBudgetPercent);
		}
		for (final String domain : domains) {
			if (!SifaBuilder.DOMAINS.contains(domain)) {
				throw new IllegalArgumentException(
						"Unknown SIFA domain " + domain + ", known are " + SifaBuilder.DOMAINS);
			}
		}
		mLogger = logger;
		mServices = services;
		mDomainBudgetMs = domainBudgetSeconds * 1000L;
		mHeapBudgetBytes = Runtime.getRuntime().maxMemory() / 100 * heapBudgetPercent;
		mShuttingDown = shuttingDown;
		mResultQueue = resultQueue;
		mSink = sink;
		final List<DomainRun> runs = new ArrayList<>();
		for (final String domain : domains) {
			runs.add(prepareRun(domain, abstraction, icfg, transfers.get()));
		}
		mRuns = runs;
		mLogger.info("SIFA: %d loop head(s) of interest", mRuns.isEmpty() ? 0 : mRuns.get(0).loopHeads().size());
	}

	/**
	 * Copies the program into the given transfer's solver. Must run on the main thread: it reads main-script terms and
	 * attaches the copies to the ICFG's locations.
	 */
	private DomainRun prepareRun(final String domain, final INestedWordAutomaton<L, IPredicate> abstraction,
			final IIcfg<?> icfg, final TransferBetweenMainAndWorker<L, IPredicate> transfer) {
		final VpAlphabet<L> alphabet = abstraction.getVpAlphabet();
		final Set<L> letters = new LinkedHashSet<>();
		for (final Set<L> part : List.of(alphabet.getInternalAlphabet(), alphabet.getCallAlphabet(),
				alphabet.getReturnAlphabet())) {
			for (final L letter : part) {
				letters.add(transfer.transferLetter(letter, TransferMode.MAIN2WORKER));
			}
		}
		final PathProgramConstructionResult construction = PathProgram.constructPathProgram("sifa-" + domain, icfg,
				letters, Set.of(), loc -> true, transfer.getWorkerCfgSmtToolKit());
		final Map<IcfgLocation, IcfgLocation> toOriginal = new HashMap<>();
		for (final Entry<IcfgLocation, IcfgLocation> entry : construction.getLocationMapping().entrySet()) {
			toOriginal.put(entry.getValue(), entry.getKey());
		}
		final PathProgram program = construction.getPathProgram();
		// The heads k-induction asks for, and those the ICFG knows of.
		final Set<IcfgLocation> loopHeads = LoopHeads.of(program);
		loopHeads.addAll(program.getLoopLocations());
		return new DomainRun(domain, transfer.getWorkerCfgSmtToolKit().getManagedScript(), program, toOriginal,
				Set.copyOf(loopHeads), Set.copyOf(IcfgInterpreter.allErrorLocations(program)));
	}

	@Override
	public void run() {
		Thread.currentThread().setName("SIFA Thread");
		try {
			mResultQueue.put(analyze());
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
		} catch (final Throwable t) {
			if (mShuttingDown.getAsBoolean()) {
				// The CEGAR loop is done and took the services down under the running analysis. Nobody waits for it.
				mLogger.info("SIFA: stopping, shut down during the analysis (" + t + ")");
				return;
			}
			mLogger.error("SIFA worker crashed: " + t);
			for (final StackTraceElement element : t.getStackTrace()) {
				mLogger.error("\tat " + element);
			}
			try {
				mResultQueue.put(new WorkerThreadResult<>(WorkerType.SIFA, null, null, null, null, null, true));
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
		}
	}

	private WorkerThreadResult<L, A> analyze() {
		for (final DomainRun run : mRuns) {
			final Map<IcfgLocation, Term> invariants;
			// Created here, the budget starts now.
			final HeapBudgetTimer timer = new HeapBudgetTimer(
					mServices.getProgressMonitorService().getChildTimer(mDomainBudgetMs), mHeapBudgetBytes);
			// SIFA's SMT work and our quantifier elimination stop at the budget too, not only the fixpoint loop.
			final IUltimateServiceProvider services =
					mServices.getProgressMonitorService().registerChildTimer(mServices, timer);
			try {
				final Set<IcfgLocation> locationsOfInterest = new LinkedHashSet<>(run.loopHeads());
				locationsOfInterest.addAll(run.errorLocations());
				final Map<IcfgLocation, IPredicate> result = new SifaBuilder(services, mLogger)
						.construct(run.program(), timer, locationsOfInterest, run.domain()).getIcfgInterpreter()
						.interpret();
				if (run.errorLocations().stream()
						.allMatch(loc -> SmtUtils.isFalseLiteral(result.get(loc).getFormula()))) {
					mLogger.info("SIFA: %s proves that no error location is reachable, the program is safe",
							run.domain());
					return new WorkerThreadResult<>(WorkerType.SIFA, null, null, null, null, null, false);
				}
				invariants = toInvariants(services, run, result);
			} catch (final ToolchainCanceledException e) {
				if (timer.isHeapBudgetExceeded()) {
					mLogger.warn("SIFA: %s exceeded its memory budget (%d MB of heap in use, budget %d MB)",
							run.domain(), timer.getHeapUsedWhenExceeded() >> 20, mHeapBudgetBytes >> 20);
					// Most of the heap is the domain's garbage. Collecting it now lets the JVM shrink its heap
					// instead of keeping it committed while the other workers and their solvers need the memory.
					System.gc();
					continue;
				}
				if (mServices.getProgressMonitorService().continueProcessing()) {
					mLogger.warn("SIFA: %s ran out of its %d s budget", run.domain(), mDomainBudgetMs / 1000);
					continue;
				}
				mLogger.warn("SIFA: stopped during %s, %s", run.domain(), e.getMessage());
				return WorkerThreadResult.noVerdict(WorkerType.SIFA);
			} catch (final RecursiveProgramException e) {
				// The call graph is the same for every domain, none of the others could do better.
				mLogger.warn("SIFA: gave up, %s", e.getMessage());
				return WorkerThreadResult.noVerdict(WorkerType.SIFA);
			} catch (final UnsupportedOperationException e) {
				mLogger.warn("SIFA: %s gave up, %s", run.domain(), e.getMessage());
				continue;
			}
			mSink.submit(new TrustedInvariants(run.script(), invariants, "SIFA " + run.domain()));
			mLogger.info("SIFA: submitted invariants of %d location(s) found by %s", invariants.size(), run.domain());
		}
		mLogger.info("SIFA: all domains done");
		return WorkerThreadResult.noVerdict(WorkerType.SIFA);
	}

	/**
	 * The predicates of the loop heads, at the locations of the original ICFG. Only quantifier-free terms: SIFA keeps
	 * the exact post of a small predicate, whose quantifiers k-induction would have to eliminate in every query. SIFA
	 * itself only runs the light elimination, so the quantified conjuncts go through our full elimination here, and
	 * only what is still quantified afterwards is dropped.
	 */
	private Map<IcfgLocation, Term> toInvariants(final IUltimateServiceProvider services, final DomainRun run,
			final Map<IcfgLocation, IPredicate> result) {
		final Map<IcfgLocation, Term> invariants = new HashMap<>();
		int eliminated = 0;
		int dropped = 0;
		for (final IcfgLocation loopHead : run.loopHeads()) {
			final List<Term> kept = new ArrayList<>();
			for (final Term conjunct : SmtUtils.getConjuncts(result.get(loopHead).getFormula())) {
				if (QuantifierUtils.isQuantifierFree(conjunct)) {
					kept.add(conjunct);
					continue;
				}
				final Term withoutQuantifiers = PartialQuantifierElimination.eliminate(services, run.script(),
						conjunct, SimplificationTechnique.SIMPLIFY_DDA);
				boolean allEliminated = true;
				for (final Term part : SmtUtils.getConjuncts(withoutQuantifiers)) {
					if (QuantifierUtils.isQuantifierFree(part)) {
						kept.add(part);
					} else {
						allEliminated = false;
						dropped++;
					}
				}
				if (allEliminated) {
					eliminated++;
				}
			}
			invariants.put(run.toOriginal().get(loopHead), SmtUtils.and(run.script().getScript(), kept));
		}
		if (eliminated > 0 || dropped > 0) {
			mLogger.info(
					"SIFA: eliminated the quantifiers of %d conjunct(s), dropped %d still quantified conjunct(s) found by %s",
					eliminated, dropped, run.domain());
		}
		return invariants;
	}
}
