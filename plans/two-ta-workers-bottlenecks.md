# Make two-ta-workers the best UParalizer configuration

## Context
Run `value.2026-11-19_21-09-33` (17,948 tasks; 900 s, 15 GB, 4 cores) compared UParalizer (U: 1 TA +
1 k-induction + value analysis + invariant supplier) with two-ta-workers (T: the same with 2 TA workers).
T solves the most tasks (11,545 vs 11,481; it wins 272 tasks and loses 208). But it is slower on most solved tasks
(geometric mean 1.04×). The user wants T to be faster than U on most tasks, ideally on every task, and to lose almost
none of U's tasks.
The numbers come from the table and a scan of all U, T and k-induction-only logs. The logs were read straight from
the zip, which was still downloading; the U and T logs in it were complete.

## What the data shows
**Who decides the tasks** (both configurations agree): k-induction 7,682 · TA proof 1,642 · value analysis 429 ·
TA counterexample 387 · trivial 352.
T compared with U, on tasks both solve from the same source:
- k-induction: 1.051× (T faster on 1,179, slower on 3,556)
- TA proof: 1.018×
- TA counterexample: **0.914×**
- U walltime > 200 s: **0.80×**

So the second TA worker pays off on hard tasks and on bugs. Where k-induction decides, which is about 70 % of tasks,
it only costs time.

### B1 – the TA workers slow k-induction down; where the z3 processes come from
Same task, same final k:
- U is 1.6× slower than k-induction alone, and T 1.9×. T/U is 1.12–1.20 at every size.
- 73 of T's 208 lost tasks are k-induction tasks where T's k-induction did not get as far before the timeout.

**Correction:** the "8 z3 for T, 5 for U" from earlier counted processes *started* per run. Running at the same time
(sample of 300 runs per configuration, last toolchain):

| | U | T |
|---|---|---|
| median | 5 | 6 |
| p90 | 6 | 8 |
| max | 9 | 10 |

What is running in T (from `Constructing external solver` and `Starting monitored process`, by creator):

| # | Process | Created by | Lifetime |
|---|---|---|---|
| 1 | main, IcfgBuilder script `-t:4000` | IcfgBuilder | whole run |
| 1 | invariant supplier script | `TransferBetweenMainAndWorker` in `setUpWorkerThreads` (`ParallelNwaCegarLoop.java:797`) | whole run |
| 2 | TA worker scripts `-t:4000`, one per worker | `ParallelNwaCegarLoop.java:909` → `CfgSmtToolkit.createFreshManagedScript` (`TransferBetweenMainAndWorker.java:141`) | whole run |
| 1 | k-induction `-t:3600000` / `bitwuzla --time-limit-per` | `ParallelNwaCegarLoop.java:909` | whole run |
| 1 | **value analysis script** | the same | **whole run**, although the value analysis stops after ≤ 20 s and needs a solver only for its one confirming trace check |
| 0–2 per TA worker | **strategy solvers** of every trace check (z3, then mathsat or bitwuzla, after `AssertionOrderModulation`) | `TaskScopedServices` per task (`CegarNwaWorkerThread.java:237,272`) | started for each task, destroyed only at its end |

On the strategy solvers: about 7.5 are started per T run. Each start replays the declarations, and a worker keeps up
to 2 of them alive at once (z3 + mathsat) until its task ends.

Compared with what the user expects (2 per TA worker, 1 main, 2 for k-induction counting the supplier, so 7 for T),
there is one too many all the time and up to two too many at the peak:
- **The value analysis z3 is never closed**, which is the +1 for the whole run. No worker closes its own script when
  it stops: there is no `exit`/destroy of the worker script in `parallel/`, only `TaskScopedServices.destroyAll` for
  the task solvers. The scripts of retired or crashed TA workers and of the supplier also stay alive until the
  toolchain ends.
- **A worker keeps several strategy solvers alive in one task**, because they are only destroyed at the end of the
  task.
- New processes are started for every task, instead of one trace-check solver per worker that is reused with
  `push`/`pop` or `reset`.

### B5 – the main thread works serially and dispatches too much
- `dispatchLimit()` = TA + KI (`ParallelNwaCegarLoop.java:223,705`). The loop at `:350-361` keeps searching until
  that many counterexamples are out, so with 2 TA workers 3 are out at once and one of them always waits in the
  queue. When a worker takes it, the abstraction has already changed. Each extra search is also another
  `IsEmptyParallel` on the main thread.
- `handleWorkerResults` (`:372-483`) refines with each result one after another (`refinement` → difference →
  minimization, because `minimizeAbstractionPerWorker` = true) and checks emptiness (`isSafeThenTerminate`) after
  every single result.
- Each worker also computes its own "Difference in Worker for Generalization", and keeps an old copy of the
  abstraction (`CegarNwaWorkerThread.java:410-419`).

## Plan (one phase at a time, re-benchmark after each)
Decided with the user: every TA worker starts right away. Startup and shutdown cost, memory, and the integer →
bit-precise rerun stay as they are.

### Phase 1 – close solvers of workers that stopped (B1)
Decided with the user: only these two changes; the strategy solvers stay as they are.
- **Value analysis:** close its solver as soon as the worker ends: when it retires, when it reaches its time limit
  with UNKNOWN, and after its confirming trace check (`valueanalysis/ValueAnalysisWorkerThread`, the end of its
  `call`, in a `finally`).
- **Terminate the worker scripts:** when a worker stops (a TA worker retires, crashes or finishes without a verdict,
  the supplier stops or crashes, k-induction ends), close its worker script.
  - Add `close()` to `TransferBetweenMainAndWorker`: `mWorkerScript.getScript().exit()` and removing it from the
    storage.
  - Each worker calls it in its `finally`, and `shutDownAndDestroy`/`finish()` closes the remaining ones.
  - Make sure that nothing touches a worker script after it is closed. The terms of a TA result are already
    transferred to the main script (`ParallelNwaCegarLoop.java:1080`). k-induction's proof invariants are transferred
    from the worker script only in `kInductionAnnotation` (`transferTerm(..., workerResult.getWorkerMgdScript())`,
    `:760`), so k-induction's script may only be closed after that.
- Measure with `tools/z3conc.py` (a sample from the logs): after the value analysis or a retired TA worker stops,
  there is one z3 fewer.

### Phase 2 – scheduling in `ParallelNwaCegarLoop` (B5)
The loop the user wants:
1. Search for a counterexample **only if a TA worker is idle**. No new counter is needed: once `dispatchLimit()` is
   fixed, "`mRunningThreads < dispatchLimit()`" means exactly that a TA worker is idle.
2. **`mWorkerTaskQueue` stays the hand-off, but a task in it is taken right away**, because there is only one when a
   worker is idle. If all workers are busy, the queue is empty.
3. **When workers finish, refine with all results first, then search.** That is already the case:
   `handleWorkerResults` (`:372-483`) polls the result queue until it is empty before the search loop (`:350`) runs.
   No change; only make sure the fix of 1 and 2 does not change it.

**The existing counters, checked: k-induction does count towards the limit (bug).**
- `mRunningThreads` counts the counterexamples that went to TA workers and are not refined yet, queued or in work.
  Correct: it goes up only in `startWorker()` (`:1016`) and down in `refinement()` (`:1092`), on a TA crash (`:603`),
  and on a TA retirement during a trace check (`:639`). k-induction never changes it.
- `mThreadLimit = mNumTaWorkers + mNumKInductionWorkers` (`:223`) is the size of the pool and the number of workers
  that can retire (`mRetiredWorkers >= mThreadLimit`, `:419,619,647`). Both uses are fine.
- **Bug:** `dispatchLimit() = mThreadLimit - mGoneTaWorkers` (`:705`) also counts the k-induction worker. The search
  loop (`:350`) and `getWorkerResult` (`:1027`) therefore let one counterexample more out than there are TA workers.
  Confirmed in the logs: `ActiveThreads` (= max of `mRunningThreads`) was 2 in 199 of 200 U runs with one TA worker,
  and 3 in 195 of 200 T runs with two. One counterexample has always been waiting in the queue.
- The statistic `IterationsWithMaxThreads` (`:961`, `mRunningThreads == mThreadLimit`) has the same mistake.
- Smaller holes:
  - A TA crash always takes off one of `mRunningThreads` (`:603`), even if the worker crashed while waiting for a
    task.
  - A TA worker that retires while waiting (`counterexample == null`, `:637-642`) leaves a counterexample in
    `mWorkerTaskQueue` that it never takes. With 1 TA worker that counterexample is lost and still counts in
    `mRunningThreads`.

Changes:
- `dispatchLimit()` → `mNumTaWorkers - mGoneTaWorkers`, without the k-induction slot. Fix `IterationsWithMaxThreads`
  the same way. `mThreadLimit` stays for the pool size and for counting retired workers.
- A TA crash only decrements `mRunningThreads` if the crashed worker had a task: carry the counterexample in
  `WorkerThreadResult.crashed`, as `retired` already does. When a TA worker retires while waiting, the main thread
  takes back a task left in `mWorkerTaskQueue` (`poll`, decrement `mRunningThreads`, remove it from
  `mActiveCounterexamples`).
- `getWorkerResult` (`:1023`) and the search loop (`:350-361`) stay as they are. With the fixed `dispatchLimit()`,
  they block or search exactly when no TA worker or one TA worker is idle.
- Check in the log: `ActiveThreads` must be ≤ the number of TA workers, i.e. 1 in U and 2 in T. Between `Main:
  Starting Thread` and the matching `Starting Thread: <id># for Trace Check: <hash>` of a worker there must be (almost)
  no time.

Crashes that hit both configurations (outside this scope, listed for completeness):
- TA `ArrayIndexOutOfBoundsException` (16 in T, 32 in U)
- `Function c_aux_v_#memory_* is already defined` (about 20)
- k-induction "Inconsistent sorts" (27 / 26)
- invariant supplier External MP exception (92 / 142)

## Verification
- Build and run with the `ultimate-build-test` skill. Smoke-test that one example run gives the right verdict for
  each phase: a safe program decided by TA, a safe program decided by k-induction, and an unsafe program. Check the
  log for the closed scripts ("Ended with exit code" right after the worker stops) and for the new scheduling line.
- Benchmark U against new T on `releaseScripts/default/benchexec/uautomizer-svcomp-2027-middle.xml`, locally with
  TIMEOUT=600 (memory: sweep timeout). Then do a full cluster run.
- Analyze with the scan scripts from this session. Copy them into the repo or paper folder first; the scratchpad is
  not permanent: `/tmp/claude-1000/-home-max-Documents-GIT-ultimate-fork-ultimate-kiduction-nocex-witness/4b8145b4-3e2b-44c5-ab3d-04e90cddc2f0/scratchpad/tools/{partialzip,scan,an,z3conc}.py`.
- Success criteria:
  - T/U geometric mean wall < 1.0 overall and ≤ 1.0 in every bucket
  - T faster on more tasks than slower
  - no z3 of a stopped worker remains alive
  - solved tasks ≥ the current 11,545
  - no new wrong results
- Save this plan as `plans/two-ta-workers-bottlenecks.md` in the repo (memory: persist plans).
- Commits for performance work start with "Optimization".
