# Running Ultimate with multiprocessing

Ultimate's multiprocessing mode runs one TraceAbstraction **coordinator** and several persistent **workers**. The coordinator performs the authoritative CEGAR analysis and publishes jobs through a filesystem exchange directory. Workers claim those jobs, compute results in parallel, and return them to the coordinator. The launcher in this directory creates isolated process data directories, starts a live monitor, stops the complete campaign when the coordinator finishes, and checks the resulting exchange artifacts.

This guide describes the supported Windows workflow using Git Bash. Commands below assume that the checkout is located at:

```text
C:\Users\maxba\Documents\GIT\ultimate-fork\ultimate
```

## Prerequisites

Install or provide:

- 64-bit Windows and Git for Windows (including Git Bash).
- Java 21. The commands below use `C:\Program Files\Eclipse Adoptium\jdk-21.0.11.10-hotspot`.
- Maven 3.9.x. The commands below use `C:\tools\apache-maven-3.9.16`.
- Python 3. The repository's `multiprocess-test/bin/python3` shim is used by the launcher on this machine.
- Enough memory for one coordinator, the requested workers, and their solver processes. Eight workers are the tested default.

Every coordinator and worker must use the same C program, property, architecture, Ultimate distribution, and exchange directory. Each process must have its own Eclipse `--data` directory; the launcher handles this automatically.

## Build and run

### 1. Open Git Bash and enter the checkout

```bash
cd /c/Users/maxba/Documents/GIT/ultimate-fork/ultimate
```

### 2. Select one input and one property

The included examples are under `multiprocess-test/examples`. For example:

```bash
PROGRAM=/c/Users/maxba/Documents/GIT/ultimate-fork/ultimate/multiprocess-test/examples/svcomp-eca-rers2012/Problem03_label45.c
PROPERTY=/c/Users/maxba/Documents/GIT/ultimate-fork/ultimate/multiprocess-test/examples/svcomp-eca-rers2012/unreach-call.prp
```

To use another benchmark, replace these with absolute paths to its `.c` and `.prp` files. Do not select an expected verdict based only on a filename or witness filename.

### 3. Configure Java and Maven

```bash
export JAVA_HOME='/c/Program Files/Eclipse Adoptium/jdk-21.0.11.10-hotspot'
export PATH="$JAVA_HOME/bin:/c/tools/apache-maven-3.9.16/bin:$PATH"
java -version
mvn -version
```

Both commands should report Java 21.

### 4. Test the monitor

```bash
cd /c/Users/maxba/Documents/GIT/ultimate-fork/ultimate/multiprocess-test
python3 -m unittest -v test_multiprocess_monitor.py
```

All monitor tests must pass before relying on a campaign report.

### 5. Build Ultimate

Compile the full Maven reactor:

```bash
cd /c/Users/maxba/Documents/GIT/ultimate-fork/ultimate/trunk/source/BA_MavenParentUltimate
mvn -DskipTests package
```

For a runnable distribution, materialize the current build and package Automizer:

```bash
mvn -T 1C install -Pmaterialize -DskipTests
cd /c/Users/maxba/Documents/GIT/ultimate-fork/ultimate/releaseScripts/default
./makeZip.sh Automizer win32 \
  AutomizerCInline_WitnessPrinter.xml \
  BuchiAutomizerCInline_WitnessPrinter.xml \
  AutomizerCInline.xml \
  AutomizerCInline_WitnessPrinter.xml \
  LTLAutomizerC.xml \
  BuchiAutomizerCInline.xml
```

The runnable distribution is then:

```text
C:\Users\maxba\Documents\GIT\ultimate-fork\ultimate\releaseScripts\default\UAutomizer-win32
```

Rebuild and repackage whenever the TraceAbstraction Java sources have changed. A stale distribution silently tests old code.

### 6. Choose a unique run name

```bash
cd /c/Users/maxba/Documents/GIT/ultimate-fork/ultimate/multiprocess-test
RUN_NAME="$(basename "$PROGRAM" .c)-$(date +%Y%m%d-%H%M%S)"
RUN_ROOT=/c/Users/maxba/Documents/GIT/ultimate-fork/ultimate/multiprocess-test/runs
```

Never reuse a run name. The launcher refuses to overwrite an existing run directory.

### 7. Start the campaign

```bash
PATH="$PWD/bin:$PATH" ./run-multiprocess.sh \
  --ultimate-dir /c/Users/maxba/Documents/GIT/ultimate-fork/ultimate/releaseScripts/default/UAutomizer-win32 \
  --file "$PROGRAM" \
  --spec "$PROPERTY" \
  --workers 8 \
  --architecture 32bit \
  --run-root "$RUN_ROOT" \
  --name "$RUN_NAME" \
  --timeout 600 \
  --job-timeout 600
```

The launcher starts the monitor, then the workers, and finally the coordinator. Keep the terminal open until it prints `PASS` or `FAIL`. A nonzero exit status means the artifact checks or a process failed; it does not by itself change an emitted SAFE/UNSAFE verdict.

To see all launcher options:

```bash
./run-multiprocess.sh --help
```

## Check that multiprocessing is running

Open a second Git Bash terminal while the campaign is active and set the same run variables:

```bash
cd /c/Users/maxba/Documents/GIT/ultimate-fork/ultimate/multiprocess-test
RUN_NAME='<the name printed by the launcher>'
RUN_ROOT=/c/Users/maxba/Documents/GIT/ultimate-fork/ultimate/multiprocess-test/runs
RUN="$RUN_ROOT/$RUN_NAME"
```

The launcher prints `Starting 8 workers...` and `Starting coordinator...`. Confirm live operating-system processes with:

```bash
tasklist.exe | grep -Ei 'java|python|z3'
```

Confirm that all worker logs exist:

```bash
ls -l "$RUN"/logs/worker-*.log "$RUN"/logs/coordinator.log "$RUN"/logs/monitor.log
```

Follow the scheduling monitor live:

```bash
tail -f "$RUN/logs/monitor.log"
```

Healthy multiprocessing produces lines such as:

- `Assigned worker=worker-N ...` for multiple worker IDs.
- `Worker worker-N completed job=...`.
- `Coordinator abstraction version changed to ...`.

Seeing several worker IDs proves participation. Strong evidence of actual parallelism is that assignments to different workers overlap in time; sequential participation alone is not proof of parallel execution.

You can also watch exchange artifacts appear:

```bash
watch -n 1 'find "'"$RUN"'/exchange/worker-0" -maxdepth 1 -type f | sed "s/.*\///" | sort | tail -30'
```

When the coordinator has a final result, it writes `shutdown`. The workers and monitor should then terminate:

```bash
test -f "$RUN/exchange/worker-0/shutdown" && echo 'shutdown requested'
```

## Check the result

### Read the authoritative verdict

The coordinator log is the source of the verification verdict:

```bash
grep -A2 '^Result:$' "$RUN/logs/coordinator.log" | tail -2
grep '^RESULT:' "$RUN/logs/coordinator.log" | tail -1
```

Common CLI results are:

- `TRUE`: the analyzed property was proved; normally reported as SAFE.
- `FALSE`: a violation was found; normally reported as UNSAFE.
- `UNKNOWN`: Ultimate could not establish either result.

If an outer watchdog created a `timeout` marker, report the campaign as `TIMEOUT` even if a partial coordinator verdict is present.

### Read the launcher's summary

At the end of the run, `run-multiprocess.sh` prints a summary similar to:

```text
requests=176 claims=163 results=163 cancellations=11 terminals=174 distinct-claimants=8
PASS: coordinator and all workers terminated cleanly
```

`PASS` means the launcher's process and exchange checks passed. `FAIL` means the logs and exchange directory need inspection. It is possible to have a valid coordinator verdict and still receive `FAIL`, for example if a worker crashed or a claimed job has no terminal result/cancellation.

To reproduce the main counts after a run:

```bash
INBOX="$RUN/exchange/worker-0"
printf 'requests=%s claims=%s results=%s cancellations=%s workers=%s\n' \
  "$(find "$INBOX" -maxdepth 1 -name 'request-*.json' | wc -l)" \
  "$(find "$INBOX" -maxdepth 1 -name 'request-*.json.claim' | wc -l)" \
  "$(find "$INBOX" -maxdepth 1 -name 'result-*.json' | wc -l)" \
  "$(find "$INBOX" -maxdepth 1 -name 'cancel-*.json' | wc -l)" \
  "$(find "$INBOX" -maxdepth 1 -name 'worker-status-*.json' | wc -l)"
```

Check final shutdown and status artifacts:

```bash
ls -l "$INBOX/shutdown" "$INBOX/coordinator-status.json" "$INBOX"/worker-status-*.json
tail -30 "$RUN/logs/monitor.log"
grep -Ei 'exception|fatal|error|timed out|failed' "$RUN"/logs/*.log
```

The last `grep` is intentionally broad. Inspect matches in context: generic Ultimate warnings are not necessarily multiprocessing failures.

### Generate a Markdown report

If `analyze_multiprocess_run.py` from the `test-ultimate-multiprocessing` tooling is installed on this machine, run:

```bash
python3 /c/Users/maxba/Documents/MutliProcessing/skills/test-ultimate-multiprocessing/scripts/analyze_multiprocess_run.py \
  --run "$RUN" \
  --workers 8 \
  --expected-verdict ANY \
  --output "$RUN/multiprocessing-report.md"
```

Then open:

```text
<run directory>\multiprocessing-report.md
```

The report summarizes the verdict, request/claim/result integrity, worker participation, overlapping work, abstraction lag, contention, failures, warnings, shutdown state, and evidence paths. Use `--expected-verdict SAFE` or `UNSAFE` only when that expectation comes from authoritative benchmark metadata; otherwise keep `ANY`.

## Folder structure

```text
multiprocess-test/
|-- README.md
|-- COMMANDS.md
|-- run-multiprocess.sh
|-- multiprocess_monitor.py
|-- test_multiprocess_monitor.py
|-- test_run_multiprocess_launcher.py
|-- run-worker.cmd
|-- run-coordinator.cmd
|-- run-verification.sh
|-- bin/
|   `-- python3
|-- examples/
|   |-- safe.c, unsafe.c, reach.prp
|   `-- svcomp-eca-rers2012/
|-- runs/
|   `-- <unique run name>/
|       |-- campaign-status.json       (when run through the watchdog wrapper)
|       |-- multiprocessing-report.md  (after running the analyzer)
|       |-- timeout                    (only when the outer watchdog expires)
|       |-- logs/
|       |-- exchange/worker-0/
|       |-- coordinator-data/
|       `-- worker-0/ ... worker-N/
|-- Problem03_label45-monitor-test/
`-- Problem18_label42-monitor-test/
```

### Top-level files and directories

- `README.md`: this human-oriented end-to-end guide.
- `COMMANDS.md`: older, compact command examples. Prefer this README and `run-multiprocess.sh` for normal multi-worker runs.
- `run-multiprocess.sh`: primary launcher. It creates an isolated run, starts the monitor/workers/coordinator, performs bounded shutdown, and validates artifacts.
- `multiprocess_monitor.py`: observes the exchange directory and records worker assignments, completions, abstraction versions, lag, contention, and shutdown.
- `test_multiprocess_monitor.py`: filesystem-based unit tests for monitor/protocol behavior.
- `test_run_multiprocess_launcher.py`: regression tests for launcher shutdown and process-tree handling.
- `run-worker.cmd` and `run-coordinator.cmd`: manual one-worker Windows launchers for debugging in separate terminals. They are not the recommended eight-worker workflow.
- `run-verification.sh`: legacy small example matrix using one worker. It is useful for basic verification, not for demonstrating substantial concurrency.
- `bin/python3`: local Git Bash shim that lets the launcher find the configured Python runtime.
- `examples/`: sample C programs, `.prp` properties, and witness files. Witness files are supporting artifacts, not a reason to assume an expected verdict.
- `runs/`: recommended parent directory for all new, uniquely named campaigns.
- `Problem03_label45-monitor-test/` and `Problem18_label42-monitor-test/`: older saved monitor-test artifacts. They are evidence/debug data, not launcher code and not templates for new runs.
- `__pycache__/`: generated Python bytecode cache; it contains no campaign evidence.

### Inside a run directory

- `logs/coordinator.log`: authoritative coordinator output, final verdict, counterexample/statistics, and coordinator errors.
- `logs/worker-N.log`: complete output for worker `N`; inspect these for worker startup, job failures, solver failures, and shutdown behavior.
- `logs/monitor.log`: concise scheduling timeline. This is the best place to check worker participation, overlapping assignments, abstraction generation/lag, contention, and orderly monitor shutdown.
- `logs/launcher.stdout.log` and `logs/launcher.stderr.log`: present when a wrapper captures the launcher's terminal streams.
- `exchange/worker-0/`: shared filesystem protocol. Despite its name, all workers and the coordinator use this same inbox.
- `coordinator-data/`: private Eclipse/RCP workspace for the coordinator.
- `worker-N/data/`: private Eclipse/RCP workspace for worker `N`. Never point two processes at the same data directory.
- `campaign-status.json`: wrapper metadata including inputs, times, worker count, build identity, watchdog status, exit codes, and residual scoped processes.
- `multiprocessing-report.md`: generated human-readable diagnostic report.
- `timeout`: authoritative marker that the fixed outer watchdog expired.

### Inside `exchange/worker-0`

- `request-NNNNNNNN.json`: job published by the coordinator.
- `request-NNNNNNNN.json.claim`: atomic worker claim. Its content identifies the claiming process.
- `result-NNNNNNNN.json`: completed worker result.
- `cancel-NNNNNNNN.json`: terminal cancellation for work that no longer needs a result.
- `automaton-NNNNNNNN.ats`: ATS produced for a corresponding UNSAT worker result.
- `abstractions.ats`: current coordinator abstraction shared with workers.
- `coordinator-status.json`: coordinator PID and current abstraction generation.
- `worker-status-worker-N.json`: worker identity, PID, and installed abstraction generation.
- `shutdown`: coordinator's terminal signal. Once present, workers must stop claiming new work and terminate.
- `*.tmp`: temporary files used for atomic publication. Persistent temporary files after completion may indicate an interrupted write and should be investigated.

For most investigations, start with `logs/coordinator.log`, `logs/monitor.log`, and `exchange/worker-0`, then inspect individual `logs/worker-N.log` files when the summary reports a failure.
