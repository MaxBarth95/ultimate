# Multiprocess test commands

The coordinator and worker must use the same input program, property, architecture, and exchange root. They use
separate RCP data directories so two Ultimate processes never share an Eclipse workspace.

On Windows, start the persistent worker in one terminal and the coordinator in another:

```bat
run-worker.cmd examples\safe.c runtime
run-coordinator.cmd examples\safe.c runtime
```

Build and run the complete verification matrix from Git Bash:

```sh
cd /c/Users/maxba/Documents/GIT/ultimate/releaseScripts/default
./makeFresh.sh

cd /c/Users/maxba/Documents/GIT/ultimate/trunk/multiprocess-test
ULTIMATE_DIR=/c/Users/maxba/Documents/GIT/ultimate/releaseScripts/default/UAutomizer-win32 \
	./run-verification.sh
```

Worker:

```sh
./Ultimate.py --file safe.c --spec reach.prp --architecture 32bit \
  --data worker-data \
  --traceabstraction.multi.process.component WORKER \
  --traceabstraction.multi.process.exchange.root exchange/worker-0
```

Coordinator:

```sh
./Ultimate.py --file safe.c --spec reach.prp --architecture 32bit \
  --data coordinator-data \
  --traceabstraction.multi.process.component COORDINATOR \
  --traceabstraction.multi.process.exchange.root exchange/worker-0 \
  --traceabstraction.multi.process.worker.count 1
```
