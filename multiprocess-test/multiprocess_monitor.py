#!/usr/bin/env python3
"""Observe an Ultimate multiprocess exchange directory and log scheduling health."""

from __future__ import annotations

import argparse
import json
import logging
import time
from pathlib import Path


class MultiprocessMonitor:
    def __init__(self, exchange: Path, logger: logging.Logger) -> None:
        self.exchange = exchange
        self.log = logger
        self.coordinator_version: int | None = None
        self.worker_versions: dict[str, int] = {}
        self.pid_to_worker: dict[int, str] = {}
        self.requests: dict[str, dict] = {}
        self.active: dict[str, dict] = {}
        self.completed: set[str] = set()
        self.reported_assignments: set[str] = set()
        self.claimed_jobs: set[str] = set()
        self.reported_lag: set[tuple[str, int, int]] = set()

    @staticmethod
    def _read_json(path: Path) -> dict | None:
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return None

    def _warn_lag(self, worker: str) -> None:
        worker_version = self.worker_versions.get(worker)
        if self.coordinator_version is None or worker_version is None:
            return
        lag = self.coordinator_version - worker_version
        key = (worker, worker_version, self.coordinator_version)
        if lag > 0 and key not in self.reported_lag:
            self.reported_lag.add(key)
            self.log.warning(
                "Worker %s abstraction version %d is %d version(s) behind coordinator version %d",
                worker, worker_version, lag, self.coordinator_version,
            )

    def _read_statuses(self) -> None:
        coordinator = self._read_json(self.exchange / "coordinator-status.json")
        if coordinator is not None:
            version = int(coordinator["abstractionGeneration"])
            if version != self.coordinator_version:
                self.coordinator_version = version
                self.log.info("Coordinator abstraction version changed to %d", version)
                for worker in self.worker_versions:
                    self._warn_lag(worker)

        for path in sorted(self.exchange.glob("worker-status-*.json")):
            status = self._read_json(path)
            if status is None:
                continue
            worker = str(status["workerId"])
            pid = int(status["pid"])
            version = int(status["installedAbstractionGeneration"])
            self.pid_to_worker[pid] = worker
            if self.worker_versions.get(worker) != version:
                self.worker_versions[worker] = version
                self.log.info("Worker %s (pid=%d) abstraction version changed to %d", worker, pid, version)
                self._warn_lag(worker)

    def _read_requests(self) -> None:
        for path in sorted(self.exchange.glob("request-*.json")):
            if path.name.endswith(".tmp"):
                continue
            job = path.name[len("request-"):-len(".json")]
            if job not in self.requests:
                request = self._read_json(path)
                if request is not None:
                    self.requests[job] = request

    def _read_assignments(self) -> None:
        for claim in sorted(self.exchange.glob("request-*.json.claim")):
            job = claim.name[len("request-"):-len(".json.claim")]
            self.claimed_jobs.add(job)
            if job in self.reported_assignments or job not in self.requests:
                continue
            try:
                pid = int(claim.read_text(encoding="utf-8").strip())
            except (OSError, ValueError):
                continue
            worker = self.pid_to_worker.get(pid)
            if worker is None:
                continue
            request = self.requests[job]
            path_hash = str(request["pathProgramHash"])
            assignment = {"worker": worker, "pid": pid, "pathProgramHash": path_hash}
            self.active[job] = assignment
            self.reported_assignments.add(job)
            workers_on_path = [x["worker"] for x in self.active.values()
                               if x["pathProgramHash"] == path_hash]
            worker_version = self.worker_versions.get(worker, -1)
            coordinator_version = self.coordinator_version
            lag = -1 if coordinator_version is None else coordinator_version - worker_version
            self.log.info(
                "Assigned worker=%s pid=%d job=%s pathProgramHash=%s pathProgramCount=%s "
                "workerVersion=%d coordinatorVersion=%s lag=%s activeOnPath=%d",
                worker, pid, job, path_hash, request.get("pathProgramCount"), worker_version,
                coordinator_version, lag, len(workers_on_path),
            )
            self._warn_lag(worker)
            # If polling discovered both claim and result together, complete this job before considering a later
            # assignment. A sequential worker must not appear to work on two jobs at once merely due to polling order.
            if (self.exchange / f"result-{job}.json").is_file():
                self._complete_job(job)

    def _complete_job(self, job: str) -> None:
        if job in self.completed or job not in self.reported_assignments:
            return
        assignment = self.active.pop(job, None)
        self.completed.add(job)
        if assignment is None:
            return
        path_hash = assignment["pathProgramHash"]
        remaining = sorted({x["worker"] for x in self.active.values()
                            if x["pathProgramHash"] == path_hash
                            and x["worker"] != assignment["worker"]})
        self.log.info("Worker %s completed job=%s pathProgramHash=%s",
                      assignment["worker"], job, path_hash)
        if remaining:
            self.log.warning(
                "Worker %s provided result for pathProgramHash=%s while %d other worker(s) "
                "still work on the same path program: %s",
                assignment["worker"], path_hash, len(remaining), ", ".join(remaining),
            )

    def _read_results(self) -> None:
        for result in sorted(self.exchange.glob("result-*.json")):
            if result.name.endswith(".tmp"):
                continue
            job = result.name[len("result-"):-len(".json")]
            self._complete_job(job)

        for cancellation in sorted(self.exchange.glob("cancel-*.json")):
            if cancellation.name.endswith(".tmp"):
                continue
            job = cancellation.name[len("cancel-"):-len(".json")]
            self._complete_job(job)

    def poll(self) -> bool:
        self._read_statuses()
        self._read_requests()
        self._read_assignments()
        self._read_results()
        shutdown = (self.exchange / "shutdown").is_file()
        completed_on_disk = {
            path.name[len("result-"):-len(".json")]
            for path in self.exchange.glob("result-*.json") if not path.name.endswith(".tmp")
        }
        completed_on_disk.update(
            path.name[len("cancel-"):-len(".json")]
            for path in self.exchange.glob("cancel-*.json") if not path.name.endswith(".tmp")
        )
        return shutdown and self.claimed_jobs.issubset(completed_on_disk)

    def run(self, interval: float) -> None:
        self.exchange.mkdir(parents=True, exist_ok=True)
        self.log.info("Monitoring exchange directory %s", self.exchange)
        while not self.poll():
            time.sleep(interval)
        self.log.info("Coordinator shut down and all claimed jobs are terminal; monitor exiting")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--exchange", required=True, type=Path)
    parser.add_argument("--log", required=True, type=Path)
    parser.add_argument("--interval", type=float, default=0.1)
    args = parser.parse_args()
    args.log.parent.mkdir(parents=True, exist_ok=True)
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(message)s",
        handlers=[logging.FileHandler(args.log, encoding="utf-8")],
    )
    MultiprocessMonitor(args.exchange.resolve(), logging.getLogger("multiprocess-monitor")).run(args.interval)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
