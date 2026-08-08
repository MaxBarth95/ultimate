import json
import logging
import tempfile
import unittest
from pathlib import Path

from multiprocess_monitor import MultiprocessMonitor


class ListHandler(logging.Handler):
    def __init__(self):
        super().__init__()
        self.messages = []

    def emit(self, record):
        self.messages.append(record.getMessage())


class MonitorTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.exchange = Path(self.temp.name)
        self.handler = ListHandler()
        self.logger = logging.getLogger(self.id())
        self.logger.setLevel(logging.INFO)
        self.logger.handlers = [self.handler]
        self.monitor = MultiprocessMonitor(self.exchange, self.logger)

    def tearDown(self):
        self.temp.cleanup()

    def write_json(self, name, value):
        (self.exchange / name).write_text(json.dumps(value), encoding="utf-8")

    def status(self, worker, pid, version):
        self.write_json(f"worker-status-{worker}.json", {
            "workerId": worker, "pid": pid, "installedAbstractionGeneration": version,
            "state": "WORKING", "jobId": None, "pathProgramHash": None,
        })

    def request(self, job, path_hash="42", count=1, generation=3):
        self.write_json(f"request-{job}.json", {
            "pathProgramHash": path_hash, "pathProgramCount": count,
            "abstractionGeneration": generation, "symbols": [],
        })

    def claim(self, job, pid):
        (self.exchange / f"request-{job}.json.claim").write_text(str(pid), encoding="utf-8")

    def test_contention_lag_completion_and_deduplication(self):
        self.write_json("coordinator-status.json", {"abstractionGeneration": 3})
        self.status("worker-0", 10, 3)
        self.status("worker-1", 11, 1)
        self.request("00000000", count=4)
        self.request("00000001", count=5)
        self.claim("00000000", 10)
        self.claim("00000001", 11)
        self.assertFalse(self.monitor.poll())
        self.assertFalse(self.monitor.poll())
        messages = "\n".join(self.handler.messages)
        self.assertIn("activeOnPath=2", messages)
        self.assertIn("2 version(s) behind", messages)
        self.assertEqual(messages.count("Assigned worker="), 2)

        self.write_json("result-00000000.json", {"outcome": "UNSAT"})
        self.monitor.poll()
        messages = "\n".join(self.handler.messages)
        self.assertIn("1 other worker(s)", messages)
        self.assertIn("worker-1", messages)

    def test_out_of_order_claim_waits_for_worker_identity_and_shutdown(self):
        self.request("00000000")
        self.claim("00000000", 20)
        self.monitor.poll()
        self.assertFalse(any("Assigned" in x for x in self.handler.messages))
        self.status("worker-0", 20, 0)
        self.monitor.poll()
        self.assertTrue(any("Assigned worker=worker-0" in x for x in self.handler.messages))
        self.write_json("result-00000000.json", {"outcome": "SAT"})
        (self.exchange / "shutdown").write_text("done", encoding="utf-8")
        self.assertTrue(self.monitor.poll())

    def test_worker_version_change_recomputes_lag(self):
        self.write_json("coordinator-status.json", {"abstractionGeneration": 4})
        self.status("worker-0", 10, 1)
        self.monitor.poll()
        self.status("worker-0", 10, 4)
        self.monitor.poll()
        messages = "\n".join(self.handler.messages)
        self.assertIn("3 version(s) behind", messages)
        self.assertIn("version changed to 4", messages)

    def test_shutdown_waits_for_claim_even_before_worker_status(self):
        self.request("00000000")
        self.claim("00000000", 99)
        (self.exchange / "shutdown").write_text("done", encoding="utf-8")
        self.assertFalse(self.monitor.poll())
        self.write_json("result-00000000.json", {"outcome": "ERROR"})
        self.assertTrue(self.monitor.poll())

    def test_cancellation_is_terminal_for_claimed_job(self):
        self.request("00000000", path_hash="hash-a")
        self.claim("00000000", 99)
        self.write_json("cancel-00000000.json", {"jobId": "00000000"})
        (self.exchange / "shutdown").write_text("done", encoding="utf-8")
        self.assertTrue(self.monitor.poll())

    def test_completed_sequential_jobs_do_not_report_same_worker_as_other(self):
        self.status("worker-0", 10, 0)
        for job in ("00000000", "00000001"):
            self.request(job, path_hash="42")
            self.claim(job, 10)
            self.write_json(f"result-{job}.json", {"outcome": "UNSAT"})
        self.monitor.poll()
        self.assertFalse(any("other worker" in x for x in self.handler.messages))


if __name__ == "__main__":
    unittest.main()
