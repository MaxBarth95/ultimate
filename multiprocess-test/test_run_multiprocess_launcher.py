import os
import shlex
import shutil
import subprocess
import tempfile
import textwrap
import time
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent
GIT_BASH = Path(r"C:\Program Files\Git\bin\bash.exe")


def bash_path(path):
    value = str(Path(path).resolve()).replace("\\", "/")
    return "/" + value[0].lower() + value[2:]


class LauncherShutdownTest(unittest.TestCase):
    @unittest.skipUnless(os.environ.get("ULTIMATE_RUN_PROCESS_TESTS") == "1",
                         "set ULTIMATE_RUN_PROCESS_TESTS=1 where Git Bash may create processes")
    def test_hung_taskkill_and_worker_are_bounded(self):
        if not GIT_BASH.is_file():
            self.skipTest("Git Bash is unavailable")
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            root = Path(temporary)
            harness = root / "harness"
            distribution = root / "distribution"
            fake_bin = root / "fake-bin"
            harness.mkdir()
            distribution.mkdir()
            fake_bin.mkdir()
            shutil.copy2(ROOT / "run-multiprocess.sh", harness / "run-multiprocess.sh")
            shutil.copy2(ROOT / "multiprocess_monitor.py", harness / "multiprocess_monitor.py")
            program = root / "input.c"
            prop = root / "property.prp"
            program.write_text("int main(void) { return 0; }\n", encoding="utf-8")
            prop.write_text("CHECK( init(main()), LTL(G ! call(reach_error())) )\n", encoding="utf-8")
            (distribution / "Ultimate.py").write_text(
                textwrap.dedent(
                    """\
                    #!/usr/bin/env python3
                    import json, os, sys, time
                    from pathlib import Path
                    args = sys.argv[1:]
                    def value(flag): return args[args.index(flag) + 1]
                    inbox = Path(value('--traceabstraction.multi.process.exchange.root'))
                    inbox.mkdir(parents=True, exist_ok=True)
                    role = value('--traceabstraction.multi.process.component')
                    if role == 'COORDINATOR':
                        (inbox / 'coordinator-status.json').write_text('{"abstractionGeneration": 0}')
                        (inbox / 'shutdown').write_text('done')
                        print('Result:\\nFALSE')
                    else:
                        worker = value('--traceabstraction.multi.process.worker.id')
                        status = {'workerId': worker, 'pid': os.getpid(),
                                  'installedAbstractionGeneration': 0, 'state': 'WORKING',
                                  'jobId': None, 'pathProgramHash': None}
                        (inbox / ('worker-status-' + worker + '.json')).write_text(json.dumps(status))
                        time.sleep(60)
                    """
                ),
                encoding="utf-8",
            )
            (fake_bin / "taskkill.exe").write_text("#!/usr/bin/env bash\nsleep 60\n", encoding="utf-8")
            for executable in (harness / "run-multiprocess.sh", distribution / "Ultimate.py",
                               fake_bin / "taskkill.exe"):
                executable.chmod(0o755)
            env = os.environ.copy()
            relative_root = root.relative_to(ROOT)
            env["PATH"] = ":".join((bash_path(fake_bin), bash_path(ROOT / "bin"), "/usr/bin", "/bin"))
            env["MULTIPROCESS_SHUTDOWN_GRACE_SECONDS"] = "1"
            env["MULTIPROCESS_KILL_GRACE_SECONDS"] = "1"
            launcher_command = [
                (relative_root / "harness" / "run-multiprocess.sh").as_posix(),
                "--ultimate-dir", (relative_root / "distribution").as_posix(),
                "--file", (relative_root / "input.c").as_posix(),
                "--spec", (relative_root / "property.prp").as_posix(),
                "--workers", "1", "--run-root", (relative_root / "runs").as_posix(),
                "--name", "bounded-cleanup",
                "--timeout", "30", "--job-timeout", "30",
            ]
            command = [str(GIT_BASH), "-c", shlex.join(launcher_command)]
            started = time.monotonic()
            completed = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True, timeout=12)
            elapsed = time.monotonic() - started
            status_path = root / "runs" / "bounded-cleanup" / "exchange" / "worker-0" / "worker-status-worker-0.json"
            if status_path.is_file():
                import json
                worker_pid = json.loads(status_path.read_text(encoding="utf-8"))["pid"]
                subprocess.run(["taskkill.exe", "/PID", str(worker_pid), "/T", "/F"],
                               capture_output=True, check=False)
            self.assertEqual(0, completed.returncode, completed.stdout + completed.stderr)
            self.assertLess(elapsed, 12)
            self.assertIn("did not exit within 1s", completed.stderr)


if __name__ == "__main__":
    unittest.main()
