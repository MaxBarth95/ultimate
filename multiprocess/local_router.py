#!/usr/bin/env python3
"""Local router for the multi-process trace abstraction (UltimateCloud Phase 2).

Runs one COORDINATOR, N TA_WORKER sessions and one WITNESS session of Ultimate on this machine and routes the
messages between their session directories (protocol EXCHANGE_V1, see
trunk/source/TraceAbstraction/.doc/multiprocessed/). It is the reference implementation of the routing that
UltimateCloud's scheduler (CooperativeStrategy, Phase 4) does:

- ABSTRACTION: broadcast to every live TA session.
- COUNTEREXAMPLE: work queue; it goes to an idle TA session. A TA session is busy from its COUNTEREXAMPLE until the
  job's INTERPOLANT_AUTOMATON, or until a CANCEL for the job is routed. A cancelled job is never waited for, and a
  RESULT without an automaton is legal.
- CANCEL: to the TA session of the job; a job still in the queue is dropped.
- RESULT and INTERPOLANT_AUTOMATON: to the coordinator; RESULT, PROOF_ANNOTATION and VERDICT are copied to WITNESS.
- A TA session that ends with a job: the coordinator (and WITNESS) get the synthetic
  RESULT {job, generation, status: UNKNOWN, reason}, with reason SESSION_LOST if the process was killed by a signal
  and SESSION_CRASHED otherwise.
- A TA session that ends idle: it leaves the work queue and the run is DEGRADED; the coordinator is not told. With
  --fail-on-ta-crash (testing mode) an idle TA that crashed ends the run with ERROR. Once no live TA session is left,
  every queued and later COUNTEREXAMPLE is answered at once with the synthetic SESSION_LOST result.
- VERDICT: fixes the verdict, shuts the coordinator and the TA sessions down and waits for the witness.

With --package (UltimateCloud Phase 6) a FRONTEND session runs first and writes the program package; COORDINATOR and
the TA sessions then start from the package (toolchain AutomizerPackage.xml), WITNESS from C. All of them, FRONTEND
included, must have the same fingerprint and settingsHash.

Only the standard library is used. Tests: python3 -m unittest multiprocess/test_local_router.py
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time

PROTOCOL = 'EXCHANGE_V1'
MESSAGE_NAME = re.compile(r'(\d+)-([A-Z_]+)(?:-j(\d+))?(?:-g(\d+))?\.(ref\.json|[a-z]+)$')
LOG_PATTERN = "%d{yyyy-MM-dd'T'HH:mm:ss.SSSXXX} %p [{sid}] %c: %m%n"
SPECIFICATION = 'CHECK( init(main()), LTL(G ! call(reach_error())) )'

COORDINATOR, TA_WORKER, WITNESS, FRONTEND = 'COORDINATOR', 'TA_WORKER', 'WITNESS', 'FRONTEND'
PACKAGE_TOOLCHAIN = 'AutomizerPackage.xml'
SESSION_LOST, SESSION_CRASHED = 'SESSION_LOST', 'SESSION_CRASHED'

# health of a run, as UltimateCloud's scheduler reports it
OK, DEGRADED, ERROR = 'OK', 'DEGRADED', 'ERROR'
# witness status, as UltimateCloud's WitnessStatus
WITNESS_PRESENT, WITNESS_DEGRADED, WITNESS_MISSING = 'WITNESS_PRESENT', 'WITNESS_DEGRADED', 'WITNESS_MISSING'
WITNESS_NOT_APPLICABLE, WITNESS_NOT_REQUESTED = 'WITNESS_NOT_APPLICABLE', 'WITNESS_NOT_REQUESTED'
# witnessLevel of the WITNESS statistics
LEVEL_WITH_VALUES = 3


class RouterError(Exception):
    """The run cannot go on (fingerprint mismatch, unexpected message, coordinator failure, testing mode)."""


class Session:
    """A session directory and the process that works on it."""

    def __init__(self, kind, sid, directory, process=None):
        self.kind = kind
        self.sid = sid
        self.dir = directory
        self.process = process
        self.next_in = 1
        self.read = set()
        self.job = None  # TA: the job it works on
        self.ready = None
        self.gone = False  # TA: its end was handled
        for sub in ('in', 'out', 'blobs', 'log'):
            os.makedirs(os.path.join(directory, sub), exist_ok=True)

    def path(self, *parts):
        return os.path.join(self.dir, *parts)

    def returncode(self):
        return None if self.process is None else self.process.poll()

    def alive(self):
        return self.returncode() is None

    def new_messages(self):
        """The unread message files of out/, in sequence order."""
        found = []
        for name in os.listdir(self.path('out')):
            match = MESSAGE_NAME.match(name)
            if match and name not in self.read:
                found.append((int(match.group(1)), name, match))
        found.sort()
        return found

    def read_ready(self):
        if self.ready is None and os.path.exists(self.path('out', 'ready.json')):
            ready = json.load(open(self.path('out', 'ready.json')))
            if ready.get('protocol') != PROTOCOL:
                raise RouterError(f'{self.sid}: unknown protocol {ready.get("protocol")}')
            if ready.get('kind') != self.kind:
                raise RouterError(f'{self.sid}: is a {ready.get("kind")}, not a {self.kind}')
            self.ready = ready
        return self.ready

    def statistics(self):
        try:
            return json.load(open(self.path('out', 'statistics.json')))
        except (OSError, ValueError):
            return None

    def _next_name(self, typ, job, generation, ext):
        name = f'{self.next_in:010d}-{typ}'
        if job is not None:
            name += f'-j{job}'
        if generation is not None:
            name += f'-g{generation}'
        self.next_in += 1
        return name + '.' + ext

    def deliver(self, source, name, match):
        """Copies a message file of another session's out/ (and its blob) into in/, with the next sequence number."""
        typ, job, generation, ext = match.group(2), match.group(3), match.group(4), match.group(5)
        if ext == 'ref.json':
            ref = json.load(open(source.path('out', name)))
            target = self.path('blobs', ref['sha256'])
            # content-addressed: an existing blob is the same, and is never rewritten (a reader may be on it)
            if not os.path.exists(target):
                shutil.copyfile(source.path('blobs', ref['sha256']), target + '.tmp')
                os.replace(target + '.tmp', target)
        with open(source.path('out', name), 'rb') as f:
            self._write(self._next_name(typ, job, generation, ext), f.read())

    def deliver_json(self, typ, job, generation, body):
        self._write(self._next_name(typ, job, generation, 'json'), json.dumps(body).encode())

    def _write(self, name, data):
        tmp = self.path('in', name + '.tmp')
        with open(tmp, 'wb') as f:
            f.write(data)
        os.replace(tmp, self.path('in', name))

    def shutdown(self):
        open(self.path('in', 'shutdown'), 'w').close()


def synthetic_result(job, generation, reason):
    return {'format': 'JSON_V1', 'job': job, 'generation': generation, 'status': 'UNKNOWN', 'reason': reason}


def gone_reason(returncode):
    """SESSION_LOST for a process killed by a signal (negative, or 128 + n from a shell), SESSION_CRASHED otherwise.
    255 is the CLI's own error code, not a signal."""
    return SESSION_LOST if returncode < 0 or 128 < returncode < 255 else SESSION_CRASHED


def witness_status(verdict, witness_exit, witness_level):
    """The witness status of a run, and whether the witness makes the run DEGRADED."""
    if verdict == 'FALSE':
        if witness_exit != 0:
            return WITNESS_MISSING, True
        return (WITNESS_PRESENT if witness_level == LEVEL_WITH_VALUES else WITNESS_DEGRADED), False
    if verdict == 'TRUE':
        return (WITNESS_PRESENT if witness_exit == 0 else WITNESS_MISSING), False
    return WITNESS_NOT_APPLICABLE, False


class Router:
    """The routing of one run. step() routes whatever is there; it never blocks."""

    def __init__(self, coordinator, tas, witness, fail_on_ta_crash=False, log=print, reference=None):
        self.coordinator = coordinator
        # sid -> ready.json of a session outside the routing (FRONTEND), checked like the others
        self.reference = reference or {}
        self.start = time.time()
        self.ready_seconds = {}
        self.tas = tas
        self.witness = witness
        self.fail_on_ta_crash = fail_on_ta_crash
        self.log = log
        self.queue = []  # COUNTEREXAMPLE (name, match) waiting for an idle TA
        self.generation_of_job = {}
        self.verdict = None
        self.verdict_file = None
        self.health = OK
        self.counts = {}
        self.events = []

    def sessions(self):
        return [self.coordinator] + self.tas + ([self.witness] if self.witness else [])

    def event(self, text):
        self.events.append(text)
        self.log(text)

    def check_fingerprints(self):
        """All sessions of a run must have the same program (fingerprint) and the same settings (settingsHash)."""
        ready = dict(self.reference)
        for s in self.sessions():
            if s.read_ready():
                ready[s.sid] = s.ready
                self.ready_seconds.setdefault(s.sid, round(time.time() - self.start, 1))
        for key in ('fingerprint', 'settingsHash'):
            values = {sid: r[key] for sid, r in ready.items()}
            if len(set(values.values())) > 1:
                raise RouterError(f'{key} mismatch: {values}')

    def live_tas(self):
        return [t for t in self.tas if not t.gone and t.alive()]

    def step(self):
        """Routes every new message once. Returns whether anything happened."""
        self.check_fingerprints()
        progressed = False
        for session in self.sessions():
            for _, name, match in session.new_messages():
                session.read.add(name)
                progressed = True
                self.route(session, name, match)
                if self.verdict is not None:
                    return True
                # keep the order of the coordinator's messages for a TA that is idle now
                self.dispatch()
        progressed |= self.handle_gone_tas()
        progressed |= self.dispatch()
        if self.coordinator.returncode() not in (None, 0) and self.verdict is None:
            if not self.coordinator.new_messages():
                raise RouterError(f'the coordinator exited with {self.coordinator.returncode()} before a verdict')
        return progressed

    def route(self, source, name, match):
        typ = match.group(2)
        job = None if match.group(3) is None else int(match.group(3))
        self.counts[typ] = self.counts.get(typ, 0) + 1
        if typ == 'EXCEPTION':
            report = json.load(open(source.path('out', name)))
            self.event(f'EXCEPTION from {source.sid}: {report["exceptionClass"]}: {report.get("message")}')
            if source is self.coordinator:
                raise RouterError(f'the coordinator failed: {report.get("message")}')
            return
        if source is self.coordinator:
            if typ == 'COUNTEREXAMPLE':
                self.generation_of_job[job] = int(match.group(4))
                self.queue.append((name, match))
            elif typ == 'ABSTRACTION':
                for ta in self.live_tas():
                    ta.deliver(source, name, match)
            elif typ == 'CANCEL':
                owners = [t for t in self.tas if t.job == job]
                if owners:
                    owners[0].deliver(source, name, match)
                    owners[0].job = None
                else:
                    self.queue = [(n, m) for n, m in self.queue if int(m.group(3)) != job]
            elif typ == 'PROOF_ANNOTATION':
                if self.witness:
                    self.witness.deliver(source, name, match)
            elif typ == 'VERDICT':
                if self.witness:
                    self.witness.deliver(source, name, match)
                self.verdict = json.load(open(source.path('out', name)))['verdict']
                self.verdict_file = source.path('out', name)
            else:
                raise RouterError(f'unexpected {typ} from the coordinator')
        elif source in self.tas:
            if typ == 'RESULT':
                self.coordinator.deliver(source, name, match)
                if self.witness:
                    self.witness.deliver(source, name, match)
            elif typ == 'INTERPOLANT_AUTOMATON':
                self.coordinator.deliver(source, name, match)
                if source.job == job:
                    source.job = None
            else:
                raise RouterError(f'unexpected {typ} from {source.sid}')
        else:
            raise RouterError(f'unexpected {typ} from {source.sid}')

    def handle_gone_tas(self):
        progressed = False
        for ta in self.tas:
            if ta.gone or ta.alive():
                continue
            # a TA may send its last messages just before it exits
            if ta.new_messages():
                continue
            ta.gone = True
            progressed = True
            reason = gone_reason(ta.returncode())
            if ta.job is not None:
                job = ta.job
                ta.job = None
                self.event(f'{ta.sid} ended with job {job} (exit {ta.returncode()}, {reason})')
                self.send_synthetic(job, reason)
            else:
                self.event(f'{ta.sid} ended idle (exit {ta.returncode()}, {reason})')
                if reason == SESSION_CRASHED and self.fail_on_ta_crash:
                    raise RouterError(f'{ta.sid} crashed while idle (testing mode)')
            self.health = DEGRADED
        return progressed

    def send_synthetic(self, job, reason):
        body = synthetic_result(job, self.generation_of_job[job], reason)
        self.coordinator.deliver_json('RESULT', job, self.generation_of_job[job], body)
        if self.witness:
            self.witness.deliver_json('RESULT', job, self.generation_of_job[job], body)

    def dispatch(self):
        progressed = False
        live = self.live_tas()
        if not live and self.queue:
            # no TA session is left: the coordinator runs out of TA sessions
            for name, match in self.queue:
                self.send_synthetic(int(match.group(3)), SESSION_LOST)
            self.queue = []
            return True
        while self.queue:
            idle = [t for t in live if t.job is None and t.ready]
            if not idle:
                break
            name, match = self.queue.pop(0)
            idle[0].deliver(self.coordinator, name, match)
            idle[0].job = int(match.group(3))
            progressed = True
        return progressed


class UltimateProcess:
    """An Ultimate CLI process for one session (R1.3: the CLI, an explicit toolchain and .epf, no Ultimate.py)."""

    def __init__(self, args, session, extra, program=None, toolchain=None):
        tool = os.path.abspath(args.tool)
        program = os.path.abspath(args.file) if program is None else program
        launchers = [f for f in os.listdir(os.path.join(tool, 'plugins')) if f.startswith('org.eclipse.equinox.launcher_')]
        if len(launchers) != 1:
            raise RouterError(f'no unique Equinox launcher in {tool}/plugins')
        if toolchain is None:
            toolchain = 'AutomizerCInline_WitnessPrinter.xml' if session.kind == WITNESS else 'AutomizerCInline.xml'
        command = ['java', '-Dultimate.logger.pattern=' + LOG_PATTERN.replace('{sid}', session.sid),
                   '-Dultimate.cli.exitOnException=true', '-Dosgi.configuration.area=' + session.path('data', 'config'),
                   f'-Xmx{args.heap}', '-Xss1M', '-jar', os.path.join(tool, 'plugins', launchers[0]),
                   '-data', '@noDefault', '-ultimatedata', session.path('data'),
                   '-tc', os.path.join(args.toolchains, toolchain), '-s', args.settings, '-i', program,
                   '--cacsl2boogietranslator.entry.function', 'main',
                   '--core.toolchain.timeout.in.seconds', str(session_timeout(args, session.kind)),
                   '--traceabstraction.multi.process.component', session.kind,
                   '--traceabstraction.multi.process.exchange.root', session.dir,
                   '--traceabstraction.multi.process.session.id', session.sid] + args.overrides + extra
        if session.kind == WITNESS:
            command += ['--witnessprinter.witness.directory', session.path('out'),
                        '--witnessprinter.witness.filename', 'witness',
                        '--witnessprinter.write.witness.besides.input.file', 'false',
                        '--witnessprinter.graph.data.specification', SPECIFICATION,
                        '--witnessprinter.graph.data.producer', 'Automizer',
                        '--witnessprinter.graph.data.architecture', args.architecture,
                        '--witnessprinter.graph.data.programhash', sha256_of(args.file)]
        self.stdout = open(session.path('log', 'stdout.log'), 'wb')
        self.stderr = open(session.path('log', 'stderr.log'), 'wb')
        self.process = subprocess.Popen(command, stdout=self.stdout, stderr=self.stderr)

    def poll(self):
        return self.process.poll()

    def wait(self, timeout):
        return self.process.wait(timeout=timeout)

    def kill(self):
        self.process.kill()


def session_timeout(args, kind):
    """The toolchain timeout of a session: the run's time limit, and for WITNESS that plus the witness timeout, so that
    a verdict at the end of the run can still be witnessed. Ultimate leaves the timeout out of settingsHash."""
    return args.timeout + args.witness_timeout if kind == WITNESS else args.timeout


def sha256_of(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def default_settings(tool, architecture):
    return os.path.join(tool, 'config', f'svcomp-Reach-{architecture}-Automizer_Default.epf')


def parse_args(argv):
    here = os.path.dirname(os.path.abspath(__file__))
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--tool', required=True, help='an Automizer directory (releaseScripts/default/UAutomizer-linux)')
    p.add_argument('--file', required=True, help='the C program')
    p.add_argument('--root', required=True, help='the directory of the session directories (emptied first)')
    p.add_argument('--ta', type=int, default=2, help='number of TA_WORKER sessions')
    p.add_argument('--timeout', type=int, default=900, help='time limit of every session in seconds')
    p.add_argument('--witness-timeout', type=int, default=60, help='seconds to wait for the witness after a verdict')
    p.add_argument('--architecture', default='32bit', choices=['32bit', '64bit'])
    p.add_argument('--settings', help='the .epf (default: the SV-COMP Reach Automizer default of the architecture)')
    p.add_argument('--toolchains', help='the directory of AutomizerCInline*.xml (default: the tool\'s config/ if it '
                   'has them, else trunk/examples/toolchains)')
    p.add_argument('--set', action='append', default=[], metavar='KEY=VALUE',
                   help='an Ultimate setting for every session, e.g. traceabstraction.trace.refinement.strategy=CAMEL')
    p.add_argument('--heap', default='4G', help='-Xmx of every session')
    p.add_argument('--no-witness', action='store_true', help='run without a WITNESS session')
    p.add_argument('--fail-on-ta-crash', action='store_true', help='testing mode: a crashed TA ends the run with ERROR')
    p.add_argument('--report', help='write the report as JSON to this file (default: <root>/report.json)')
    p.add_argument('--package', action='store_true',
                   help='run a FRONTEND session first; COORDINATOR and TA sessions start from its program package')
    # fault injection, for tests of the protocol
    p.add_argument('--kill-ta-after', type=float, help='kill -9 the first TA once it has a job after this many seconds')
    p.add_argument('--crash-ta-after', type=float, help='make the first TA throw once it has a job after this many seconds')
    p.add_argument('--kill-witness-at-verdict', action='store_true', help='kill -9 the WITNESS session at the verdict')
    p.add_argument('--set-ta1', action='append', default=[], metavar='KEY=VALUE',
                   help='an Ultimate setting for the first TA only (must give a mismatch)')
    args = p.parse_args(argv)
    if args.settings is None:
        args.settings = default_settings(args.tool, args.architecture)
    if args.toolchains is None:
        config = os.path.join(args.tool, 'config')
        args.toolchains = config if os.path.exists(os.path.join(config, 'AutomizerCInline.xml')) \
            else os.path.join(here, '..', 'trunk', 'examples', 'toolchains')
    args.overrides = settings_options(args.set)
    args.ta1_overrides = settings_options(args.set_ta1)
    return args


def settings_options(settings):
    options = []
    for setting in settings:
        key, sep, value = setting.partition('=')
        if not sep:
            raise SystemExit(f'a setting needs KEY=VALUE, not {setting}')
        options += ['--' + key, value]
    return options


def run_frontend(args, root):
    """Runs the FRONTEND session to its end. Returns the path of the program package, its ready.json and statistics."""
    frontend = Session(FRONTEND, 'frontend', os.path.join(root, 'frontend'))
    frontend.process = UltimateProcess(args, frontend, [])
    try:
        code = frontend.process.wait(args.timeout + 60)
    except subprocess.TimeoutExpired:
        frontend.process.kill()
        raise RouterError('FRONTEND did not end in time')
    if code != 0:
        raise RouterError(f'FRONTEND ended with exit code {code}')
    ready = frontend.read_ready()
    if ready is None:
        raise RouterError('FRONTEND wrote no ready.json')
    messages = frontend.new_messages()
    if len(messages) != 1 or messages[0][2].group(2) != 'PROGRAM_PACKAGE':
        raise RouterError(f'FRONTEND must send exactly one PROGRAM_PACKAGE, sent {[m[1] for m in messages]}')
    _, name, match = messages[0]
    source = frontend.path('out', name)
    if match.group(5) == 'ref.json':
        source = frontend.path('blobs', json.load(open(source))['sha256'])
    package = os.path.join(root, 'program-package.json')
    shutil.copyfile(source, package)
    if hashlib.sha256(open(package, 'rb').read()).hexdigest() != ready['fingerprint']:
        raise RouterError('the fingerprint of FRONTEND is not the hash of its program package')
    return package, ready, frontend.statistics() or {}


def run(args):
    shutil.rmtree(args.root, ignore_errors=True)
    root = os.path.abspath(args.root)
    start = time.time()
    package, frontend_ready, frontend_statistics, frontend_seconds = None, None, {}, None
    if args.package:
        try:
            package, frontend_ready, frontend_statistics = run_frontend(args, root)
        except RouterError as e:
            report = {'verdict': 'ERROR', 'health': ERROR, 'witness': {'status': WITNESS_NOT_APPLICABLE},
                      'events': [f'ERROR: {e}']}
            with open(args.report or os.path.join(root, 'report.json'), 'w') as f:
                json.dump(report, f, indent=2)
            return report
        frontend_seconds = round(time.time() - start, 1)

    def make(kind, sid, extra):
        session = Session(kind, sid, os.path.join(root, sid))
        if package is not None and kind in (COORDINATOR, TA_WORKER):
            session.process = UltimateProcess(args, session, extra, program=package, toolchain=PACKAGE_TOOLCHAIN)
        else:
            session.process = UltimateProcess(args, session, extra)
        return session

    coordinator = make(COORDINATOR, 'coordinator',
                       ['--traceabstraction.number.of.ta.workers.in.parallel.trace.abstraction', str(args.ta)]
                       + (['--traceabstraction.multi.process.fail.on.ta.crash', 'true'] if args.fail_on_ta_crash else []))
    tas = [make(TA_WORKER, f'ta{i}', args.ta1_overrides if i == 1 else []) for i in range(1, args.ta + 1)]
    witness = None if args.no_witness else make(WITNESS, 'witness', [])
    router = Router(coordinator, tas, witness, args.fail_on_ta_crash,
                    reference={'frontend': frontend_ready} if frontend_ready else None)
    injected = False
    verdict_time = None
    try:
        while router.verdict is None:
            if not router.step():
                time.sleep(0.05)
            if not injected and tas and tas[0].job is not None:
                if args.kill_ta_after is not None and time.time() - start > args.kill_ta_after:
                    tas[0].process.kill()
                    router.event(f'injected: kill -9 {tas[0].sid}')
                    injected = True
                elif args.crash_ta_after is not None and time.time() - start > args.crash_ta_after:
                    # an unknown message type makes the TA's Ultimate throw
                    tas[0].deliver_json('FOO', None, None, {})
                    router.event(f'injected: unknown message type to {tas[0].sid}')
                    injected = True
        verdict_time = time.time() - start
    except RouterError as e:
        router.event(f'ERROR: {e}')
        router.health = ERROR
        router.verdict = 'ERROR'
    finally:
        for session in [coordinator] + tas:
            if session.alive():
                session.shutdown()

    status, level, degraded_by_witness = WITNESS_NOT_REQUESTED, None, False
    if witness is not None and args.kill_witness_at_verdict and witness.alive():
        witness.process.kill()
        router.event('injected: kill -9 witness')
    if witness is not None:
        if router.verdict in ('TRUE', 'FALSE'):
            try:
                witness_exit = witness.process.wait(args.witness_timeout)
            except subprocess.TimeoutExpired:
                witness.process.kill()
                witness_exit = 'timeout'
            statistics = witness.statistics() or {}
            level = statistics.get('counters', {}).get('witnessLevel')
            status, degraded_by_witness = witness_status(router.verdict, witness_exit, level)
        else:
            witness.shutdown()
            status = WITNESS_NOT_APPLICABLE
    if degraded_by_witness and router.health == OK:
        router.health = DEGRADED

    exits = {}
    for session in router.sessions():
        try:
            exits[session.sid] = session.process.wait(30)
        except subprocess.TimeoutExpired:
            session.process.kill()
            exits[session.sid] = 'killed'
    report = {
        'verdict': router.verdict,
        'health': router.health,
        'witness': {'status': status, 'level': level,
                    'file': witness.path('out', 'witness.yml') if status in (WITNESS_PRESENT, WITNESS_DEGRADED) else None},
        'verdictSeconds': None if verdict_time is None else round(verdict_time, 1),
        'totalSeconds': round(time.time() - start, 1),
        'readySeconds': router.ready_seconds,
        'messages': router.counts,
        'exitCodes': exits,
        'events': router.events,
    }
    if args.package:
        report['frontend'] = {'seconds': frontend_seconds, 'fingerprint': frontend_ready['fingerprint'],
                              'counters': frontend_statistics.get('counters', {})}
    with open(args.report or os.path.join(root, 'report.json'), 'w') as f:
        json.dump(report, f, indent=2)
    return report


def main(argv=None):
    args = parse_args(argv)
    report = run(args)
    print(f'VERDICT {report["verdict"]} ({report["health"]}) in {report["verdictSeconds"]} s; '
          f'witness {report["witness"]["status"]}; messages {report["messages"]}; exit codes {report["exitCodes"]}')
    return 0 if report['health'] != ERROR else 1


if __name__ == '__main__':
    signal.signal(signal.SIGINT, signal.default_int_handler)
    sys.exit(main())
