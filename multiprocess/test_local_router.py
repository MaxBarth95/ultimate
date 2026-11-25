#!/usr/bin/env python3
"""Tests of the routing of local_router.py with fake sessions (no Ultimate): python3 -m unittest test_local_router"""

import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import local_router as lr  # noqa: E402


class FakeProcess:
    def __init__(self):
        self.code = None

    def poll(self):
        return self.code


class RouterTest(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.seq = {}
        self.coord = self.session(lr.COORDINATOR, 'coordinator')
        self.ta1 = self.session(lr.TA_WORKER, 'ta1')
        self.ta2 = self.session(lr.TA_WORKER, 'ta2')
        self.witness = self.session(lr.WITNESS, 'witness')
        self.router = lr.Router(self.coord, [self.ta1, self.ta2], self.witness, log=lambda _: None)

    def tearDown(self):
        self.tmp.cleanup()

    def session(self, kind, sid, fingerprint='f'):
        session = lr.Session(kind, sid, os.path.join(self.tmp.name, sid), FakeProcess())
        self.write_out(session, 'ready.json', {'protocol': 'EXCHANGE_V1', 'kind': kind, 'fingerprint': fingerprint,
                                               'settingsHash': 'h'})
        return session

    def write_out(self, session, name, body):
        with open(session.path('out', name), 'w') as f:
            f.write(body if isinstance(body, str) else json.dumps(body))

    def send(self, session, typ, job=None, generation=None, body=None, ext='json'):
        self.seq[session.sid] = self.seq.get(session.sid, 0) + 1
        name = f'{self.seq[session.sid]:010d}-{typ}' + (f'-j{job}' if job is not None else '') \
            + (f'-g{generation}' if generation is not None else '') + '.' + ext
        self.write_out(session, name, body if body is not None else {'format': 'JSON_V1', 'job': job})

    def inbox(self, session):
        return sorted(n for n in os.listdir(session.path('in')) if not n.endswith('.tmp'))

    def types(self, session):
        return [lr.MESSAGE_NAME.match(n).group(2) + (('-j' + lr.MESSAGE_NAME.match(n).group(3))
                                                      if lr.MESSAGE_NAME.match(n).group(3) else '')
                for n in self.inbox(session) if lr.MESSAGE_NAME.match(n)]

    def test_counterexamples_go_to_idle_tas_and_wait_for_the_automaton(self):
        for job in (1, 2, 3):
            self.send(self.coord, 'COUNTEREXAMPLE', job, 0)
        self.router.step()
        self.assertEqual(self.types(self.ta1), ['COUNTEREXAMPLE-j1'])
        self.assertEqual(self.types(self.ta2), ['COUNTEREXAMPLE-j2'])
        # a RESULT alone does not free the TA
        self.send(self.ta1, 'RESULT', 1, 0)
        self.router.step()
        self.assertEqual(self.types(self.ta1), ['COUNTEREXAMPLE-j1'])
        self.assertEqual(self.types(self.coord), ['RESULT-j1'])
        self.assertEqual(self.types(self.witness), ['RESULT-j1'])
        self.send(self.ta1, 'INTERPOLANT_AUTOMATON', 1, 0, body='NestedWordAutomaton a = ();', ext='ats')
        self.router.step()
        self.assertEqual(self.types(self.ta1), ['COUNTEREXAMPLE-j1', 'COUNTEREXAMPLE-j3'])
        self.assertEqual(self.types(self.coord), ['RESULT-j1', 'INTERPOLANT_AUTOMATON-j1'])
        # the witness gets no automata
        self.assertEqual(self.types(self.witness), ['RESULT-j1'])

    def test_sequence_numbers_are_per_session_and_increasing(self):
        self.send(self.coord, 'COUNTEREXAMPLE', 1, 0)
        self.send(self.coord, 'ABSTRACTION', None, 1, body='x', ext='ats')
        self.router.step()
        self.assertEqual(self.inbox(self.ta1), ['0000000001-COUNTEREXAMPLE-j1-g0.json', '0000000002-ABSTRACTION-g1.ats'])
        self.assertEqual(self.inbox(self.ta2), ['0000000001-ABSTRACTION-g1.ats'])

    def test_cancel_of_a_queued_job_drops_it(self):
        self.ta2.process.code = -9
        self.ta2.gone = True
        self.send(self.coord, 'COUNTEREXAMPLE', 1, 0)
        self.send(self.coord, 'COUNTEREXAMPLE', 2, 0)
        self.send(self.coord, 'CANCEL', 2)
        self.router.step()
        self.send(self.ta1, 'INTERPOLANT_AUTOMATON', 1, 0, body='x', ext='ats')
        self.router.step()
        self.assertEqual(self.types(self.ta1), ['COUNTEREXAMPLE-j1'])

    def test_cancel_of_a_running_job_frees_its_ta(self):
        self.send(self.coord, 'COUNTEREXAMPLE', 1, 0)
        self.router.step()
        self.send(self.coord, 'CANCEL', 1)
        self.send(self.coord, 'COUNTEREXAMPLE', 2, 0)
        self.send(self.coord, 'COUNTEREXAMPLE', 3, 0)
        self.router.step()
        self.assertEqual(self.types(self.ta1), ['COUNTEREXAMPLE-j1', 'CANCEL-j1', 'COUNTEREXAMPLE-j2'])
        self.assertEqual(self.types(self.ta2), ['COUNTEREXAMPLE-j3'])

    def test_ta_killed_with_a_job_is_lost(self):
        self.send(self.coord, 'COUNTEREXAMPLE', 4, 2)
        self.router.step()
        self.ta1.process.code = -9
        self.router.step()
        self.assertEqual(self.types(self.coord), ['RESULT-j4'])
        result = json.load(open(self.coord.path('in', self.inbox(self.coord)[0])))
        self.assertEqual(result, {'format': 'JSON_V1', 'job': 4, 'generation': 2, 'status': 'UNKNOWN',
                                  'reason': 'SESSION_LOST'})
        self.assertEqual(self.types(self.witness), ['RESULT-j4'])
        self.assertEqual(self.router.health, lr.DEGRADED)

    def test_ta_that_exits_with_1_during_a_job_crashed(self):
        self.send(self.coord, 'COUNTEREXAMPLE', 1, 0)
        self.router.step()
        self.ta1.process.code = 1
        self.router.step()
        result = json.load(open(self.coord.path('in', self.inbox(self.coord)[0])))
        self.assertEqual(result['reason'], 'SESSION_CRASHED')

    def test_exit_codes(self):
        self.assertEqual(lr.gone_reason(-9), lr.SESSION_LOST)
        self.assertEqual(lr.gone_reason(137), lr.SESSION_LOST)
        self.assertEqual(lr.gone_reason(1), lr.SESSION_CRASHED)
        self.assertEqual(lr.gone_reason(255), lr.SESSION_CRASHED)
        self.assertEqual(lr.gone_reason(0), lr.SESSION_CRASHED)

    def test_idle_ta_lost_degrades_without_telling_the_coordinator(self):
        self.ta2.process.code = -9
        self.router.step()
        self.assertEqual(self.inbox(self.coord), [])
        self.assertEqual(self.router.health, lr.DEGRADED)
        self.send(self.coord, 'COUNTEREXAMPLE', 1, 0)
        self.send(self.coord, 'COUNTEREXAMPLE', 2, 0)
        self.router.step()
        # the second job waits for the remaining TA
        self.assertEqual(self.types(self.ta1), ['COUNTEREXAMPLE-j1'])
        self.assertEqual(self.types(self.ta2), [])

    def test_no_ta_left_answers_every_counterexample(self):
        self.send(self.coord, 'COUNTEREXAMPLE', 1, 0)
        self.send(self.coord, 'COUNTEREXAMPLE', 2, 0)
        self.send(self.coord, 'COUNTEREXAMPLE', 3, 0)
        self.router.step()
        self.ta1.process.code = -9
        self.ta2.process.code = -9
        self.router.step()
        self.send(self.coord, 'COUNTEREXAMPLE', 4, 1)
        self.router.step()
        self.assertEqual(sorted(self.types(self.coord)), ['RESULT-j1', 'RESULT-j2', 'RESULT-j3', 'RESULT-j4'])
        for name in self.inbox(self.coord):
            self.assertEqual(json.load(open(self.coord.path('in', name)))['reason'], 'SESSION_LOST')

    def test_testing_mode_idle_crash_is_an_error(self):
        router = lr.Router(self.coord, [self.ta1, self.ta2], self.witness, fail_on_ta_crash=True, log=lambda _: None)
        self.ta2.process.code = 1
        with self.assertRaises(lr.RouterError):
            router.step()

    def test_testing_mode_idle_kill_is_not_an_error(self):
        router = lr.Router(self.coord, [self.ta1, self.ta2], self.witness, fail_on_ta_crash=True, log=lambda _: None)
        self.ta2.process.code = -9
        router.step()
        self.assertEqual(router.health, lr.DEGRADED)

    def test_verdict_and_annotation_go_to_the_witness(self):
        self.send(self.coord, 'PROOF_ANNOTATION', None, 3, body={'format': 'JSON_V1', 'generation': 3, 'invariants': {}})
        self.send(self.coord, 'VERDICT', body={'format': 'JSON_V1', 'verdict': 'TRUE', 'decidedBy': 'COORDINATOR',
                                               'evidence': {}})
        self.router.step()
        self.assertEqual(self.router.verdict, 'TRUE')
        self.assertEqual(self.inbox(self.witness), ['0000000001-PROOF_ANNOTATION-g3.json', '0000000002-VERDICT.json'])

    def test_blobs_are_delivered_once_and_atomically(self):
        content = b'x' * 100
        sha = 'a' * 64
        with open(self.ta1.path('blobs', sha), 'wb') as f:
            f.write(content)
        self.send(self.coord, 'COUNTEREXAMPLE', 1, 0)
        self.router.step()
        ref = {'sha256': sha, 'size': len(content)}
        self.send(self.ta1, 'RESULT', 1, 0)
        self.send(self.ta1, 'INTERPOLANT_AUTOMATON', 1, 0, body=ref, ext='ref.json')
        self.router.step()
        target = self.coord.path('blobs', sha)
        self.assertEqual(open(target, 'rb').read(), content)
        before = os.stat(target).st_mtime_ns
        inode = os.stat(target).st_ino
        # the same blob again: the existing file is left alone
        self.send(self.coord, 'COUNTEREXAMPLE', 2, 0)
        self.router.step()
        self.send(self.ta1, 'RESULT', 2, 0)
        self.send(self.ta1, 'INTERPOLANT_AUTOMATON', 2, 0, body=ref, ext='ref.json')
        self.router.step()
        self.assertEqual((os.stat(target).st_mtime_ns, os.stat(target).st_ino), (before, inode))
        self.assertFalse([n for n in os.listdir(self.coord.path('blobs')) if n.endswith('.tmp')])

    def test_fingerprint_mismatch_is_an_error(self):
        other = self.session(lr.TA_WORKER, 'ta3', fingerprint='g')
        router = lr.Router(self.coord, [self.ta1, other], self.witness, log=lambda _: None)
        with self.assertRaises(lr.RouterError):
            router.step()

    def test_settings_hash_mismatch_is_an_error(self):
        other = lr.Session(lr.TA_WORKER, 'ta4', os.path.join(self.tmp.name, 'ta4'), FakeProcess())
        self.write_out(other, 'ready.json', {'protocol': 'EXCHANGE_V1', 'kind': lr.TA_WORKER, 'fingerprint': 'f',
                                             'settingsHash': 'other'})
        for session in (self.coord, self.ta1, self.witness):
            ready = json.load(open(session.path('out', 'ready.json')))
            ready['settingsHash'] = 'h'
            self.write_out(session, 'ready.json', ready)
        router = lr.Router(self.coord, [self.ta1, other], self.witness, log=lambda _: None)
        with self.assertRaises(lr.RouterError):
            router.step()

    def test_unexpected_message_is_an_error(self):
        self.send(self.ta1, 'VERDICT', body={})
        with self.assertRaises(lr.RouterError):
            self.router.step()

    def test_coordinator_exception_is_an_error(self):
        self.send(self.coord, 'EXCEPTION', body={'format': 'JSON_V1', 'kind': 'COORDINATOR',
                                                 'exceptionClass': 'X', 'message': 'm', 'stackTrace': ''})
        with self.assertRaises(lr.RouterError):
            self.router.step()

    def test_frontend_fingerprint_must_match(self):
        router = lr.Router(self.coord, [self.ta1, self.ta2], self.witness, log=lambda _: None,
                           reference={'frontend': {'fingerprint': 'other', 'settingsHash': 'h'}})
        with self.assertRaises(lr.RouterError):
            router.step()
        router = lr.Router(self.coord, [self.ta1, self.ta2], self.witness, log=lambda _: None,
                           reference={'frontend': {'fingerprint': 'f', 'settingsHash': 'h'}})
        router.step()
        self.assertEqual(set(router.ready_seconds), {'coordinator', 'ta1', 'ta2', 'witness'})

    def test_witness_gets_the_time_limit_plus_the_witness_timeout(self):
        args = type('Args', (), {'timeout': 120, 'witness_timeout': 60})()
        self.assertEqual(lr.session_timeout(args, lr.COORDINATOR), 120)
        self.assertEqual(lr.session_timeout(args, lr.TA_WORKER), 120)
        self.assertEqual(lr.session_timeout(args, lr.WITNESS), 180)

    def test_witness_status(self):
        self.assertEqual(lr.witness_status('FALSE', 0, 3), (lr.WITNESS_PRESENT, False))
        self.assertEqual(lr.witness_status('FALSE', 0, 2), (lr.WITNESS_DEGRADED, False))
        self.assertEqual(lr.witness_status('FALSE', 0, 1), (lr.WITNESS_DEGRADED, False))
        self.assertEqual(lr.witness_status('FALSE', 1, None), (lr.WITNESS_MISSING, True))
        self.assertEqual(lr.witness_status('TRUE', 0, 0), (lr.WITNESS_PRESENT, False))
        self.assertEqual(lr.witness_status('TRUE', 1, None), (lr.WITNESS_MISSING, False))
        self.assertEqual(lr.witness_status('UNKNOWN', 0, None), (lr.WITNESS_NOT_APPLICABLE, False))


if __name__ == '__main__':
    unittest.main()
