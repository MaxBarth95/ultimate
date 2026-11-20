#!/usr/bin/env python3
"""End-to-end tests of the multi-process trace abstraction: local_router.py on small programs with expected outcomes.

    python3 multiprocess/e2e_test.py --tool releaseScripts/default/UAutomizer-linux [--root /tmp/e2e] [--only NAME]

Each case runs a whole COORDINATOR + TA_WORKER + WITNESS run and checks verdict, health and witness status. A case
takes 15-40 s. The routing logic itself is unit-tested in test_local_router.py, without Ultimate.
"""

import argparse
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PROGRAMS = os.path.join(HERE, 'programs')

# name, program, router options, expected (verdict, health, witness status)
CASES = [
    ('loop-safe', 'loop-safe.c', ['--ta', '2'], ('TRUE', 'OK', 'WITNESS_PRESENT')),
    ('loop-unsafe', 'loop-unsafe.c', ['--ta', '2'], ('FALSE', 'OK', 'WITNESS_PRESENT')),
    # an overapproximated counterexample never gives FALSE (Ultimate's integer run answers unprovable)
    ('float-integer-mode', 'float-integer-mode.c', ['--ta', '1'], ('UNKNOWN', 'OK', 'WITNESS_NOT_APPLICABLE')),
    # a real UNKNOWN of a TA trace check ends the run with UNKNOWN at once (R2.6 rule 3)
    ('ta-unknown', 'fermat.c',
     ['--ta', '2', '--set', 'traceabstraction.trace.refinement.strategy=FIXED_PREFERENCES',
      '--set', 'traceabstraction.smt.solver=Internal_SMTInterpol'], ('UNKNOWN', 'OK', 'WITNESS_NOT_APPLICABLE')),
    # a killed WITNESS keeps the verdict
    ('witness-killed', 'loop-unsafe.c', ['--ta', '1', '--kill-witness-at-verdict'],
     ('FALSE', 'DEGRADED', 'WITNESS_MISSING')),
    # a session with other settings ends the run
    ('settings-mismatch', 'loop-safe.c',
     ['--ta', '2', '--set-ta1', 'traceabstraction.compute.interpolants.along.a.counterexample=BackwardPredicates'],
     ('ERROR', 'ERROR', 'WITNESS_NOT_APPLICABLE')),
]


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--tool', required=True)
    p.add_argument('--root', default='/tmp/ultimate-multiprocess-e2e')
    p.add_argument('--only', action='append')
    p.add_argument('--timeout', default='120')
    args = p.parse_args()
    failures = 0
    for name, program, options, expected in CASES:
        if args.only and name not in args.only:
            continue
        root = os.path.join(args.root, name)
        command = [sys.executable, os.path.join(HERE, 'local_router.py'), '--tool', args.tool,
                   '--file', os.path.join(PROGRAMS, program), '--root', root, '--timeout', args.timeout] + options
        subprocess.run(command, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
        try:
            report = json.load(open(os.path.join(root, 'report.json')))
            actual = (report['verdict'], report['health'], report['witness']['status'])
        except (OSError, ValueError, KeyError) as e:
            actual = ('NO REPORT', str(e), '')
        ok = actual == expected
        failures += 0 if ok else 1
        print(f'{"ok  " if ok else "FAIL"} {name}: {actual}' + ('' if ok else f', expected {expected}'))
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main())
