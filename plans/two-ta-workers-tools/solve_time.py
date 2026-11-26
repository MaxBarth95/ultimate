#!/usr/bin/env python3
"""Compare two BenchExec run sets on the time the analysis needs, without pre- and post-processing.

Walltime includes the JVM start, parsing, the ICFG construction, the shutdown of all solvers, the witness and, for
tasks where Ultimate.py reruns with the bit-precise settings, all of that twice. These costs are almost the same in
both configurations and hide the difference of the analysis itself. This script reads every log of both run sets and
measures, for each toolchain of a run,

    solve = decision - start
    start    = "Applying trace abstraction" (first CEGAR line of the toolchain)
    decision = the first of
               "<WORKER> delivered a verdict" / "<WORKER> refuted the program"  (k-induction, value analysis, TA cex)
               "every worker finished without a verdict"                         (UNKNOWN)
               the last "Checking if program is safe" before the statistics      (TA proof)
               the statistics line "Iteration N" of the parallel loop             (fallback)

and sums it over the toolchains of the run. overhead = walltime - solve.

Usage:
    solve_time.py TABLE.html ZIP [ZIP ...] --base RUNSET --cmp RUNSET [--cache FILE] [--csv FILE] [--jobs N]

The run set names are the "name" fields of the table (e.g. UParalizer-no-probation, two-ta-workers-v2). The zips are
the .logfiles.zip archives of the table; logs are streamed out of them, never extracted.
"""
import argparse
import csv
import datetime
import json
import math
import os
import pickle
import re
import statistics
import sys
import zipfile
from collections import Counter, defaultdict
from multiprocessing import Pool
from urllib.parse import unquote

TS = re.compile(r'^\[(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d,\d{3}) \w+ +L\d+ +([^\]]*)\]: (.*)')
VERDICT = re.compile(r'Main: (\S+) (delivered a verdict|refuted the program)')

_ZIPS = {}


def ts(s):
    return datetime.datetime.strptime(s, '%Y-%m-%d %H:%M:%S,%f').timestamp()


def load_table(path):
    s = open(path, encoding='utf-8', errors='replace').read()
    i = s.find('const data = ') + len('const data = ')
    data, _ = json.JSONDecoder().raw_decode(s[i:])
    names = [t['name'] for t in data['tools']]
    rows = []
    for r in data['rows']:
        e = {'task': r['id'][0], 'expected': r['id'][1]}
        for n, res in zip(names, r['results']):
            v = res['values']
            try:
                wall = float(v[2].get('raw'))
            except (TypeError, ValueError):
                wall = None
            e[n] = {'cat': res.get('category'), 'status': v[0].get('raw'), 'wall': wall,
                    'href': unquote(res.get('href') or '')}
        rows.append(e)
    return names, rows


def init_worker(zip_paths):
    for z in zip_paths:
        zf = zipfile.ZipFile(z)
        for name in zf.namelist():
            _ZIPS[name] = zf


def parse_toolchain(lines):
    start = decision = safe_check = stats = None
    source = None
    iterations = 0
    for line in lines:
        m = TS.match(line)
        if not m:
            continue
        msg = m.group(3)
        if msg.startswith('Applying trace abstraction'):
            start = start or ts(m.group(1))
        elif msg.startswith('=== Iteration '):
            iterations += 1
        elif decision is None and (v := VERDICT.search(msg)):
            decision = ts(m.group(1))
            source = v.group(1)
        elif decision is None and 'every worker finished without a verdict' in msg:
            decision = ts(m.group(1))
            source = 'NONE'
        elif msg == 'Checking if program is safe' and stats is None:
            safe_check = ts(m.group(1))
        elif stats is None and re.fullmatch(r'Iteration \d+', msg) and 'ParallelNwaCegarLoop' in m.group(2):
            stats = ts(m.group(1))
    if start is None:
        return None
    if decision is None:
        if safe_check is not None:
            decision, source = safe_check, ('TA_PROOF' if iterations else 'TRIVIAL')
        elif stats is not None:
            decision, source = stats, 'UNKNOWN_END'
        else:
            return None
    if source == 'TA':
        source = 'TA_CEX'
    return max(decision - start, 0.0), source


def parse_run(href):
    zf = _ZIPS.get(href)
    if zf is None:
        return href, None
    txt = zf.read(href).decode('utf-8', 'replace')
    parts = txt.split('Calling Ultimate with')[1:] or [txt]
    solve = 0.0
    source = None
    toolchains = 0
    for part in parts:
        r = parse_toolchain(part.split('\n'))
        if r is None:
            continue
        solve += r[0]
        source = r[1]
        toolchains += 1
    if toolchains == 0:
        return href, None
    return href, {'solve': solve, 'source': source, 'toolchains': toolchains}


def geo(xs):
    xs = [x for x in xs if x > 0]
    return math.exp(statistics.mean(map(math.log, xs))) if xs else float('nan')


def summary(label, pairs, min_time):
    """pairs: list of (base value, cmp value)."""
    r = [b / a for a, b in pairs if a >= min_time and b >= min_time]
    if not r:
        return f'{label:34} n=0'
    return (f'{label:34} n={len(r):6}  geomean cmp/base {geo(r):.3f}  median {statistics.median(r):.3f}  '
            f'cmp faster(<0.95) {sum(x < 0.95 for x in r):5}  slower(>1.05) {sum(x > 1.05 for x in r):5}  '
            f'sum ratio {sum(b for a, b in pairs) / max(sum(a for a, b in pairs), 1e-9):.3f}')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('table')
    ap.add_argument('zips', nargs='+')
    ap.add_argument('--base', required=True)
    ap.add_argument('--cmp', required=True)
    ap.add_argument('--cache', help='pickle with already parsed logs, read and updated')
    ap.add_argument('--csv', help='write one line per task with both runs')
    ap.add_argument('--jobs', type=int, default=os.cpu_count())
    ap.add_argument('--min-time', type=float, default=0.05,
                    help='ignore pairs where one side is below this many seconds (ratios of ~0 are noise)')
    a = ap.parse_args()

    names, rows = load_table(a.table)
    for n in (a.base, a.cmp):
        if n not in names:
            sys.exit(f'run set {n} not in table; available: {names}')
    ok = lambda x: x['cat'] == 'correct'
    both = [e for e in rows if ok(e[a.base]) and ok(e[a.cmp])]

    cache = pickle.load(open(a.cache, 'rb')) if a.cache and os.path.exists(a.cache) else {}
    todo = sorted({e[k]['href'] for e in both for k in (a.base, a.cmp)} - set(cache))
    if todo:
        print(f'parsing {len(todo)} logs ...', file=sys.stderr)
        with Pool(a.jobs, initializer=init_worker, initargs=(a.zips,)) as p:
            for href, res in p.imap_unordered(parse_run, todo, chunksize=50):
                cache[href] = res
        if a.cache:
            pickle.dump(cache, open(a.cache, 'wb'))

    pairs = []
    missing = 0
    for e in both:
        rb, rc = cache.get(e[a.base]['href']), cache.get(e[a.cmp]['href'])
        if rb is None or rc is None:
            missing += 1
            continue
        pairs.append((e, rb, rc))

    print(f'{a.cmp} (cmp) vs {a.base} (base): {len(both)} tasks solved correctly by both, '
          f'{len(pairs)} with parsable logs ({missing} without)')
    print()
    print(summary('walltime', [(e[a.base]['wall'], e[a.cmp]['wall']) for e, _, _ in pairs], a.min_time))
    print(summary('solve time (without pre/post)', [(rb['solve'], rc['solve']) for _, rb, rc in pairs], a.min_time))
    ob = [e[a.base]['wall'] - rb['solve'] for e, rb, _ in pairs]
    oc = [e[a.cmp]['wall'] - rc['solve'] for e, _, rc in pairs]
    print(f'{"overhead (wall - solve)":34} base median {statistics.median(ob):.2f}s  cmp median {statistics.median(oc):.2f}s  '
          f'median diff {statistics.median(c - b for b, c in zip(ob, oc)):+.3f}s  mean diff '
          f'{statistics.mean(c - b for b, c in zip(ob, oc)):+.3f}s')

    print('\nsolve time by base solve time:')
    for lo, hi in [(0, 1), (1, 5), (5, 30), (30, 100), (100, 300), (300, 1e9)]:
        sub = [(rb['solve'], rc['solve']) for _, rb, rc in pairs if lo <= rb['solve'] < hi]
        print('  ' + summary(f'[{lo}, {hi if hi < 1e9 else "inf"}) s', sub, a.min_time))

    print('\nsolve time by deciding worker (same worker in both runs):')
    groups = defaultdict(list)
    for _, rb, rc in pairs:
        key = rb['source'] if rb['source'] == rc['source'] else f'{rb["source"]} -> {rc["source"]}'
        groups[key].append((rb['solve'], rc['solve']))
    for key, sub in sorted(groups.items(), key=lambda kv: -len(kv[1]))[:12]:
        print('  ' + summary(key, sub, a.min_time))

    print('\nsolve time by number of toolchains (base):')
    for t, c in sorted(Counter(rb['toolchains'] for _, rb, _ in pairs).items()):
        sub = [(rb['solve'], rc['solve']) for _, rb, rc in pairs if rb['toolchains'] == t]
        print('  ' + summary(f'{t} toolchain(s)', sub, a.min_time))

    if a.csv:
        with open(a.csv, 'w', newline='') as f:
            w = csv.writer(f)
            w.writerow(['task', 'expected', 'base_wall', 'base_solve', 'base_source', 'base_toolchains',
                        'cmp_wall', 'cmp_solve', 'cmp_source', 'cmp_toolchains'])
            for e, rb, rc in pairs:
                w.writerow([e['task'], e['expected'], e[a.base]['wall'], round(rb['solve'], 3), rb['source'],
                            rb['toolchains'], e[a.cmp]['wall'], round(rc['solve'], 3), rc['source'],
                            rc['toolchains']])
        print(f'\nwrote {a.csv}')


if __name__ == '__main__':
    main()
