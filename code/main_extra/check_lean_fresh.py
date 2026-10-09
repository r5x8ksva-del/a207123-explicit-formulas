# -*- coding: utf-8 -*-
"""Check, without running Lean, that the last Lean build is up to date with the current sources.

Rebuilding costs about 8 GB of memory and half a minute per module on this machine (27 modules plus the
root, Axioms and Checks), so instead of recompiling we check what the last build left behind:
  1. every module (A207123/X.lean and the root A207123.lean) has an .olean written after the source was
     last modified;
  2. every module's .olean was written after the .olean of each module it imports, so nothing was
     compiled against an older version of a dependency;
  3. the last run of Axioms.lean and of Checks.lean in logs/lean_mem.log exited 0 and started after the
     file was last modified and after the newest .olean;
  4. the output of that Axioms run (logs/lean_axioms_*.log) has one line per `#print axioms` in
     Axioms.lean, in the same order, each listing only propext, Classical.choice and Quot.sound, and its
     scan of all declarations reports no other axiom;
  5. git reports no uncommitted change under lean/ (skipped when the folder is not in a git work tree).
lean_mem.log records the end of each run in UTC (the Bash clock) and its duration in whole seconds.

Usage:  py -3.14 code/main_extra/check_lean_fresh.py [lean_dir [lean_mem.log [axioms.log]]]
(exit code 1 on any FAIL; without axioms.log the most recently written logs/lean_axioms_*.log is used: names with the
same date and different suffixes do not sort by time)
"""
import datetime as dt
import glob
import hashlib
import os
import re
import subprocess
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
IMPORT = re.compile(r'^import A207123\.(\w+)', re.M)
RUN = re.compile(r'^(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d) \| (\S+)[^|\n]*\| exit (\d+) \| (\d+)s', re.M)
PRINT = re.compile(r'^#print axioms (\S+)', re.M)
DEPENDS = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.M)
SCAN = re.compile(r'出现过的公理：\[([^\]]*)\]；依赖其他公理的声明：(\d+) 个')
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

results = []


def check(ok, label, detail=''):
    results.append(ok)
    print('%s %s%s' % ('PASS' if ok else 'FAIL', label, ('  ' + detail) if detail else ''))


def mtime(path):
    return dt.datetime.fromtimestamp(os.path.getmtime(path), dt.timezone.utc).replace(tzinfo=None)


def fmt(t):
    return t.strftime('%Y-%m-%d %H:%M:%S')


def last_run(memlog, name):
    """(start, end, exit code) of the last run of `name` in lean_mem.log; start is rounded down by 1 s."""
    runs = [m for m in RUN.finditer(memlog) if m.group(2) == name]
    if not runs:
        return None
    m = runs[-1]
    end = dt.datetime.strptime(m.group(1), '%Y-%m-%d %H:%M:%S')
    return end - dt.timedelta(seconds=int(m.group(4)) + 1), end, int(m.group(3))


def main(lean_dir, memlog_path, axioms_path):
    build = os.path.join(lean_dir, '.lake', 'build', 'lib', 'lean')
    modules = {'A207123': os.path.join(lean_dir, 'A207123.lean')}
    for p in sorted(glob.glob(os.path.join(lean_dir, 'A207123', '*.lean'))):
        modules['A207123.' + os.path.basename(p)[:-5]] = p

    # 1 and 2: sources against .olean files.
    olean = {}
    for mod, src in modules.items():
        o = os.path.join(build, *mod.split('.')) + '.olean'
        olean[mod] = mtime(o) if os.path.exists(o) else None
    for mod, src in modules.items():
        if olean[mod] is None:
            check(False, '%-26s no .olean' % mod)
            continue
        deps = ['A207123.' + d for d in IMPORT.findall(open(src, encoding='utf-8').read())]
        stale_src = mtime(src) >= olean[mod]
        stale_dep = [d for d in deps if olean.get(d) is None or olean[d] >= olean[mod]]
        check(not stale_src and not stale_dep, '%-26s source %s < olean %s; %d imports older'
              % (mod, fmt(mtime(src)), fmt(olean[mod]), len(deps) - len(stale_dep)),
              ('imports not older: ' + ', '.join(stale_dep)) if stale_dep else '')
    newest = max(t for t in olean.values() if t is not None)

    # 3: the two files that are run, not compiled to .olean.
    memlog = open(memlog_path, encoding='utf-8').read()
    runs = {}
    for name in ('Axioms.lean', 'Checks.lean'):
        src = os.path.join(lean_dir, name)
        r = runs[name] = last_run(memlog, name)
        if r is None:
            check(False, '%-26s no run in %s' % (name, os.path.basename(memlog_path)))
            continue
        start, end, code = r
        check(code == 0 and mtime(src) < start and newest < start,
              '%-26s last run %s..%s exit %d; source %s, newest olean %s'
              % (name, fmt(start), fmt(end), code, fmt(mtime(src)), fmt(newest)))

    # 4: the axioms printed by that Axioms run.
    names = PRINT.findall(open(os.path.join(lean_dir, 'Axioms.lean'), encoding='utf-8').read())
    out = open(axioms_path, encoding='utf-8').read()
    lines = DEPENDS.findall(out)
    r = runs.get('Axioms.lean')
    written = mtime(axioms_path)
    check(r is not None and r[0] <= written <= r[1] + dt.timedelta(seconds=60),
          '%-26s written %s, during or just after that run' % (os.path.basename(axioms_path), fmt(written)))
    check(['A207123.' + n if not n.startswith('A207123.') else n for n in names] == [n for n, _ in lines],
          '%-26s %d #print axioms lines, %d answers, same names in the same order'
          % ('Axioms.lean', len(names), len(lines)))
    extra = sorted({a.strip() for _, ax in lines for a in ax.split(',') if a.strip()} - STANDARD)
    check(not extra, '%-26s axioms used beyond propext, Classical.choice, Quot.sound: %s'
          % ('', ', '.join(extra) or 'none'))
    s = SCAN.search(out)
    scan_extra = sorted({a.strip() for a in s.group(1).split(',') if a.strip()} - STANDARD) if s else None
    check(s is not None and not scan_extra and s.group(2) == '0',
          '%-26s scan of all declarations: %s' % ('', s.group(0) if s else 'line not found'))

    # 5: git.
    try:
        g = subprocess.run(['git', '-C', lean_dir, 'status', '--porcelain', '--', '.'],
                           capture_output=True, text=True, encoding='utf-8')
        inside = subprocess.run(['git', '-C', lean_dir, 'rev-parse', '--show-prefix'],
                                capture_output=True, text=True, encoding='utf-8')
    except OSError:
        g = inside = None
    if g is None or g.returncode != 0 or inside.returncode != 0:
        print('SKIP git: %s is not in a git work tree' % lean_dir)
    else:
        changed = [l for l in g.stdout.splitlines() if l.strip()]
        check(not changed, 'git status of %s: %s' % (inside.stdout.strip() or '.',
              'clean' if not changed else '; '.join(changed[:5])))

    print('sha256 of the sources:')
    for path in [modules['A207123']] + [p for m, p in sorted(modules.items()) if m != 'A207123'] + \
            [os.path.join(lean_dir, 'Axioms.lean'), os.path.join(lean_dir, 'Checks.lean')]:
        print('  %s  %s' % (hashlib.sha256(open(path, 'rb').read()).hexdigest(), os.path.relpath(path, lean_dir)))
    nfail = results.count(False)
    print('%d checks: %d PASS, %d FAIL' % (len(results), len(results) - nfail, nfail))
    return 1 if nfail else 0


if __name__ == '__main__':
    a = sys.argv[1:]
    lean_dir = a[0] if len(a) > 0 else os.path.join(ROOT, 'lean')
    memlog = a[1] if len(a) > 1 else os.path.join(ROOT, 'logs', 'lean_mem.log')
    axioms = a[2] if len(a) > 2 else max(glob.glob(os.path.join(ROOT, 'logs', 'lean_axioms_*.log')), key=os.path.getmtime)
    sys.exit(main(lean_dir, memlog, axioms))
