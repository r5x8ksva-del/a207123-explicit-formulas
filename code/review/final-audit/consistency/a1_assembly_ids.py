# -*- coding: utf-8 -*-
"""Final audit (consistency): read-only checks.
1. 报告.md == strip-join of notes/report_parts/*.md (as assemble_report.py does)
2. every cited check id -> PASS line in logs/verify_all_final.log (print the PASS line text)
3. ⑤ result table vs. tail of logs/verify_all_final.log
4. existence of every file path mentioned in the report (logs/..., notes/..., code/..., data/...)
"""
import os, re, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
sys.stdout.reconfigure(encoding='utf-8')
PARTS = os.path.join(ROOT, 'notes', 'report_parts')
names = sorted(n for n in os.listdir(PARTS) if n.endswith('.md'))
chunks = [open(os.path.join(PARTS, n), encoding='utf-8').read().strip() for n in names]
text = '\n\n'.join(chunks) + '\n'
rep = open(os.path.join(ROOT, '报告.md'), encoding='utf-8').read()
print('[1] report == assembled parts:', rep == text, len(rep), len(text))

log = open(os.path.join(ROOT, 'logs', 'verify_all_final.log'), encoding='utf-8').read()
passlines = {}
for ln in log.splitlines():
    m = re.match(r'(PASS|FAIL) (\S+) ?(.*)', ln)
    if m:
        passlines[m.group(2)] = (m.group(1), m.group(3))
areas = ('c0', 'c1', 'c2a', 'c2b', 'c3a', 'c3b', 'c4', 'c5a', 'c5b', 'rv', 'rv2')
pat = re.compile(r'(?<![A-Za-z0-9_/\\])(' + '|'.join(areas) + r')\.([A-Za-z0-9*][A-Za-z0-9_\-.*]*[A-Za-z0-9*]|\*)')
# which part file each id appears in
cited = {}
for n, ch in zip(names, chunks):
    for a, c in pat.findall(ch):
        if c == 'md' or c.endswith('.md'):
            continue
        cited.setdefault((a, c), []).append(n)
print('[2] cited ids:', len(cited))
for (a, c), where in sorted(cited.items()):
    key = None
    if c in passlines:
        key = c
    elif a + '.' + c in passlines:
        key = a + '.' + c
    if key:
        st, desc = passlines[key]
        print('  %-28s %-4s [%s] %s' % (a + '.' + c, st, ','.join(sorted(set(where))), desc[:400]))
    else:
        print('  %-28s ???? [%s]' % (a + '.' + c, ','.join(sorted(set(where)))))

# ids in log by module
mods = {}
cur = None
for ln in log.splitlines():
    m = re.match(r'>>> check_(\S+)\.py', ln)
    if m:
        cur = m.group(1)
    m = re.match(r'(PASS|FAIL) (\S+)', ln)
    if m and cur:
        mods.setdefault(cur, []).append(m.group(2))
print('[2b] per-module counts in log:', {k: len(v) for k, v in mods.items()}, sum(len(v) for v in mods.values()))
citedset = set()
for (a, c) in cited:
    citedset.add(c); citedset.add(a + '.' + c)
uncited = [(k, i) for k, v in mods.items() for i in v if i not in citedset and (k + '.' + i) not in citedset]
print('[2c] ids in log never cited in report:', len(uncited))
for k, i in uncited:
    print('   ', k, i, '|', passlines[i][1][:200])

# [3] table
tbl_rep = re.search(r'```\n(area .*?OVERALL: PASS)\n```', rep, re.S).group(1)
idx = log.rfind('area     pass')
tbl_log = log[idx:].strip()
print('[3] table identical:', tbl_rep.strip() == tbl_log)
if tbl_rep.strip() != tbl_log:
    import difflib
    for d in difflib.unified_diff(tbl_rep.strip().splitlines(), tbl_log.splitlines(), lineterm=''):
        print('   ', d)

# [4] file paths
paths = set(re.findall(r'(?:logs|notes|code|data)/[A-Za-z0-9_\-./<>一-鿿]+', rep))
print('[4] paths mentioned:', len(paths))
for p in sorted(paths):
    pp = p.rstrip('.。，、；：）)')
    if '<' in pp:
        print('   (template)', pp); continue
    full = os.path.join(ROOT, pp)
    print('   %-6s %s' % ('OK' if os.path.exists(full) else 'MISSING', pp))
