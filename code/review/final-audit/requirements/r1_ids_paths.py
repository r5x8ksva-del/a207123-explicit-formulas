# -*- coding: utf-8 -*-
"""最终审计（requirements 方向）r1：只读检查。
(1) report_parts 中引用的「模块.核对id」是否都在 logs/verify_all_final.log 以 PASS 出现；
(2) report_parts 中引用的文件路径（logs/、notes/、code/、data/ 开头）是否存在；
(3) 统计 01_summary.md 非空行数；
(4) 列出所有【已证明】/【已验证】/【猜想】/【未完成】/【已否定】标注的位置。
不修改任何文件。
"""
import os
import re
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
PARTS = os.path.join(ROOT, 'notes', 'report_parts')
names = sorted(n for n in os.listdir(PARTS) if n.endswith('.md'))
texts = {n: open(os.path.join(PARTS, n), encoding='utf-8').read() for n in names}

# (0) 报告.md 是否等于拼接
joined = '\n\n'.join(texts[n].strip() for n in names) + '\n'
rep = open(os.path.join(ROOT, '报告.md'), encoding='utf-8').read()
print('[0] 报告.md == concat(report_parts):', joined == rep, len(joined), len(rep))

# (1) ids
log = open(os.path.join(ROOT, 'logs', 'verify_all_final.log'), encoding='utf-8').read().splitlines()
passed = set()
for ln in log:
    m = re.match(r'PASS (\S+)', ln)
    if m:
        passed.add(m.group(1))
print('[1] PASS ids in log:', len(passed))
areas = ('c0', 'c1', 'c2a', 'c2b', 'c3a', 'c3b', 'c4', 'c5a', 'c5b', 'rv', 'rv2')
pat = re.compile(r'(?<![A-Za-z0-9_/\\])(' + '|'.join(areas) + r')\.([A-Za-z0-9][A-Za-z0-9_\-.]*[A-Za-z0-9])')
cited = {}
for n, t in texts.items():
    for a, cid in pat.findall(t):
        if cid == 'md' or cid.endswith('.md'):
            continue
        cited.setdefault((a, cid), set()).add(n)
miss = []
for (a, cid), where in sorted(cited.items()):
    ok = cid in passed or (a + '.' + cid) in passed
    if not ok and '..' in cid:
        stem = cid.split('..')[0].rstrip('0123456789')
        ok = any(p.startswith(stem) for p in passed)
    if not ok:
        miss.append((a, cid, sorted(where)))
print('[1] cited ids:', len(cited), ' missing:', len(miss))
for x in miss:
    print('    MISSING', x)
# 找 "GCD1/2/3" 这类简写
for n, t in texts.items():
    for m in re.finditer(r'C3B-GCD1/2/3', t):
        print('    shorthand in', n, '-> check C3B-GCD2, C3B-GCD3:', 'C3B-GCD2' in passed, 'C3B-GCD3' in passed)
# 日志中有、报告从未引用的 id
cited_full = set()
for (a, cid) in cited:
    cited_full.add(cid)
    cited_full.add(a + '.' + cid)
never = sorted(p for p in passed if p not in cited_full)
print('[1] log PASS ids never cited in report (%d):' % len(never))
for p in never:
    print('    ', p)

# (2) paths
ppat = re.compile(r'((?:logs|notes|code|data)/[A-Za-z0-9_\-./<>一-鿿]+)')
seen = {}
for n, t in texts.items():
    for m in ppat.finditer(t):
        p = m.group(1).rstrip('.,;:）)、，。')
        seen.setdefault(p, set()).add(n)
print('[2] referenced paths:', len(seen))
for p, where in sorted(seen.items()):
    if '<' in p:
        print('    (template)', p, sorted(where))
        continue
    full = os.path.join(ROOT, p)
    print('    %-60s %s %s' % (p, 'OK' if os.path.exists(full) else 'MISSING', sorted(where)))
# 不带目录前缀的日志名，例如 "review_r-c5a_s7_rr.log"
bare = re.compile(r'(?<![/A-Za-z0-9_\-])((?:review|audit|c[0-9][a-z]?|rv2?|phase\d)_[A-Za-z0-9_\-.]+\.log)')
for n, t in texts.items():
    for m in bare.finditer(t):
        p = 'logs/' + m.group(1)
        print('    bare log %-50s %s %s' % (m.group(1), 'OK' if os.path.exists(os.path.join(ROOT, p)) else 'MISSING', n))

# (3) summary lines
s = texts['01_summary.md'].splitlines()
ne = [l for l in s if l.strip()]
print('[3] 01_summary.md non-empty lines:', len(ne), '(incl. heading);', 'items:', sum(1 for l in ne if re.match(r'\d+\.', l)))

# (4) grade labels
gpat = re.compile(r'【(已证明|已验证|猜想|未完成|已否定)[^】]*】')
cnt = {}
for n, t in texts.items():
    for m in gpat.finditer(t):
        cnt[m.group(1)] = cnt.get(m.group(1), 0) + 1
print('[4] grade label counts:', cnt)
for n, t in texts.items():
    for m in re.finditer(r'【已验证[^】]*】', t):
        ctx = t[max(0, m.start() - 60):m.end() + 40].replace('\n', ' ')
        print('    [%s] %s' % (n, ctx))
