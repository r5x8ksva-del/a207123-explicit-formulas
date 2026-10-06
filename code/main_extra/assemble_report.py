# -*- coding: utf-8 -*-
"""把 notes/report_parts/*.md 按文件名顺序拼接成 报告.md（各节之间空一行）。

用法：py -3.14 code/main_extra/assemble_report.py
拼接后顺带检查：报告里出现的核对 id（形如 c2a.form_H、rv.rv-negzeros）是否都在 logs/verify_all_final.log 里以 PASS 出现。
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
PARTS = os.path.join(ROOT, 'notes', 'report_parts')
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

names = sorted(n for n in os.listdir(PARTS) if n.endswith('.md'))
chunks = [open(os.path.join(PARTS, n), encoding='utf-8').read().strip() for n in names]
text = '\n\n'.join(chunks) + '\n'
out = os.path.join(ROOT, '报告.md')
with open(out, 'w', encoding='utf-8') as f:
    f.write(text)
print('wrote %s from %d parts (%d chars)' % (out, len(names), len(text)))

# 核对 id 交叉检查
log = os.path.join(ROOT, 'logs', 'verify_all_final.log')
if os.path.exists(log):
    passed = set()
    for ln in open(log, encoding='utf-8'):
        m = re.match(r'PASS (\S+)', ln)
        if m:
            passed.add(m.group(1))
    areas = ('c0', 'c1', 'c2a', 'c2b', 'c3a', 'c3b', 'c4', 'c5a', 'c5b', 'rv', 'rv2', 'rv3')
    # 报告里写成「模块.核对id」；日志里有的模块打印裸 id（如 C1-sum、c3a-1f1-const），
    # 有的打印带前缀的 id（如 c2b.T1.bijection、c5b.U3），两种都认。
    pat = re.compile(r'(?<![A-Za-z0-9_/\\])(' + '|'.join(areas) + r')\.([A-Za-z0-9][A-Za-z0-9_\-.]*[A-Za-z0-9])')
    cited = sorted(set(pat.findall(text)))
    missing, n_ids = [], 0
    for area, cid in cited:
        if cid == 'md' or cid.endswith('.md'):      # 笔记文件名 notes/c4.md 之类
            continue
        n_ids += 1
        if cid in passed or (area + '.' + cid) in passed:
            continue
        # 区间写法，如 c5a-asym-m1..m8：只要前缀匹配到日志里的 id 即可
        if '..' in cid:
            stem = cid.split('..')[0].rstrip('0123456789')
            if any(p.startswith(stem) for p in passed):
                continue
        missing.append('%s.%s' % (area, cid))
    print('cited check ids: %d, not found as PASS in log: %d' % (n_ids, len(missing)))
    for x in missing:
        print('  MISSING', x)
    sys.exit(1 if missing else 0)
