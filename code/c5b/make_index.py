# -*- coding: utf-8 -*-
"""由 logs/c5b_fetch.log 与快照内容生成 data/oeis/INDEX.md（查询 URL、时间、HTTP、命中条目）。"""
import os
import re
import json

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
OEIS = os.path.join(ROOT, 'data', 'oeis')
LOG = os.path.join(ROOT, 'logs', 'c5b_fetch.log')

with open(os.path.join(HERE, 'search_terms.json'), encoding='utf-8') as f:
    META = json.load(f)

ENTRY_DESC = {
    'A207118': 'n×3 数组（A207123 第 3 列）', 'A207119': 'n×4（第 4 列）', 'A207120': 'n×5（第 5 列）',
    'A207121': 'n×6（第 6 列）', 'A207122': 'n×7（第 7 列）', 'A207123': '二维表 T(n,k)',
    'A038718': 'R_k 候选（第 1 行）', 'A084990': 'U_3 候选', 'A326247': 'U_4 候选',
    'A207069': 'A207123 第 2 行（%Y 所指）', 'A207070': 'A207123 第 3 行（%Y 所指）',
    'A002620': 'A207123 第 1 列（%Y：A002620(n+2)）', 'A030179': 'A207123 第 2 列（%Y：A030179(n+2)）',
    'A207117': 'A207123 对角线', 'A207124': '第 4 行', 'A207125': '第 5 行', 'A207126': '第 6 行',
    'A207127': '第 7 行',
}


def summarize(fname):
    path = os.path.join(OEIS, fname)
    with open(path, encoding='utf-8') as f:
        txt = f.read()
    if fname.startswith('b'):
        ns = [int(l.split()[0]) for l in txt.splitlines() if l.strip() and not l.startswith('#')]
        return 'b 文件 A%s' % fname[1:7], 'n=%d..%d（%d 项）' % (min(ns), max(ns), len(ns))
    show = re.search(r'^(Showing \d+-\d+ of \d+|No results\.)', txt, re.M)
    ids = re.findall(r'^%I (A\d{6})', txt, re.M)
    head = show.group(1) if show else '?'
    if fname in META and META[fname].get('terms'):
        desc = META[fname]['desc']
    elif fname in META:
        desc = META[fname]['desc']
    elif re.match(r'A\d{6}\.txt', fname):
        desc = '条目原文 %s：%s' % (fname[:7], ENTRY_DESC.get(fname[:7], ''))
    else:
        desc = ''
    hits = ' '.join(ids) if ids else '无'
    return desc, '%s；命中：%s' % (head, hits)


rows = []
with open(LOG, encoding='utf-8') as f:
    for line in f:
        parts = line.rstrip('\n').split('\t')
        if len(parts) < 5:
            continue
        ts, name, code, size, url = parts[:5]
        desc, res = summarize(name)
        rows.append((ts, name, url, code, size, desc, res))

urls = [r[2] for r in rows]
assert len(urls) == len(set(urls)), '有 URL 被重复抓取'

out = []
out.append('# OEIS 只读快照索引（c5b）')
out.append('')
out.append('- 方式：Git Bash 下 `curl` 直接访问 oeis.org（条目 `search?q=id:A......&fmt=text`、搜索 `search?q=<逗号分隔项>&fmt=text`、b 文件 `/A....../b......txt`）；未使用 agent-reach 或任何第三方代理；没有发帖、提交或联系任何人。')
out.append('- 每个 URL 只取一次（`code/c5b/fetch.sh` 先查 `logs/c5b_fetch.log`，出现过即跳过），请求间隔 2 秒。')
out.append('- 总请求数：%d（上限 80），全部 HTTP %s。' % (len(rows), '/'.join(sorted(set(r[3] for r in rows)))))
out.append('- 搜索项全部由 `code/c5b/build_list2.py`、`build_list5.py` 从 core 高度 DP 结果程序化生成（见 `code/c5b/search_terms.json`），没有手抄。')
out.append('- OEIS 的逗号分隔搜索要求各项按给定顺序**相邻**出现（按绝对值匹配，故带符号版本也会命中）。')
out.append('- 解读、证明与结论等级见 `notes/c5b.md`；离线核对见 `code/checks/check_c5b.py`（不联网，只读本目录快照）。')
out.append('')
out.append('| # | 时间 (UTC) | 快照文件 | 查询 URL | HTTP | 字节 | 内容 | 结果 |')
out.append('|---|---|---|---|---|---|---|---|')
for i, (ts, name, url, code, size, desc, res) in enumerate(rows, 1):
    out.append('| %d | %s | `%s` | %s | %s | %s | %s | %s |' % (i, ts, name, url, code, size, desc, res))
out.append('')
out.append('## 命中汇总')
out.append('')
pos = [(r[1], r[6]) for r in rows if r[1].startswith('search_') and 'No results' not in r[6]]
neg = [r[1] for r in rows if r[1].startswith('search_') and 'No results' in r[6]]
out.append('有命中的搜索：')
for n, res in pos:
    out.append('- `%s`：%s' % (n, res))
out.append('')
out.append('无命中的搜索（%d 个）：%s' % (len(neg), '、'.join('`%s`' % n for n in neg)))
out.append('')
with open(os.path.join(OEIS, 'INDEX.md'), 'w', encoding='utf-8', newline='\n') as f:
    f.write('\n'.join(out) + '\n')
print('INDEX.md rows:', len(rows), 'positive searches:', len(pos), 'negative:', len(neg))
