# -*- coding: utf-8 -*-
"""T5.4(1)：b 文件与 a_k(n)=U_k(ceil(n/2))U_k(floor(n/2)) 的一致性（final-audit math-c4c5，离线快照）。"""
import os
import time

from alib import say, check, ROOT, write_log
from core import U_fast_column

t0 = time.time()


def bfile(aid):
    d = {}
    for line in open(os.path.join(ROOT, 'data', 'oeis', 'b%s.txt' % aid[1:]), encoding='utf-8'):
        line = line.strip()
        if line and not line.startswith('#'):
            n, v = line.split()[:2]
            d[int(n)] = int(v)
    return d


UC = {}


def U(k, m):
    if (m, k) not in UC:
        col = U_fast_column(m, 220)
        for kk, v in enumerate(col):
            UC[(m, kk)] = v
    return UC[(m, k)]


def a(k, n):
    return U(k, (n + 1) // 2) * U(k, n // 2)


bad = []
for k, aid in zip(range(3, 8), ['A207118', 'A207119', 'A207120', 'A207121', 'A207122']):
    bf = bfile(aid)
    for n, v in bf.items():
        if a(k, n) != v:
            bad.append((aid, n))
            break
for n, aid in zip(range(4, 8), ['A207124', 'A207125', 'A207126', 'A207127']):
    bf = bfile(aid)
    for k, v in bf.items():
        if a(k, n) != v:
            bad.append((aid, k))
            break
for n, aid in zip(range(2, 4), ['A207069', 'A207070']):
    bf = bfile(aid)
    for k, v in bf.items():
        if a(k, n) != v:
            bad.append((aid, k))
            break
bf = bfile('A207117')
for n, v in bf.items():
    if a(n, n) != v:
        bad.append(('A207117', n))
        break
# A207123：按反对角线读，同一反对角线内行号 n 递增
bf = bfile('A207123')
seq = []
s = 2
while len(seq) < len(bf):
    for n in range(1, s):
        seq.append(a(s - n, n))
    s += 1
ok123 = all(seq[i - 1] == bf[i] for i in bf)
check('T5.4.1-bfiles', not bad and ok123,
      'A207118–A207122（列 k=3..7，n<=210）、A207124–A207127 与 A207069/A207070（行 n=4..7、2..3，k<=210）、A207117（对角 n<=19）、'
      'A207123（%d 项，反对角线内 n 递增）全部 = U_k(ceil n/2)U_k(floor n/2); bad=%s' % (len(bf), bad[:3]))
say('elapsed %.1fs' % (time.time() - t0))
write_log('final_audit_math-c4c5_s7.log')
