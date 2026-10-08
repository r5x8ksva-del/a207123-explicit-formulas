# -*- coding: utf-8 -*-
"""探索（2026-10-08）：纤维 i 上 η 模 l 的阶的分解，用来挑筛法的模数 T（notes/12 注 2.7）。
用法： py -3.14 code/tableB/explore/explore_b4_twoatom_orders.py [i=3] [L=60000]
对每个候选 T 列出阶整除 T 的素数。
"""
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import check_b2 as B2  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

i = int(sys.argv[1]) if len(sys.argv) > 1 else 3
L = int(sys.argv[2]) if len(sys.argv) > 2 else 60000


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b'\x00\x00'
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = bytearray(len(s[p * p::p]))
    return [p for p in range(n + 1) if s[p]]


def factor(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def order(i, l):
    # 群阶的倍数：lcm(l-1, l^2-1, l^3-1) 的因子里找最小的
    N = (l - 1) * (l + 1) * (l * l + l + 1)
    fN = factor(N)
    o = N
    for p, e in fN.items():
        for _ in range(e):
            if o % p == 0 and B2.powm(o // p, i, l) == [1, 0, 0]:
                o //= p
            else:
                break
    assert B2.powm(o, i, l) == [1, 0, 0]
    return o


res = []
for l in primes_upto(L):
    if l == 2 or i % l == 0 or B2.disc(i) % l == 0:
        continue
    o = order(i, l)
    fo = factor(o)
    if max(fo) <= 13 if fo else True:
        res.append((l, o, fo))
print('纤维 %d：l<=%d 中阶 13-光滑的素数 %d 个' % (i, L, len(res)))
for l, o, fo in res:
    print('  l=%d  P=%d  %s' % (l, o, fo))
cands = [2520, 5040, 7560, 10080, 13860, 15120, 20160, 25200, 27720, 30240, 32760, 36036, 40320, 55440]
for T in cands:
    sel = [(l, o) for (l, o, _) in res if T % o == 0]
    print('T=%d：%d 个 %s' % (T, len(sel), sel))
