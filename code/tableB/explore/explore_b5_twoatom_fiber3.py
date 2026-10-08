# -*- coding: utf-8 -*-
"""探索（2026-10-08，notes/13 注 5.2；复核者 s12-b4t3 的建议）：N(·,q)（4<=q<=QMAX）在纤维 3 上的两原子条件。

F_q 在纤维 3 的部分分式元素 E_{q,3} = sum_{M=3}^{q-1} (-1)^{q-1-M} C(q,M+1) (-1)^{M-3}/(3!(M-3)!) x^{-3M} W~_3。
乘以非零有理数 3!(q-4)! 与单位 x^{3(q-1)}（不影响「是否落在两个 x 的幂张成的子空间里」），得到整系数多项式
  S_q(x) = W~_3(x) * sum_{M=3}^{q-1} (-1)^{q-1-M} (-1)^{M-3} C(q,M+1) (q-4)!/(M-3)! x^{3(q-1-M)} 。
两原子条件 ⇔ 存在 (n,b)、b≠0 使 D_3(n,b)=0（元素换成 S_q）。用 check_b2 的筛法与 l 进实现，证书素数同 notes/12 引理 3.1。
用法： py -3.14 code/tableB/explore/explore_b5_twoatom_fiber3.py [QMAX=30] [T=3360]
"""
import os
import sys
import time
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import check_b2 as B2  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 30
T = int(sys.argv[2]) if len(sys.argv) > 2 else 3360
ALL = [(5, 20), (13, 84), (31, 480), (71, 70), (97, 96), (193, 96), (449, 448), (673, 672)]
CERT3 = [(l, P) for (l, P) in ALL if T % P == 0]
B2.T = T
B2.CERT[3] = CERT3


def S_poly(q):
    """S_q 的整系数（低次在前）。"""
    W = [0] * 12
    W[0] = 1
    for j in range(1, 4):
        W[3 * j + 2] += j * B2.falling(3, j)
    L = [0] * (3 * (q - 4) + 1)
    for M in range(3, q):
        cf = (-1) ** (q - 1 - M) * (-1) ** (M - 3) * comb(q, M + 1) * (factorial(q - 4) // factorial(M - 3))
        L[3 * (q - 1 - M)] += cf
    out = [0] * (len(W) + len(L) - 1)
    for a, x in enumerate(W):
        if x:
            for b, y in enumerate(L):
                out[a + b] += x * y
    return out


def elem_mod_factory(coeffs):
    def f(l):
        acc = [0, 0, 0]
        for d, c in enumerate(coeffs):
            if c % l:
                v = B2.powm(d, 3, l)
                acc = [(acc[t] + c * v[t]) % l for t in range(3)]
        return acc
    return f


t0 = time.time()
print('T=%d，证书素数 %s' % (T, CERT3), flush=True)
bad = []
for q in range(4, QMAX + 1):
    co = S_poly(q)
    surv, tabs = B2.sieve('U', (3,), elems={3: elem_mod_factory(co)})
    unr, used = B2.padic('U', (3,), tabs)
    ok = not surv and not unr
    if not ok:
        bad.append(q)
    print('q=%d：筛法幸存 %d 类，l 进未解决 %d 个，首中 %s  %s  (%.1fs)'
          % (q, len(surv), len(unr), {l: c for (_, l), c in sorted(used.items())}, 'OK' if ok else 'FAIL', time.time() - t0),
          flush=True)
print('未排除的 q：%s' % bad)
print('time %.1fs' % (time.time() - t0))
