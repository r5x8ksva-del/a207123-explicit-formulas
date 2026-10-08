# -*- coding: utf-8 -*-
"""探索（2026-10-08，notes/13 注 5.2）：N(k,q) 的「每个 i 两个原子」表示。

F_q 在纤维 i（b_i 的根）上的部分分式元素（K_i 中）：
  E_{q,i} = sum_{M=i}^{q-1} (-1)^{q-1-M} C(q,M+1) (-1)^{M-i}/(i!(M-i)!) x^{-3M} W~_i 。
两原子表示存在 ⇔ 对每个 1<=i<=q-1，E_{q,i} 落在某个 span(x^a, x^a')（a≠a'）里（与 notes/12 定理 3 同样的约化）。
先在 |a|,|a'|<=R 内精确搜索；q=3 时纤维 1 的元素若在窗口内无解，再用 notes/08 的筛法 + l 进（check_b2 的实现）证明。
用法： py -3.14 code/tableB/explore/explore_b5_twoatom.py
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from check_b4 import kmul, coords  # noqa: E402
import check_b2 as B2  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
R = 40


def xpow(i, a):
    e = [Fr(1), Fr(0), Fr(0)]
    step = [Fr(0), Fr(1), Fr(0)] if a >= 0 else [Fr(1), Fr(0), Fr(i)]
    for _ in range(abs(a)):
        e = kmul(e, step, i)
    return e


def elem(q, i):
    W = coords(i)
    acc = [Fr(0)] * 3
    for M in range(i, q):
        cf = Fr((-1) ** (q - 1 - M) * comb(q, M + 1) * (-1) ** (M - i), factorial(i) * factorial(M - i))
        t = kmul(W, xpow(i, -3 * M), i)
        acc = [acc[r] + cf * t[r] for r in range(3)]
    return acc


def det3(u, v, w):
    return (u[0] * (v[1] * w[2] - v[2] * w[1]) - u[1] * (v[0] * w[2] - v[2] * w[0]) + u[2] * (v[0] * w[1] - v[1] * w[0]))


def window_pairs(E, i):
    X = {a: xpow(i, a) for a in range(-R, R + 1)}
    return [(a, b) for a in range(-R, R + 1) for b in range(a + 1, R + 1) if det3(E, X[a], X[b]) == 0]


t0 = time.time()
for q in range(2, 8):
    res = {}
    for i in range(1, q):
        res[i] = window_pairs(elem(q, i), i)
    print('q=%d：%s' % (q, {i: (len(v), v[:4]) for i, v in res.items()}), flush=True)
print('time %.1fs' % (time.time() - t0))

# q=3 纤维 1：E = 常数 * x^-6 W~_1 (1+3x^3)；用 W~_1(1+3x^3) 代替（差一个 x 的幂与非零常数，不影响「是否落在两个幂张成的子空间」）
E31 = elem(3, 1)
print('q=3 纤维 1 的元素（约化坐标）：', E31)


def e31_mod(l):
    # W~_1 * (1 + 3 x^3) mod l，用 check_b2 的模 l 运算（纤维 1：x^3 = 1 - x）
    w = B2.elem_mod(1, 'U', l)
    one_plus = [(1 + 3 * v) % l for v in [1, 0, 0]]
    x3 = B2.powm(3, 1, l)
    f = [(1 + 3 * x3[0]) % l, (3 * x3[1]) % l, (3 * x3[2]) % l]
    return B2.mulm(w, f, 1, l)


surv, tabs = B2.sieve('U', (1,), elems={1: e31_mod})
print('q=3 纤维 1 筛法（T=%d，CERT[1]=%s）：幸存 %d 类' % (B2.T, B2.CERT[1], len(surv)))
if surv:
    print('  前 20 个：', surv[:20])
unr, used = B2.padic('U', (1,), {k: v for k, v in tabs.items()})
print('  l 进未解决 %d 个（前 20 个 %s），首中 %s' % (len(unr), unr[:20], dict(sorted(used.items()))))
print('time %.1fs' % (time.time() - t0))
