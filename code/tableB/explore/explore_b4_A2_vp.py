# -*- coding: utf-8 -*-
"""探索（2026-10-08）：A_p^(r)（r=0,1,2）的 p 进赋值，p<=211；以及 (a,a') 两原子搜索的计数（|a|,|a'|<=40，i<=8）。"""
import os
import sys
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from check_b4 import coords, vp, is_prime, kmul  # noqa: E402
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
rows = []
for p in range(3, 212):
    if is_prime(p):
        A = coords(p)
        t = -3 * (p - 1) // 2
        rows.append((p, vp(A[0], p) - t, vp(A[1], p) - t, vp(A[2], p) - t))
print('(p, v0-t, v1-t, v2-t)：', rows[:6], '...')
print('v2-t 的取值：', sorted({r[3] for r in rows}), '；p=3：', rows[0])
print('v2-t==1 的 p 范围：', all(r[3] == 1 for r in rows if r[0] >= 5))
def det3(u, v, w):
    return (u[0] * (v[1] * w[2] - v[2] * w[1]) - u[1] * (v[0] * w[2] - v[2] * w[0]) + u[2] * (v[0] * w[1] - v[1] * w[0]))
R = 40
for i in range(1, 9):
    X = {0: [Fr(1), Fr(0), Fr(0)]}
    for a in range(1, R + 1):
        X[a] = kmul(X[a - 1], [Fr(0), Fr(1), Fr(0)], i)
        X[-a] = kmul(X[-a + 1], [Fr(1), Fr(0), Fr(i)], i)
    W = coords(i)
    pairs = [(a, b) for a in range(-R, R + 1) for b in range(a + 1, R + 1) if det3(W, X[a], X[b]) == 0]
    print('i=%d：%d 对 %s' % (i, len(pairs), pairs[:16]))
