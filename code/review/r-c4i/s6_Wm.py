# -*- coding: utf-8 -*-
"""s6：独立复核 C4-2 的推论 G_m = W_m/P_m，W_m = 1 + x^2 Σ_{j=1}^m j P_{j-1}（P_m = Π_{i=0}^m (1-x-i x^3)）。
U_k(m) 取自自写高度 DP（rlib.U_column），比较 P_m·G_m 与 W_m 的系数到 x^K（m<=MM）。
另：b_m G_m = G_{m-1} + m x^2 （逐系数）。
"""
import sys, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rlib import U_column

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
t0 = time.time()
KK, MM = 90, 24


def mul(a, b, n):
    r = [0] * n
    for i, x in enumerate(a[:n]):
        if x:
            for j, y in enumerate(b[:n - i]):
                r[i + j] += x * y
    return r


P = {-1: [1]}
for m in range(0, MM + 1):
    P[m] = mul(P[m - 1] + [0] * 4, [1, -1, 0, -m], len(P[m - 1]) + 3)
W = {-1: [1]}
for m in range(0, MM + 1):
    w = list(W[m - 1]) + [0] * (len(P[m - 1]) + 3)
    for i, c in enumerate(P[m - 1]):
        w[i + 2] += m * c
    while w and w[-1] == 0:
        w.pop()
    W[m] = w
G = {m: U_column(m, KK) for m in range(0, MM + 1)}
G[-1] = [1] + [0] * KK
ok1 = True
ok2 = True
for m in range(0, MM + 1):
    pr = mul(P[m] + [0] * (KK + 1), G[m], KK + 1)
    want = (W[m] + [0] * (KK + 1))[:KK + 1]
    if pr != want:
        ok1 = False
    lhs = mul([1, -1, 0, -m] + [0] * KK, G[m], KK + 1)
    rhs = list(G[m - 1][:KK + 1])
    rhs[2] += m
    if lhs != rhs:
        ok2 = False
print(('OK  ' if ok1 else 'BAD ') + 'C4-2 推论：P_m * Σ_k U_k(m) x^k == W_m（模 x^%d），0<=m<=%d（U 取自自写 DP）' % (KK + 1, MM))
print(('OK  ' if ok2 else 'BAD ') + 'C4-2 推论：(1-x-m x^3) G_m == G_{m-1} + m x^2（模 x^%d），0<=m<=%d' % (KK + 1, MM))
print('SUMMARY s6 ok=%d bad=%d runtime=%.1fs' % (ok1 + ok2, 2 - ok1 - ok2, time.time() - t0))
