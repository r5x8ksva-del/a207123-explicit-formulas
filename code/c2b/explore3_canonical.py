# -*- coding: utf-8 -*-
"""探索 3：u = x^3/(1-x) 型的规范分解。
因 Q((x)) 是 Q((u)) 上以 {1, x, x^2} 为基的 3 维空间，G_m (1-x)^{m+1} = F0(u) + x F1(u) + x^2 F2(u) 唯一，
于是 U_k(m) = sum_s sum_{r=0}^2 f_{r,s}(m) C(k+m-r-2s, m+s)（三角可解，k=3s+r 时新未知数系数为 1）。
这里用三角解从 DP 数据求 f_{r,s}(m)，再看是否有闭式。同样对 E 部分（截断块部分）做。"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
from formulas import *
import core

K, M = 33, 8
T = core.U_fast_table(K, M)

def solve_canon(vals, m):
    """vals[k] (k=0..K)，返回 f[(r,s)]。"""
    f = {}
    for k in range(len(vals)):
        known = sum(c * binom(k + m - r - 2 * s, m + s) for (r, s), c in f.items())
        s, r = divmod(k, 3)
        f[(r, s)] = vals[k] - known      # 系数 C(m+s, m+s) = 1
    return f

for m in range(0, M + 1):
    vals = [T[k][m] for k in range(K + 1)]
    f = solve_canon(vals, m)
    smax = (K + 1) // 3 - 1
    print('m=%d' % m)
    for r in range(3):
        print('   f_%d,s :' % r, [f[(r, s)] for s in range(smax + 1)])
    print('   S(m+s,m):', [stirling2(m + s, m) for s in range(smax + 1)])

print()
print('E part only (ascent-ending):')
for m in range(0, M + 1):
    tot, asc = refined_dp(K, m)
    vals = [sum(asc[k]) for k in range(K + 1)]
    f = solve_canon(vals, m)
    smax = (K + 1) // 3 - 1
    print('m=%d' % m)
    for r in range(3):
        print('   e_%d,s :' % r, [f[(r, s)] for s in range(smax + 1)])
