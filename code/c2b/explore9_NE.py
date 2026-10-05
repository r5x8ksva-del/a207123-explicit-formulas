# -*- coding: utf-8 -*-
"""探索 9：
 (1) N^E(k,q) 的骨架三重和：
     N^E(k,q) = sum_{s>=1} sum_p sum_{h0} R'(p,s,h0) C(q-1-h0, p-1-h0) C(k-1-2s+p-h0, s+q-2-h0)，
     R'(p,s,h0) = 端点恰为 {0..p-1}、最小头为 h0 的 s 弧骨架数（暴力枚举）。
 (2) R(p,s) = sum_k <<s,k>> C(2s-2-k, 2s-p)（二阶 Euler 数；s>=1）。
"""
import sys, os
from math import comb
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import core
from formulas import refined_dp, binom
from explore6_surjective import arc_systems, R_ie

K, QQ = 13, 10
T = core.U_fast_table(K, QQ)
E = {}
for m in range(0, QQ + 1):
    tot, asc = refined_dp(K, m)
    E[m] = [sum(asc[k]) for k in range(K + 1)]
NE = {q: [sum((-1) ** (q - i) * comb(q, i) * (0 if i == 0 else E[i - 1][k]) for i in range(q + 1)) for k in range(K + 1)]
      for q in range(1, QQ + 1)}

Rp = Counter()
for s in range(1, 5):
    for p in range(2, 2 * s + 1):
        for sy in arc_systems(p, s):
            if set(x for arc in sy for x in arc) == set(range(p)):
                h0 = min(v for v, a in sy)
                Rp[(p, s, h0)] += 1

def NE_formula(k, q):
    tot = 0
    for (p, s, h0), r in Rp.items():
        tot += r * binom(q - 1 - h0, p - 1 - h0) * binom(k - 1 - 2 * s + p - h0, s + q - 2 - h0)
    return tot

ok = all(NE_formula(k, q) == NE[q][k] for q in range(1, QQ + 1) for k in range(0, K + 1))
print('(1) N^E skeleton triple sum == DP inclusion-exclusion, k<=%d q<=%d (s<=4 suffices since 3s<=k+1):' % (K, QQ), ok)

# (2) second-order Eulerian
E2 = {(0, 0): 1}
def eul2(n, k):
    if (n, k) in E2:
        return E2[(n, k)]
    if n == 0 or k < 0 or k >= n:
        return 1 if (n == 0 and k == 0) else 0
    v = (k + 1) * eul2(n - 1, k) + (2 * n - 1 - k) * eul2(n - 1, k - 1)
    E2[(n, k)] = v
    return v

ok2 = all(R_ie(p, s) == sum(eul2(s, k) * binom(2 * s - 2 - k, 2 * s - p) for k in range(0, s))
          for s in range(1, 12) for p in range(0, 2 * s + 3))
print('(2) R(p,s) = sum_k <<s,k>> C(2s-2-k, 2s-p), 1<=s<=11:', ok2)
print('    <<s,k>> rows:', [[eul2(s, k) for k in range(s)] for s in range(1, 6)])
