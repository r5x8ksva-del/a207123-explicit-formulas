# -*- coding: utf-8 -*-
"""探索 10：R'(p,s,h0) 的容斥公式，并把 N^E 骨架三重和的核对扩到 k<=30, q<=12。

R'(p,s,h0) = 端点恰为 {0..p-1}、最小头恰为 h0 的 s 弧骨架数。对未覆盖集 Z（h0∉Z，因 h0 是头）容斥：
删去 Z 后值域大小 w=p-|Z|，h0 的新序号 r0 = h0 - |Z∩[0,h0)|，「头 >= r0 且至少一个头 = r0」的骨架数
= h_s(r0..w-1) - h_s(r0+1..w-1)。按 z1=|Z∩[0,h0)|、z2=|Z∩(h0,p-1]| 分组：
R'(p,s,h0) = sum_{z1,z2} (-1)^{z1+z2} C(h0,z1) C(p-1-h0,z2) [h_s(h0-z1..p-1-z1-z2) - h_s(h0-z1+1..p-1-z1-z2)]。
"""
import sys, os, time
from math import comb
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import core
from formulas import refined_dp, binom, hcomp
from explore6_surjective import arc_systems, R_ie


def Rprime(p, s, h0):
    tot = 0
    for z1 in range(0, h0 + 1):
        for z2 in range(0, p - h0):
            w = p - z1 - z2
            r0 = h0 - z1
            tot += (-1) ** (z1 + z2) * comb(h0, z1) * comb(p - 1 - h0, z2) * (hcomp(s, r0, w - 1) - hcomp(s, r0 + 1, w - 1))
    return tot


t0 = time.time()
ok = True
for s in range(1, 5):
    for p in range(2, 2 * s + 1):
        cnt = Counter()
        for sy in arc_systems(p, s):
            if set(x for arc in sy for x in arc) == set(range(p)):
                cnt[min(v for v, a in sy)] += 1
        for h0 in range(0, p):
            if cnt[h0] != Rprime(p, s, h0):
                ok = False
                print('mismatch', p, s, h0, cnt[h0], Rprime(p, s, h0))
print("R'(p,s,h0) inclusion-exclusion == brute force (s<=4, p<=2s):", ok)
ok2 = all(sum(Rprime(p, s, h0) for h0 in range(p)) == R_ie(p, s) for s in range(1, 11) for p in range(2, 2 * s + 1))
print("sum_h0 R'(p,s,h0) == R(p,s) (s<=10):", ok2)

K, QQ = 30, 12
T = core.U_fast_table(K, QQ)
E = {}
for m in range(0, QQ + 1):
    tot, asc = refined_dp(K, m)
    E[m] = [sum(asc[k]) for k in range(K + 1)]
NE = {q: [sum((-1) ** (q - i) * comb(q, i) * (0 if i == 0 else E[i - 1][k]) for i in range(q + 1)) for k in range(K + 1)]
      for q in range(1, QQ + 1)}
RP = {}
for s in range(1, (K + 1) // 3 + 1):
    for p in range(2, 2 * s + 1):
        for h0 in range(1, p):
            v = Rprime(p, s, h0)
            if v:
                RP[(p, s, h0)] = v

def NE_formula(k, q):
    return sum(r * binom(q - 1 - h0, p - 1 - h0) * binom(k - 1 - 2 * s + p - h0, s + q - 2 - h0) for (p, s, h0), r in RP.items())

ok3 = all(NE_formula(k, q) == NE[q][k] for q in range(1, QQ + 1) for k in range(0, K + 1))
print('N^E skeleton triple sum (R\' by inclusion-exclusion) == DP, k<=%d q<=%d:' % (K, QQ), ok3)
print('elapsed %.1fs' % (time.time() - t0))
