# -*- coding: utf-8 -*-
"""探索 3：p_d 在负整数/特殊点的取值；缺陷 e_d(k)=D(k,d)-p_d(k) 的表；h*-向量（不同平移）。"""
from math import factorial
from c4lib import *

KR = 140
NR = N_table_rec(KR)
DMAX = 9


def fit(d):
    ks = list(range(KR - 2 * d, KR + 1))
    return interpolate(ks, [Dval(NR, k, d) for k in ks])


P = {d: fit(d) for d in range(DMAX + 1)}
print('p_d(j) for j=-8..2d+2')
for d in range(DMAX + 1):
    print(d, [str(pval(P[d], j)) for j in range(-8, 2 * d + 3)])

print('\ndefects e_d(k)=D(k,d)-p_d(k), k=0..2d+1 (listed from k=2d+1 downwards)')
for d in range(DMAX + 1):
    print(d, [str(Dval(NR, k, d) - pval(P[d], k)) for k in range(2 * d + 1, -1, -1)])


def hstar(p, deg, shift):
    """(1-x)^{deg+1} sum_{k>=0} p(k+shift) x^k 的系数。"""
    n = deg + 1 + 5
    s = [pval(p, k + shift) for k in range(n + deg + 2)]
    for _ in range(deg + 1):
        s = [s[i] - (s[i - 1] if i > 0 else 0) for i in range(len(s))]
    return trim(s)


print('\nh*-vectors of p_d(k+shift), shift = d+1, 2d+1, 2d+2, 2d+3')
for d in range(DMAX + 1):
    for sh in (d + 1, 2 * d + 1, 2 * d + 2, 2 * d + 3):
        print(d, sh, [str(a) for a in hstar(P[d], 2 * d, sh)])
