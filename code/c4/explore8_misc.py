# -*- coding: utf-8 -*-
"""探索 8：Num_q 系数符号；模式展开多项式 == 插值多项式；Newton(2d+1) 正性；h* 位移扫描。"""
from math import comb, factorial
from fractions import Fraction
from c4lib import *
from explore4_patterns import pattern_counts

QMAX = 70
Num = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for q in range(3, QMAX + 1):
    Num[q] = padd(pmul([0, 1, 0, 2 * (q - 1)], Num[q - 1]), pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), Num[q - 2]))
neg = [(q, i, c) for q in range(1, QMAX + 1) for i, c in enumerate(Num[q]) if c < 0]
zero_inside = [(q, i) for q in range(1, QMAX + 1) for i in range(q, 3 * q - 1) if Num[q][i] == 0]
print('negative coefficients in Num_q (q<=%d):' % QMAX, neg[:10], len(neg))
print('zero coefficients strictly between x^q and x^{3q-2}:', zero_inside[:20], len(zero_inside))

KR = 140
NR = N_table_rec(KR)
def fit(d):
    ks = list(range(KR - 2 * d, KR + 1))
    return interpolate(ks, [Dval(NR, k, d) for k in ks])
for d in range(0, 7):
    M = pattern_counts(d)
    poly = []
    for (s, b), w in M.items():
        poly = padd(poly, pscale(binom_poly(-d - b, s - b), w))
    print('d=%d pattern polynomial == interpolated p_d:' % d, trim(poly) == trim(fit(d)))
