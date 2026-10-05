# -*- coding: utf-8 -*-
"""探索 12：nu_j(q) 的整系数分子；pi_i(q)=[x^i]P_{q-1} 的多项式形式（GKP 6.44）。"""
from math import factorial, comb
from fractions import Fraction
from c4lib import *
QMAX = 70
Num = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for q in range(3, QMAX + 1):
    Num[q] = padd(pmul([0, 1, 0, 2 * (q - 1)], Num[q - 1]), pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), Num[q - 2]))
def coef(p, i):
    return p[i] if 0 <= i < len(p) else 0
from math import lcm
for j in range(0, 9):
    qs = list(range(QMAX - 2 * j - 3, QMAX + 1))
    poly = interpolate(qs, [coef(Num[q], q + j) for q in qs])
    den = 1
    for c in poly:
        den = lcm(den, Fraction(c).denominator)
    print('nu_%d = (%s)/%d' % (j, [int(c * den) for c in reversed(poly)], den))
# pi_i polys
def euler2(n):
    E = [[0] * (n + 1) for _ in range(n + 1)]
    E[0][0] = 1
    for a in range(1, n + 1):
        for k in range(0, a):
            E[a][k] = (k + 1) * E[a - 1][k] + ((2 * a - 1 - k) * E[a - 1][k - 1] if k >= 1 else 0)
    return E
E = euler2(10)
print('<<n,k>> rows:', [E[n][:n] for n in range(1, 6)])
