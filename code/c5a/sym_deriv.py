# -*- coding: utf-8 -*-
"""c5a: 符号计算 h_k^{(d)}(1)（d<=3）与 B_d(k)（d<=3）的多项式（用已证明的 D(k,e) 多项式）。"""
import os, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from polylib import padd, pmul, pscale, trim
from explore_poly import poly_shift, fmt_poly
p0 = [F(2)]
p1 = [F(-4), F(-1), F(1)]
p2 = [F(164, 4), F(-98, 4), F(43, 4), F(-10, 4), F(1, 4)]
p3 = [F(11088, 24), F(-17392, 24), F(8560, 24), F(-2225, 24), F(331, 24), F(-27, 24), F(1, 24)]
P = [p0, p1, p2, p3]
def binom_poly(shift, r):   # C(k+shift, r) as poly in k
    p = [F(1)]
    for i in range(r):
        p = pmul(p, [F(shift - i), F(1)])
    from math import factorial
    return pscale(p, F(1, factorial(r)))
from math import factorial
for d in range(1, 4):
    tot = []
    for e in range(0, d + 1):
        tot = padd(tot, pscale(pmul(binom_poly(-1 - e, d - e), P[e]), (-1) ** e))
    tot = pscale(tot, factorial(d))
    print('h^(%d)(1) =' % d, fmt_poly(tot), ' ; times 2:', [c * 2 for c in tot])
# etilde
et = [[F(1)], [F(-3, 2), F(1, 2)], pscale(pmul([F(-2), F(1)], [F(-13), F(3)]), F(1, 24)),
      pscale(pmul([F(-3), F(1)], [F(8), F(-7), F(1)]), F(1, 48))]
for d in range(1, 4):
    B = []
    for e in range(0, d + 1):
        B = padd(B, pscale(pmul(P[e], poly_shift(et[d - e], -e)), (-1) ** (d - e)))
    print('B_%d(k) =' % d, fmt_poly(B), ' ; times %d:' % [1, 1, 12, 24][d], [c * [1, 1, 12, 24][d] for c in B])
