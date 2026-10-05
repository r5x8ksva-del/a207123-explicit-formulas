# -*- coding: utf-8 -*-
"""探索 11：正项全历史递推
 Num_q = x Num_{q-1} + sum_{m=2}^{q-2} (q-1)!/m! x^{3(q-1-m)} (q-1-m+x) Num_m
         + (q-1)! ((q-2) x^{3q-5} + q x^{3q-4} + x^{3q-2}),  q>=3
 以及 Y^{(c)}_q = c Num_{q-1} + b_{q-2} Num_{q-2} 的递推 Y^{(c)}_q = (1+(c-1)x) Num_{q-2} + c(q-2) x^3 Y^{(2-1/c)}_{q-1}。"""
from math import factorial
from fractions import Fraction
from c4lib import *
QMAX = 40
Num = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for q in range(3, QMAX + 1):
    Num[q] = padd(pmul([0, 1, 0, 2 * (q - 1)], Num[q - 1]), pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), Num[q - 2]))
ok = True
for q in range(3, QMAX + 1):
    s = pshift(Num[q - 1], 1)
    for m in range(2, q - 1):
        s = padd(s, pscale(pmul(pshift([q - 1 - m, 1], 3 * (q - 1 - m)), Num[m]), factorial(q - 1) // factorial(m)))
    bd = [0] * (3 * q - 1)
    bd[3 * q - 5] += q - 2; bd[3 * q - 4] += q; bd[3 * q - 2] += 1
    s = padd(s, pscale(bd, factorial(q - 1)))
    if trim(s) != trim(Num[q]):
        ok = False; print('fail q=', q)
print('positive full-history recurrence 3<=q<=%d:' % QMAX, ok)
ok = True
for q in range(4, 30):
    for c in (Fraction(1), Fraction(3, 2), Fraction(2), Fraction(7, 3), Fraction(5)):
        lhs = padd(pscale(Num[q - 1], c), pmul(b_poly(q - 2), Num[q - 2]))
        c2 = 2 - 1 / c
        Yq1 = padd(pscale(Num[q - 2], c2), pmul(b_poly(q - 3), Num[q - 3]))
        rhs = padd(pmul([1, c - 1], Num[q - 2]), pscale(pshift(Yq1, 3), c * (q - 2)))
        if trim(lhs) != trim(rhs):
            ok = False; print('Y fail', q, c)
print('Y^(c) recurrence 4<=q<30:', ok)
