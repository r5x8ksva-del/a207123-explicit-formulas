# -*- coding: utf-8 -*-
"""探索 13：p_d(2d+1+m)、p_d(2d+2+n) 的单项式系数符号；模式计数若干族的闭式。"""
from math import factorial, lcm
from fractions import Fraction
from c4lib import *
from explore4_patterns import pattern_counts
KR = 140
NR = N_table_rec(KR)
def fit(d):
    ks = list(range(KR - 2 * d, KR + 1))
    return interpolate(ks, [Dval(NR, k, d) for k in ks])
for d in range(0, 13):
    p = fit(d)
    for sh in (2 * d + 1, 2 * d + 2, d + 1, 2 * d):
        ps = pcompose_shift(p, sh)
        den = 1
        for c in ps:
            den = lcm(den, Fraction(c).denominator)
        cs = [int(c * den) for c in reversed(ps)]
        allpos = all(c > 0 for c in cs)
        if sh in (2 * d + 1,) or d <= 3:
            print('d=%d shift=%d  den=%d  allpos=%s  num(desc)=%s' % (d, sh, den, allpos, cs if d <= 5 else '...'))
        elif not allpos:
            print('d=%d shift=%d not all positive' % (d, sh))
for d in range(1, 7):
    M = pattern_counts(d)
    df = lambda n: 1 if n <= 0 else n * df(n - 2)
    print(d, M.get((2*d-1,0)), df(2*d-1), M.get((2*d+1,2)), M.get((2*d+2,d+1)), d*factorial(d+1)//2, M.get((2*d-2,0)), 4*(d-1)*df(2*d-3) if d>=2 else None)
