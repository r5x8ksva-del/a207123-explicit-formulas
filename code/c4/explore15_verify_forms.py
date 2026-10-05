# -*- coding: utf-8 -*-
"""探索 15：核对 c4.md 表 1 的 m=k-2d-1 形式与表 6 的调和数形式。"""
from math import factorial
from fractions import Fraction
from c4lib import *
KR = 140
NR = N_table_rec(KR)
def fit(d):
    ks = list(range(KR - 2 * d, KR + 1))
    return interpolate(ks, [Dval(NR, k, d) for k in ks])
MFORM = {0: (1, [2]), 1: (1, [1, 5, 2]), 2: (4, [1, 10, 43, 82, 124]),
         3: (24, [1, 15, 121, 673, 2554, 6212, 4200]),
         4: (192, [1, 20, 234, 2160, 15137, 75452, 244500, 411488, 405312]),
         5: (1920, [1, 25, 380, 4890, 50653, 398817, 2340990, 9829580, 28039016, 54223968, 40805760])}
ok = True
for d, (den, cs) in MFORM.items():
    q = [Fraction(c, den) for c in reversed(cs)]
    if trim(q) != trim(pcompose_shift(fit(d), 2 * d + 1)):
        ok = False; print('mform mismatch', d)
print('table 1 m-forms:', ok)
QMAX = 40
Num = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for qq in range(3, QMAX + 1):
    Num[qq] = padd(pmul([0, 1, 0, 2 * (qq - 1)], Num[qq - 1]), pmul(pscale(pshift(b_poly(qq - 2), 3), qq - 1), Num[qq - 2]))
def H(n, r=1):
    return sum(Fraction(1, i ** r) for i in range(1, n + 1))
ok = True
for qq in range(1, QMAX + 1):
    f = factorial(qq - 1)
    a = lambda j: Num[qq][3 * qq - 2 - j] if 0 <= 3 * qq - 2 - j < len(Num[qq]) else 0
    if a(2) != f * (qq - 1 + H(qq - 1)): ok = False; print('j2', qq)
    if a(3) != (qq - 1) * f * (H(qq - 1) - 1): ok = False; print('j3', qq)
    if a(4) != f * (qq - 1 - H(qq - 1) + (H(qq - 1) ** 2 - H(qq - 1, 2)) / 2): ok = False; print('j4', qq)
print('table 6 harmonic forms (q<=40):', ok)
