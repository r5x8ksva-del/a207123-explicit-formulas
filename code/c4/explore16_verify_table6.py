# -*- coding: utf-8 -*-
"""探索 16：核对 c4.md 表 6（j=5..8）因式分解写法与实际系数。"""
from math import factorial
from fractions import Fraction as F
from c4lib import *
QMAX = 40
Num = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for q in range(3, QMAX + 1):
    Num[q] = padd(pmul([0, 1, 0, 2 * (q - 1)], Num[q - 1]), pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), Num[q - 2]))
c = [[0] * (QMAX + 2) for _ in range(QMAX + 2)]
c[0][0] = 1
for n in range(1, QMAX + 2):
    for k in range(1, n + 1):
        c[n][k] = (n - 1) * c[n - 1][k] + c[n - 1][k - 1]
ok = True
for q in range(1, QMAX + 1):
    C = lambda i: c[q][i]
    a = lambda j: Num[q][3 * q - 2 - j] if 0 <= 3 * q - 2 - j < len(Num[q]) else 0
    forms = {
        5: F((q - 1) * (q - 2), 2) * C(1) - (q - 2) * C(2) + (q - 2) * C(3),
        6: -F((q - 1) * (5 * q - 6), 4) * C(1) + F(q * q + q - 4, 2) * C(2) - q * C(3) + C(4),
        7: F(3 * (q - 1) * (q - 2), 4) * C(1) - (q - 2) * C(2) - (q - 3) * C(3) + (q - 3) * C(4),
        8: F((q - 1) * (2 * q * q - q + 54), 24) * C(1) - F(2 * q * q - 4 * q + 5, 2) * C(2) + F(q * q + 3 * q - 8, 2) * C(3) - 2 * (q - 1) * C(4) + C(5),
    }
    for j, v in forms.items():
        if v != a(j):
            ok = False; print('mismatch', q, j, v, a(j))
print('table 6 factored forms j=5..8, q<=40:', ok)
