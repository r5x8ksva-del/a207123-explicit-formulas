# -*- coding: utf-8 -*-
"""探索 5：(C7) 分子 Num_q = P_{q-1} * sum_k N(k,q) x^k。递推、gcd、低次/高次系数。"""
from math import factorial, comb
from fractions import Fraction
from c4lib import *

KD = 60
ND, T = N_table_dp(KD)
QMAX = 16

# Num_q from DP-derived N (series truncated at KD, Num_q has degree 3q-2 <= KD needs q <= 20)
Num = {}
for q in range(1, QMAX + 1):
    ser = [ND[k][q] if q <= k else 0 for k in range(KD + 1)]
    prod = series_mul(ser, P_poly(q - 1), KD + 1)
    prod = trim(prod)
    assert len(prod) - 1 <= 3 * q - 2, ('deg', q, len(prod))
    # 确认截断后剩余项为 0（说明是多项式）：检查 3q-1..KD
    Num[q] = prod
print('Num_1..4:', [Num[q] for q in range(1, 5)])

# 递推
ok = True
for q in range(3, QMAX + 1):
    rhs = padd(pmul([0, 1, 0, 2 * (q - 1)], Num[q - 1]), pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), Num[q - 2]))
    if trim(rhs) != trim(Num[q]):
        ok = False
print('3-term recurrence 3<=q<=%d:' % QMAX, ok)

# gcd with P_{q-1}
for q in range(1, QMAX + 1):
    g = pgcd(Num[q], P_poly(q - 1))
    gb = [(i, len(pgcd(Num[q], b_poly(i))) - 1) for i in range(0, q)]
    nz = [t for t in gb if t[1] > 0]
    print('q=%d deg gcd(Num_q,P_{q-1}) = %d ; nontrivial gcd with b_i: %s ; Num_q(1)=%s' % (
        q, len(g) - 1, nz, peval(Num[q], 1)))

# 低次系数 [x^{q+j}] Num_q
print('\nlow coefficients [x^{q+j}]Num_q, rows j, columns q=1..%d' % QMAX)
for j in range(0, 8):
    print(j, [Num[q][q + j] if q + j < len(Num[q]) else 0 for q in range(1, QMAX + 1)])

# 高次系数 a_{q,j} = [x^{3q-2-j}] Num_q
print('\nhigh coefficients a_{q,j}=[x^{3q-2-j}]Num_q, rows j, columns q=1..%d' % QMAX)
for j in range(0, 9):
    print(j, [Num[q][3 * q - 2 - j] if 0 <= 3 * q - 2 - j < len(Num[q]) else 0 for q in range(1, QMAX + 1)])
