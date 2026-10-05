# -*- coding: utf-8 -*-
"""探索 6：Num_q 的低次系数 nu_j(q)=[x^{q+j}]Num_q（q 的多项式）与高次系数 a_{q,j}=[x^{3q-2-j}]Num_q
（用第一类 Stirling 数 c(q,i) 拟合）。Num_q 用已证明的三项递推计算（并与 DP 结果在 q<=16 已对过）。"""
from math import factorial, comb
from fractions import Fraction
from c4lib import *

QMAX = 70
Num = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for q in range(3, QMAX + 1):
    Num[q] = padd(pmul([0, 1, 0, 2 * (q - 1)], Num[q - 1]), pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), Num[q - 2]))


def coef(p, i):
    return p[i] if 0 <= i < len(p) else 0


# ---------- 低次 ----------
print('low coefficients nu_j(q) = [x^{q+j}] Num_q : polynomial fit and threshold')
for j in range(0, 9):
    qs = list(range(QMAX - 2 * j - 3, QMAX + 1))
    poly = interpolate(qs, [coef(Num[q], q + j) for q in qs])
    deg = len(poly) - 1
    thr = None
    for q in range(QMAX, 0, -1):
        if pval(poly, q) != coef(Num[q], q + j):
            thr = q + 1
            break
    else:
        thr = 1
    print(' j=%d deg=%d threshold q>=%d  coeffs=%s' % (j, deg, thr, [str(c) for c in poly]))
    print('     exceptions:', [(q, coef(Num[q], q + j), str(pval(poly, q))) for q in range(1, thr)])

# ---------- 高次：用 c(q,i) 拟合 ----------
CM = QMAX + 2
c1 = [[0] * (CM + 1) for _ in range(CM + 1)]
c1[0][0] = 1
for n in range(1, CM + 1):
    for k in range(1, n + 1):
        c1[n][k] = (n - 1) * c1[n - 1][k] + c1[n - 1][k - 1]


def solve(rows, rhs):
    """精确高斯消元，最小二乘不需要：rows 多于未知数时要求相容。返回解或 None。"""
    m = len(rows[0])
    A = [[Fraction(x) for x in r] + [Fraction(b)] for r, b in zip(rows, rhs)]
    piv = []
    r = 0
    for c in range(m):
        p = None
        for i in range(r, len(A)):
            if A[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = 1 / A[r][c]
        A[r] = [x * inv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    for i in range(r, len(A)):
        if A[i][m] != 0:
            return None
    sol = [Fraction(0)] * m
    for i, c in enumerate(piv):
        sol[c] = A[i][m]
    return sol


print('\nhigh coefficients a_{q,j} = sum_{i,r} lam_{i,r} q^r c(q,i)')
for j in range(0, 9):
    found = False
    for I in range(1, j // 2 + 3):
        for R in range(0, j // 2 + 2):
            basis = [(i, r) for i in range(1, I + 1) for r in range(0, R + 1)]
            qs = list(range(1, QMAX + 1))
            rows = [[q ** r * c1[q][i] for (i, r) in basis] for q in qs]
            rhs = [coef(Num[q], 3 * q - 2 - j) for q in qs]
            sol = solve(rows, rhs)
            if sol is not None:
                terms = ['%s*q^%d*c(q,%d)' % (s, r, i) for s, (i, r) in zip(sol, basis) if s != 0]
                print(' j=%d (I=%d,R=%d): a = %s' % (j, I, R, ' + '.join(terms)))
                found = True
                break
        if found:
            break
    if not found:
        print(' j=%d: no fit' % j)
