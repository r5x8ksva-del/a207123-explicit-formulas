# -*- coding: utf-8 -*-
"""final-audit / math-c3: negative controls for a1_formal (perturbed formulas must FAIL)."""
import sys, os
from fractions import Fraction
from math import comb, factorial
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', '..', '..')))
sys.path.insert(0, HERE)
import core
from lser import L, rf, gbinom_neg
T = core.U_fast_table(30, 10)
K, M = 18, 6
REL = K + 3 * M + 6
def cml(c):
    cc = [Fraction(0)] * REL; cc[0] = Fraction(-1); cc[1] = Fraction(1); cc[3] = Fraction(c)
    return L(-3, cc)
def b_poly(i): return [1, -1, 0, -i]
# (1) kappa_j = j x^3 instead of j x^2  -> must fail
def sum1f1(kpow):
    ok = True
    for m in range(M + 1):
        tot = L(0, [0] * REL)
        for j in range(m + 1):
            n = m - j
            term = L.mono(-3 * n, (-1) ** n, REL)
            for i in range(n):
                term = term * cml(j + 1 + i).inv()
            term = term * L.poly(b_poly(j), REL).inv()
            if j >= 1:
                p = [0] * (kpow + 1); p[kpow] = j
                term = term * L.poly(p, REL)
            tot = tot + term
        ok &= all(tot.coeff(k) == T[k][m] for k in range(K + 1))
    return ok
print('kappa_j=j x^2 (true):', sum1f1(2), '| kappa_j=j x^3 (perturbed):', sum1f1(3))
# (2) Y_beta with b_i built from 1-x instead of A (A = 1-x+x^3) -> must fail
def ser_inv(p, K):
    p = [Fraction(a) for a in p] + [Fraction(0)] * (K + 1)
    r = [Fraction(0)] * (K + 1); r[0] = 1 / p[0]
    for k in range(1, K + 1):
        r[k] = -sum(p[j] * r[k - j] for j in range(1, k + 1)) / p[0]
    return r
def smul(p, q, K):
    r = [Fraction(0)] * (K + 1)
    for i, a in enumerate(p[:K + 1]):
        if a:
            for j in range(min(len(q), K + 1 - i)):
                r[i + j] += a * q[j]
    return r
def ybeta_ok(Apoly, Bpoly, beta, K=15, M=6):
    Y = [[Fraction(0)] * (K + 1) for _ in range(M + 1)]
    for N in range(M + 1):
        den = list(Apoly)
        for i in range(1, N + 1):
            bi = list(Bpoly) + [0] * 4; bi[3] -= i
            den = smul(den + [0] * 4, bi, K)
        dinv = ser_inv(den, K)
        for mm in range(N + 1):
            c = comb(N, mm) * rf(beta, mm)
            if c == 0 or 3 * mm > K: continue
            for r in range(M + 1 - N):
                cr = c * gbinom_neg(beta + mm, r)
                for k in range(K + 1 - 3 * mm):
                    Y[N + r][k + 3 * mm] += cr * dinv[k]
    for m in range(M + 1):
        AY = smul(Apoly, Y[m], K)
        for k in range(K + 1):
            val = AY[k] - (Y[m - 1][k] if m else 0) - (m * Y[m][k - 3] if k >= 3 else 0)
            if val != (gbinom_neg(beta, m) if k == 0 else 0):
                return False
    return True
print('Y_beta true b_i^(A):', ybeta_ok([1, -1, 0, 1], [1, -1, 0, 1], Fraction(2)), '| b_i from 1-x (perturbed):', ybeta_ok([1, -1, 0, 1], [1, -1], Fraction(2)),
      '| beta shift (1-t)^{-beta-1} wrong:', ybeta_ok([1, -1], [1, -1], Fraction(2)) and not ybeta_ok([1, -1], [1, -1, 0, 0, 0], Fraction(3)) )
