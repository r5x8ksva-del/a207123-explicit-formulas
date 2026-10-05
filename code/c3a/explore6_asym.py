# -*- coding: utf-8 -*-
"""探索 6：
(i) 点 (21/100, -1/20) 用 170 位精度核对 I - S = x^{-3} K e^a a^lambda（预测约 1e-62）。
(ii) x -> 0+ 的渐近：I(x,t) 与 sum_{k<K} f_k(t) x^k（f_k = sum_m U_k(m) t^m）比较；S 在 |t| 较大时偏离。
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import getcontext, Decimal as D
from fractions import Fraction as Fr
from numerics import *
from c3a_lib import U_fast_table
from math import comb


def fk_at(t0, Kmax):
    """f_k(t0)，k<=Kmax，用 PDE 的 x^k 系数在 t0 处做 Taylor 递推（精确 Fraction）。"""
    J = Kmax // 3 + 3
    d = {}
    def get(k, j):
        if k < 0 or j < 0:
            return Fr(0)
        return d[(k, j)]
    for k in range(Kmax + 1):
        Jk = (Kmax - k) // 3 + 2
        for j in range(Jk + 1):
            g = Fr(0)
            if k == 0 and j == 0:
                g = Fr(1)
            if k == 2:
                g = t0 * (j + 1) / (1 - t0) ** (j + 2) + (Fr(j) / (1 - t0) ** (j + 1) if j >= 1 else 0)
            val = get(k, j - 1) + get(k - 1, j) + (t0 * (j + 1) * get(k - 3, j + 1) + j * get(k - 3, j) if k >= 3 else 0) + g
            d[(k, j)] = val / (1 - t0)
    return [d[(k, 0)] for k in range(Kmax + 1)]


# 自检：f_k(t0) 对照 DP 的 h_k
T = U_fast_table(20, 30)
t0 = Fr(-1, 2)
fk = fk_at(t0, 20)
ok = True
for k in range(21):
    h = [sum((-1) ** j * comb(k + 1, j) * T[k][i - j] for j in range(0, min(i, k + 1) + 1)) for i in range(max(k, 1))]
    val = sum(Fr(c) * t0 ** i for i, c in enumerate(h)) / (1 - t0) ** (k + 1)
    if val != fk[k]:
        ok = False
print('f_k(t0) Taylor recursion vs DP h_k (k<=20):', ok)

# (i) 高精度点
getcontext().prec = 170
x, t = Fr(21, 100), Fr(-1, 20)
tt = time.time()
I1, e1, l1 = I_val(x, t, with_g=True)
S1, m1 = S_val(x, t, with_g=True)
Kx = K_val(x, with_g=True)
gap = predicted_gap(x, t, Kx)
PI = pi_dec()
lam = (1 - x) / x ** 3
G1 = gamma_neg_reflect(dec(lam), PI)
G2 = K_val(x, with_g=False)
print('(i) x=21/100 t=-1/20 prec 170 (%.1fs)' % (time.time() - tt))
print('   I-S  = %.30E' % (I1 - S1))
print('   pred = %.30E' % gap)
print('   rel residual = %.3E' % ((I1 - S1 - gap) / gap))
print('   Gamma(-lam): reflect %.30E ; regularized %.30E' % (G1, G2))
print('   K(x) = %.30E' % Kx)
print('   quad err est %s level %d' % (e1, l1))

# (ii) 渐近比较
getcontext().prec = 60
for (x, t) in [(Fr(21, 100), Fr(-1, 2)), (Fr(1, 4), Fr(-1, 2)), (Fr(1, 5), Fr(-3, 10))]:
    tt = time.time()
    lam = (1 - x) / x ** 3
    if lam.denominator == 1:
        print('skip integer lambda'); continue
    I1, e1, l1 = I_val(x, t, with_g=True)
    S1, m1 = S_val(x, t, with_g=True)
    fk = fk_at(t, 150)
    xd = dec(x)
    part = D(0)
    best = None
    rows = []
    for k in range(151):
        term = dec(fk[k]) * xd ** k
        part += term
        diff = abs(I1 - part)
        if best is None or diff < best[1]:
            best = (k, diff, abs(term))
        if k % 15 == 0:
            rows.append('k=%d |term|=%.2E |I-partial|=%.2E' % (k, abs(term), diff))
    print('(ii) x=%s t=%s lambda=%.3f (%.1fs): I=%s' % (x, t, float(lam), time.time() - tt, +I1))
    print('     S = %.6E   (sum_m t^m G_m(x), %d terms)' % (S1, m1))
    for r in rows:
        print('     ' + r)
    print('     best truncation k=%d: |I-partial|=%.3E (term size %.3E)' % best)
