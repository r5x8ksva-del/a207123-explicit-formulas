# -*- coding: utf-8 -*-
"""探索 8：用 Humbert（合流 Appell）函数 Phi_1 写出整张表 F 的闭式，并按定义展开对照 DP。

Phi_1(al,be;ga;X,Y) = sum_{m,n} (al)_{m+n} (be)_m / ((ga)_{m+n} m! n!) X^m Y^n。
候选 (I)  ：F = e^a/(1-x) * [ 1F1(-lam;1-lam;-a) + x^2 ( Phi_1(-lam,2;1-lam;t,-a) - Phi_1(-lam,1;1-lam;t,-a) ) ]
候选 (II) ：F = 1/(1-x) * [ 1F1(1;1-lam;a) + x^2 ( (1-t)^{-2} Phi_1(1,2;1-lam;-t/(1-t),a) - (1-t)^{-1} Phi_1(1,1;1-lam;-t/(1-t),a) ) ]
a = -t/x^3，lam = (1-x)/x^3。
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c3a_lib import *
from laurent import Lau
from fractions import Fraction
from math import factorial, comb

K, M = 40, 16
CAP = K + 3 * M + 12
t0 = time.time()
T = U_fast_table(K, M)

lam = Lau.poly([1, -1], CAP, shift=-3)
ONE = Lau.poly([1], CAP)
ZERO = Lau(0, [], CAP)
inv_1mx = Lau.poly([1, -1], CAP).inv()


def poch_L(base_shift, n):
    """(c - lam)_n，c = base_shift：prod_{i=0}^{n-1} (c + i - lam)。"""
    p = ONE
    for i in range(n):
        p = p * (Lau.poly([base_shift + i], CAP) - lam)
    return p


def poch_int(b, n):
    r = 1
    for i in range(n):
        r *= b + i
    return r


def xpow(e, c=1):
    return Lau.poly([c], CAP, shift=e)


# 预计算 (1-lam)_N 的逆、(-lam)_N
inv_poch1 = [poch_L(1, N).inv() for N in range(M + 1)]
pochm = [poch_L(0, N) for N in range(M + 1)]          # (-lam)_N

# ---------- 候选 (I) ----------
# 各因子按 t 的幂展开成「t^M 系数 = Laurent 级数」的列表
def series_e_a():
    # e^a，a = -t/x^3：t^n 系数 (-1)^n x^{-3n}/n!
    return [xpow(-3 * n, Fraction((-1) ** n, factorial(n))) for n in range(M + 1)]


def series_phi1_I(be):
    """Phi_1(-lam, be; 1-lam; X=t, Y=-a)，Y = t/x^3：t^{m+n} 系数累加。"""
    out = [ZERO] * (M + 1)
    for m in range(M + 1):
        for n in range(M + 1 - m):
            N = m + n
            coef = Fraction(poch_int(be, m), factorial(m) * factorial(n))
            term = pochm[N] * inv_poch1[N] * xpow(-3 * n, coef)      # X^m = t^m，Y^n = x^{-3n} t^n
            out[N] = out[N] + term
    return out


def mul_series(A, B):
    out = [ZERO] * (M + 1)
    for i in range(M + 1):
        for j in range(M + 1 - i):
            out[i + j] = out[i + j] + A[i] * B[j]
    return out


ea = series_e_a()
P0, P1, P2 = series_phi1_I(0), series_phi1_I(1), series_phi1_I(2)
inner = [P0[N] + xpow(2) * (P2[N] - P1[N]) for N in range(M + 1)]
FI = mul_series(ea, inner)
okI = True
for N in range(M + 1):
    L = FI[N] * inv_1mx
    if L.v is not None and L.v < 0:
        okI = False; print('I: negative powers at t^%d' % N)
    for k in range(K + 1):
        if L.coeff(k) != T[k][N]:
            okI = False; print('I: mismatch k=%d m=%d' % (k, N)); break
print('(I) e^a/(1-x)[1F1(-lam;1-lam;-a) + x^2(Phi1(-lam,2;..)-Phi1(-lam,1;..))] == DP (k<=%d,m<=%d): %s  %.1fs'
      % (K, M, okI, time.time() - t0))

# ---------- 候选 (II) ----------
t1 = time.time()


def series_X_pow(m):
    """X^m，X = -t/(1-t)：t^{m+r} 系数 (-1)^m C(m+r-1, r)（m>=1），m=0 时为 1。"""
    out = [Fraction(0)] * (M + 1)
    if m == 0:
        out[0] = Fraction(1)
        return out
    for r in range(M + 1 - m):
        out[m + r] = Fraction((-1) ** m * comb(m + r - 1, r))
    return out


def series_phi1_II(be):
    """Phi_1(1, be; 1-lam; X=-t/(1-t), Y=a)，a^n：(-1)^n x^{-3n} t^n。"""
    out = [ZERO] * (M + 1)
    for m in range(M + 1):
        Xm = series_X_pow(m)
        for n in range(M + 1 - m):
            N = m + n
            coef = Fraction(factorial(N) * poch_int(be, m), factorial(m) * factorial(n))
            base = inv_poch1[N] * xpow(-3 * n, coef * (-1) ** n)
            for d in range(M + 1):
                if Xm[d] and d + n <= M:
                    out[d + n] = out[d + n] + base * Xm[d]
    return out


def series_1mt_pow(be):
    return [Fraction(comb(be + p - 1, p)) for p in range(M + 1)]


def mul_scalar_series(A, s):
    out = [ZERO] * (M + 1)
    for i in range(M + 1):
        for j in range(M + 1 - i):
            if s[j]:
                out[i + j] = out[i + j] + A[i] * s[j]
    return out


Q1 = mul_scalar_series(series_phi1_II(1), series_1mt_pow(1))
Q2 = mul_scalar_series(series_phi1_II(2), series_1mt_pow(2))
# 1F1(1;1-lam;a)：t^n 系数 (-1)^n x^{-3n}/(1-lam)_n
F11 = [inv_poch1[n] * xpow(-3 * n, (-1) ** n) for n in range(M + 1)]
okII = True
negfree = True
for N in range(M + 1):
    L = (F11[N] + xpow(2) * (Q2[N] - Q1[N])) * inv_1mx
    if L.v is not None and L.v < 0:
        okII = False; print('II: negative powers at t^%d' % N)
    for k in range(K + 1):
        if L.coeff(k) != T[k][N]:
            okII = False; print('II: mismatch k=%d m=%d' % (k, N)); break
    for Q in (Q1, Q2):
        if Q[N].v is not None and Q[N].v < 0:
            negfree = False
print('(II) 1/(1-x)[1F1(1;1-lam;a) + x^2((1-t)^-2 Phi1(1,2;1-lam;-t/(1-t),a) - (1-t)^-1 Phi1(1,1;..))] == DP: %s ; '
      'each Phi1 term already free of negative x-powers: %s  %.1fs' % (okII, negfree, time.time() - t1))
