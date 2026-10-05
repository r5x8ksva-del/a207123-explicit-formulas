# -*- coding: utf-8 -*-
"""探索 9：
(a) 一般 beta：L_A[Y] = (1-t)^{-beta} 的解 Y_beta = (1/A)(1-t)^{-beta} Phi_1(1,beta;1-lam_A;-t/(1-t),a)，lam_A = A/x^3；
    检查 L_A[Y_beta] == (1-t)^{-beta}（A = 1-x 与 1-x+x^3，beta = 0..4 以及 beta = 1/2, -3）。
(b) Ncal(x,y) = (1/(A(1+y))) [ (A+x^2) 1F1(1;-lam;yh) - 2x^2(1+y) Phi_1(1,1;-lam;-y,yh) + x^2(1+y)^2 Phi_1(1,2;-lam;-y,yh) ]，
    yh = -y/((1+y)x^3)，A = 1-x+x^3，对照 N(k,q)（DP 反演）。
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c3a_lib import *
from laurent import Lau
from fractions import Fraction
from math import factorial, comb

K, M = 30, 12
CAP = K + 3 * M + 12
ONE = Lau.poly([1], CAP)
ZERO = Lau(0, [], CAP)


def xpow(e, c=1):
    return Lau.poly([c], CAP, shift=e)


def gpoch(b, n):
    r = Fraction(1)
    for i in range(n):
        r *= b + i
    return r


def gbinom_series(e, n):
    """(1-t)^{-e} 的 t^p 系数，p<=n（e 为任意有理数）：(e)_p/p!。"""
    return [gpoch(e, p) / factorial(p) for p in range(n + 1)]


def Y_beta(A, be):
    """返回 Y_beta 的 t^N 系数（Laurent 级数）列表，N<=M。"""
    Apoly = Lau.poly(A, CAP)
    lamA = Apoly * xpow(-3)
    inv_poch = []
    p = ONE
    for N in range(M + 1):
        inv_poch.append(p.inv())
        p = p * (Lau.poly([1 + N], CAP) - lamA)       # (1-lamA)_{N+1}
    out = [ZERO] * (M + 1)
    for m in range(M + 1):
        # X^m = (-t/(1-t))^m：t^{m+r} 系数 (-1)^m C(m+r-1,r)
        Xm = [Fraction(0)] * (M + 1)
        if m == 0:
            Xm[0] = Fraction(1)
        else:
            for r in range(M + 1 - m):
                Xm[m + r] = Fraction((-1) ** m * comb(m + r - 1, r))
        for n in range(M + 1 - m):
            N = m + n
            coef = Fraction(factorial(N)) * gpoch(be, m) / (factorial(m) * factorial(n)) * (-1) ** n
            base = inv_poch[N] * xpow(-3 * n, coef)
            for d in range(M + 1 - n):
                if Xm[d]:
                    out[d + n] = out[d + n] + base * Xm[d]
    pre = gbinom_series(be, M)
    res = [ZERO] * (M + 1)
    for i in range(M + 1):
        for j in range(M + 1 - i):
            if pre[j]:
                res[i + j] = res[i + j] + out[i] * pre[j]
    Ainv = Apoly.inv()
    return [r * Ainv for r in res]


def apply_LA_series(Y, A):
    """(A - t)Y - x^3 t Y_t 的 t^N 系数。"""
    Apoly = Lau.poly(A, CAP)
    out = []
    for N in range(M + 1):
        v = Apoly * Y[N] - xpow(3, N) * Y[N]
        if N >= 1:
            v = v - Y[N - 1]
        out.append(v)
    return out


t0 = time.time()
ok = True
for A in ([1, -1], [1, -1, 0, 1]):
    for be in (Fraction(0), Fraction(1), Fraction(2), Fraction(3), Fraction(4), Fraction(1, 2), Fraction(-3)):
        Y = Y_beta(A, be)
        LY = apply_LA_series(Y, A)
        target = gbinom_series(be, M)
        for N in range(M + 1):
            L = LY[N]
            if L.v is not None and L.v < 0:
                ok = False; print('neg powers', A, be, N)
            for k in range(K + 1):
                want = target[N] if k == 0 else 0
                if L.coeff(k) != want:
                    ok = False; print('mismatch', A, be, N, k, L.coeff(k), want); break
print('(a) L_A[Y_beta] == (1-t)^{-beta}, A in {1-x,1-x+x^3}, beta in {0,1,2,3,4,1/2,-3}, k<=%d, t^N N<=%d: %s  %.1fs'
      % (K, M, ok, time.time() - t0))

# (b) Ncal 的 Humbert 形式
t1 = time.time()
KK, QQ = 40, 14
CAP2 = KK + 3 * QQ + 12
T = U_fast_table(KK, QQ + 1)
Ntab = [[N_from_U(T, k, q) for q in range(QQ + 1)] for k in range(KK + 1)]
lam = Lau.poly([1, -1], CAP2, shift=-3)
ONE2 = Lau.poly([1], CAP2)
ZERO2 = Lau(0, [], CAP2)
inv_poch = []
p = ONE2
for N in range(QQ + 1):
    inv_poch.append(p.inv())
    p = p * (Lau.poly([N], CAP2) - lam)        # (-lam)_{N+1} = prod_{i=0}^{N} (i - lam)


def ser_mul(A_, B_):
    out = [ZERO2] * (QQ + 1)
    for i in range(QQ + 1):
        for j in range(QQ + 1 - i):
            if not (isinstance(B_[j], Fraction) and B_[j] == 0):
                out[i + j] = out[i + j] + A_[i] * B_[j]
    return out


def phi1_N(be):
    """Phi_1(1,be;-lam;X=-y,Y=yh)，yh^n = (-1)^n x^{-3n} y^n (1+y)^{-n}；返回 y^q 系数列表。"""
    out = [ZERO2] * (QQ + 1)
    for m in range(QQ + 1):
        for n in range(QQ + 1 - m):
            N = m + n
            coef = Fraction(factorial(N) * gpoch(be, m), factorial(m) * factorial(n)) * (-1) ** m * (-1) ** n
            base = inv_poch[N] * Lau.poly([coef], CAP2, shift=-3 * n)
            # y^{m+n} (1+y)^{-n}
            for r in range(QQ + 1 - N):
                c = Fraction(comb(n + r - 1, r) * (-1) ** r) if n > 0 else Fraction(1 if r == 0 else 0)
                if c:
                    out[N + r] = out[N + r] + base * c
    return out


def onepy(e):
    return [Fraction(comb(e, r)) if e >= 0 else Fraction(0) for r in range(QQ + 1)]


A = Lau.poly([1, -1, 0, 1], CAP2)
x2 = Lau.poly([1], CAP2, shift=2)
P0, P1, P2 = phi1_N(0), phi1_N(1), phi1_N(2)
tot = [ZERO2] * (QQ + 1)
T0 = [(A + x2) * c for c in P0]
T1 = ser_mul([x2 * c * (-2) for c in P1], onepy(1))
T2 = ser_mul([x2 * c for c in P2], onepy(2))
pre = [Fraction((-1) ** r) for r in range(QQ + 1)]       # 1/(1+y)
inner = [T0[q] + T1[q] + T2[q] for q in range(QQ + 1)]
Nc = ser_mul(inner, pre)
Ainv = A.inv()
okb = True
for q in range(QQ + 1):
    L = Nc[q] * Ainv
    if L.v is not None and L.v < 0:
        okb = False; print('neg powers q', q)
    for k in range(KK + 1):
        if L.coeff(k) != Ntab[k][q]:
            okb = False; print('N mismatch k=%d q=%d' % (k, q), L.coeff(k), Ntab[k][q]); break
print('(b) Ncal Humbert form == N(k,q) (k<=%d, q<=%d): %s  %.1fs' % (KK, QQ, okb, time.time() - t1))
