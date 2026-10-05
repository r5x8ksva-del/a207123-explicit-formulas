# -*- coding: utf-8 -*-
"""c3b 探索脚本 1：三次式 y^3-y^2-i 的实根、G_m 的极点/留数、gcd(W_m,b_m) 等精确核对。
只用整数 / Fraction（Decimal 仅用于打印近似值）。"""
import sys, os, time
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_fast_table, binom
from polylib import (trim, padd, psub, pscale, pmul, pshift, peval, pdiv, pgcd,
                     pderiv, series_inv, series_mul, P_poly, b_poly)

t0 = time.time()

# ---------------- 1. 三次式 f_i(y) = y^3 - y^2 - i -----------------
def f(i, y):
    return y * y * y - y * y - i

def disc_cubic(a, b, c):
    """y^3 + a y^2 + b y + c 的判别式。"""
    return 18 * a * b * c - 4 * a ** 3 * c + a * a * b * b - 4 * b ** 3 - 27 * c * c

def isolate_rho(i, bits=80):
    """返回有理区间 (lo, hi)，ρ_i ∈ (lo, hi)，hi-lo <= 2^-bits。i>=1。"""
    lo, hi = Fr(1), Fr(i + 1)
    assert f(i, lo) < 0 < f(i, hi)
    while hi - lo > Fr(1, 2 ** bits):
        mid = (lo + hi) / 2
        if f(i, mid) < 0:
            lo = mid
        else:
            hi = mid
    return lo, hi

IMAX = 60
ok_disc = all(disc_cubic(-1, 0, -i) == -i * (27 * i + 4) < 0 for i in range(1, IMAX + 1))
iv = {i: isolate_rho(i) for i in range(1, IMAX + 1)}
ok_mono = all(iv[i][1] < iv[i + 1][0] for i in range(1, IMAX)) and Fr(1) < iv[1][0]
ok_mod = all(i < iv[i][0] ** 3 for i in range(1, IMAX + 1))   # |omega|^2 = i/rho < rho^2
print('cubic: disc=-i(27i+4)<0 (i<=%d): %s; rho strictly increasing & >1: %s; i<rho^3: %s'
      % (IMAX, ok_disc, ok_mono, ok_mod))

# ---------------- 2. W_m, P_m 与 DP 表 -----------------
MMAX, KMAX = 30, 60
T = U_fast_table(KMAX, MMAX)
P = {-1: [1]}
for m in range(0, MMAX + 1):
    P[m] = pmul(P[m - 1], b_poly(m))
W = {-1: [1]}
for m in range(0, MMAX + 1):
    W[m] = padd(W[m - 1], pshift(pscale(P[m - 1], m), 2))
ok_G = True
for m in range(0, MMAX + 1):
    ser = series_mul(W[m], series_inv(P[m], KMAX + 1), KMAX + 1)
    if [int(c) for c in ser] != [T[k][m] for k in range(KMAX + 1)]:
        ok_G = False
        print('G_m != W_m/P_m at m=', m)
print('G_m = W_m/P_m vs height DP (k<=%d, m<=%d): %s' % (KMAX, MMAX, ok_G))
print('deg W_m = 3m (m>=1), deg P_m = 3m+1:',
      all(len(trim(W[m])) - 1 == 3 * m and len(trim(P[m])) - 1 == 3 * m + 1 for m in range(1, MMAX + 1)))

# Omega_m(x) = 1 + sum_j j (m)_j x^{3j+2}  and  W_m ≡ Omega_m (mod b_m)
def falling(m, j):
    r = 1
    for v in range(j):
        r *= (m - v)
    return r
ok_om = True
for m in range(1, MMAX + 1):
    Om = [0] * (3 * m + 3)
    Om[0] = 1
    for j in range(1, m + 1):
        Om[3 * j + 2] += j * falling(m, j)
    _, r1 = pdiv(W[m], b_poly(m))
    _, r2 = pdiv(Om, b_poly(m))
    if trim(r1) != trim(r2):
        ok_om = False
print('W_m ≡ 1 + sum_j j (m)_j x^{3j+2}  (mod b_m), 1<=m<=%d: %s' % (MMAX, ok_om))

# ---------------- 3. gcd(W_m, b_m), gcd(W_m, P_m) -----------------
ok_g1 = all(pgcd(W[m], b_poly(m)) == [Fr(1)] for m in range(0, MMAX + 1))
print('gcd(W_m, b_m) = 1 for 0<=m<=%d: %s' % (MMAX, ok_g1))
ok_g2 = True
for m in range(0, 13):
    if pgcd(W[m], P[m]) != [Fr(1)]:
        ok_g2 = False
print('gcd(W_m, P_m) = 1 for 0<=m<=12 (direct Euclid): %s' % ok_g2)

# 例外 m = n^2(n-1)：b_m = (1-nx)(1+(n-1)x+n(n-1)x^2)；检查二次因子不整除 W_m
def W_mod(poly_mod, m):
    """W_m mod poly_mod，逐步取模避免高次。"""
    Pm = [Fr(1)]           # P_{-1}
    Wm = [Fr(1)]           # W_{-1}
    for v in range(0, m + 1):
        # W_v = W_{v-1} + v x^2 P_{v-1}
        Wm = pdiv(padd(Wm, pshift(pscale(Pm, v), 2)), poly_mod)[1]
        Pm = pdiv(pmul(Pm, b_poly(v)), poly_mod)[1]
    return trim(Wm)
for n in range(2, 9):
    m = n * n * (n - 1)
    q = [1, n - 1, n * (n - 1)]
    assert trim(pmul([1, -n], q)) == trim(b_poly(m))
    r = W_mod(q, m)
    print('  exceptional m=%d (n=%d): W_m mod quadratic factor = %s -> nonzero: %s'
          % (m, n, 'deg%d' % (len(r) - 1) if r else '0', bool(r)))

# ---------------- 4. 留数递推（精确，mod b_v） -----------------
ok_res = True
for m in range(1, 16):
    for v in range(0, m):
        d = m - v
        fac = 1
        for u in range(1, d + 1):
            fac *= u
        lhs = pscale(pshift(pmul(W[m], pderiv(P[v])), 3 * d), fac)
        rhs = pscale(pmul(W[v], pderiv(P[m])), (-1) ** d)
        _, rem = pdiv(psub(lhs, rhs), b_poly(v))
        if trim(rem):
            ok_res = False
            print('residue recursion fails', m, v)
print('Res_{x_v} G_m = Res_{x_v} G_v * (-1)^{m-v}/((m-v)! x_v^{3(m-v)}) mod b_v, v<m<=15: %s' % ok_res)

# ---------------- 5. 区间算术：W_m(x_m) > 0 与 G_{m-1}(x_m)+m x_m^2 > 0 -----------------
def peval_interval(p, lo, hi):
    """0<lo<=x<=hi 时 p(x) 的严格包络（正负系数分开）。"""
    pos = [c if c > 0 else 0 for c in p]
    neg = [-c if c < 0 else 0 for c in p]
    return peval(pos, lo) - peval(neg, hi), peval(pos, hi) - peval(neg, lo)
ok_pos = True
vals = []
for m in range(1, MMAX + 1):
    rlo, rhi = isolate_rho(m, bits=40 + 12 * m)
    xlo, xhi = 1 / rhi, 1 / rlo
    wl, wh = peval_interval(W[m], xlo, xhi)
    nl, nh = peval_interval(W[m - 1], xlo, xhi)
    dl, dh = peval_interval(P[m - 1], xlo, xhi)
    if not (wl > 0 and dl > 0):
        ok_pos = False
        print('interval check inconclusive at m=', m, float(wl), float(dl))
        continue
    # G_{m-1}(x)+m x^2 的下界：nl/dh (若 nl>0) + m xlo^2
    lowerG = (nl / dh if nl > 0 else nl / dl) + m * xlo * xlo
    if not lowerG > 0:
        ok_pos = False
    vals.append((m, float(lowerG)))
print('interval: W_m(x_m)>0 and G_{m-1}(x_m)+m x_m^2 >0, 1<=m<=%d: %s' % (MMAX, ok_pos))
print('  lower bounds (m, value):', [(m, round(v, 4)) for m, v in vals[:8]], '...')
print('elapsed %.1fs' % (time.time() - t0))
