# -*- coding: utf-8 -*-
"""探索 3：1F1 / Kummer / 下不完全 Gamma 形式，用 Laurent 级数直接从定义展开，对照定义层 DP。
  NA[k][m] = {0..m}^k 中不以上升结尾的合法序列数；AS[k][m][j] = 以上升结尾且末项为 j 的个数。
"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c3a_lib import *
from laurent import Lau
from fractions import Fraction
from math import factorial

K, M = 40, 20
CAP = K + 3 * M + 10
t0 = time.time()
TOT, NA, AS = stats_tables(K, M)
T = U_fast_table(K, M)
assert TOT == T
print('stats tables %.1fs' % (time.time() - t0))

lam = Lau.poly([1, -1], CAP, shift=-3)          # lambda = (1-x)/x^3
one_minus_x_inv = Lau.poly([1, -1], CAP).inv()


def i_minus_lam(i):
    return Lau.poly([i], CAP) - lam


def xpow(e, c=1):
    return Lau.poly([c], CAP, shift=e)


def series_ok(L, target, label):
    """L 的 x^e 系数：e<0 全为 0，0<=e<=K 等于 target[e]。"""
    assert L.top >= K, (label, L.top)
    if not L.is_zero() and L.v < 0:
        print('  %s: 负幂未消去 v=%d' % (label, L.v)); return False
    for e in range(K + 1):
        if L.coeff(e) != target[e]:
            print('  %s: x^%d 系数 %s != %s' % (label, e, L.coeff(e), target[e])); return False
    return True


# (c) 1F1(1;1-lambda;-t/x^3)/(1-x) 的 t^n 系数 = (-1)^n x^{-3n} / ((1-lambda)_n (1-x))
t1 = time.time()
ok_c = True
for n in range(M + 1):
    poch = Lau.poly([1], CAP)
    for i in range(1, n + 1):
        poch = poch * i_minus_lam(i)
    term = xpow(-3 * n, (-1) ** n) * poch.inv() * one_minus_x_inv
    ok_c &= series_ok(term, [NA[k][n] for k in range(K + 1)], '1F1 n=%d' % n)
print('(c) 1F1 vs NA (k<=%d, m<=%d): %s  %.1fs' % (K, M, ok_c, time.time() - t1))

# (e) 下不完全 Gamma（级数）形式：x^{-3} e^a sum_n (-a)^n/(n!(lambda-n))
t1 = time.time()
ok_e = True
inv_lam_minus = [(lam - Lau.poly([n], CAP)).inv() for n in range(M + 1)]
for m in range(M + 1):
    acc = Lau(0, [], CAP)
    for n in range(m + 1):
        i = m - n
        coef = Fraction((-1) ** i, factorial(i) * factorial(n))
        acc = acc + xpow(-3 - 3 * i - 3 * n, coef) * inv_lam_minus[n]
    ok_e &= series_ok(acc, [NA[k][m] for k in range(K + 1)], 'gamma m=%d' % m)
print('(e) incomplete-gamma series form vs NA: %s  %.1fs' % (ok_e, time.time() - t1))

# (f) F = sum_j c_j t^j / b_j * 1F1(1; j+1-lambda; -t/x^3)，c_0=1, c_j=j x^2；逐 j 对照细分计数
t1 = time.time()
ok_f = True
inv_b = [Lau.poly([1, -1, 0, -j], CAP).inv() for j in range(M + 1)]
ilm = [i_minus_lam(i) for i in range(M + 2)]
for m in range(M + 1):
    total = Lau(0, [], CAP)
    for j in range(m + 1):
        n = m - j
        poch = Lau.poly([1], CAP)
        for i in range(j + 1, j + n + 1):
            poch = poch * ilm[i]
        cj = Lau.poly([1], CAP) if j == 0 else Lau.poly([j], CAP, shift=2)
        term = cj * inv_b[j] * xpow(-3 * n, (-1) ** n) * poch.inv()
        target = [NA[k][m] for k in range(K + 1)] if j == 0 else [AS[k][m][j] for k in range(K + 1)]
        ok_f &= series_ok(term, target, '1F1-sum m=%d j=%d' % (m, j))
        total = total + term
    ok_f &= series_ok(total, [T[k][m] for k in range(K + 1)], '1F1-sum total m=%d' % m)
print('(f) F = sum_j c_j t^j/b_j 1F1(1;j+1-lam;a): per-j vs refined counts, total vs U: %s  %.1fs'
      % (ok_f, time.time() - t1))

# (g) Kummer 形式：F = x^{-3} e^a sum_n phi_n a^n/(lambda-n)，phi(tau) = e^{-tau} g(-x^3 tau)
t1 = time.time()
ok_g = True


def phi_poly(n):
    # phi_n(x) = sum_{j=0}^n (-1)^{n-j}/(n-j)! * c'_j，c'_0 = 1，c'_j = j x^{2+3j} (-1)^j
    acc = Lau(0, [], CAP)
    for j in range(n + 1):
        c = Fraction((-1) ** (n - j), factorial(n - j))
        if j == 0:
            acc = acc + Lau.poly([c], CAP)
        else:
            acc = acc + Lau.poly([c * j * (-1) ** j], CAP, shift=2 + 3 * j)
    return acc


phis = [phi_poly(n) for n in range(M + 1)]
for m in range(M + 1):
    acc = Lau(0, [], CAP)
    for n in range(m + 1):
        i = m - n
        coef = Fraction((-1) ** i * (-1) ** n, factorial(i))
        acc = acc + xpow(-3 - 3 * i - 3 * n, coef) * phis[n] * inv_lam_minus[n]
    ok_g &= series_ok(acc, [T[k][m] for k in range(K + 1)], 'Kummer-F m=%d' % m)
print('(g) Kummer form of F vs U: %s  %.1fs' % (ok_g, time.time() - t1))

# (d) Kummer 恒等式在 Q(lambda) 中：sum_j (-1)^j/((n-j)! j!) * lam/(lam-j) == 1/(1-lam)_n
#     两边乘 prod_{j=0}^n (lam-j) 后是次数 <= n+1 的多项式，在 n+2 个点相等即恒等。
random.seed(7)
ok_d = True
for n in range(0, 31):
    pts = set()
    while len(pts) < n + 2:
        p = Fraction(random.randint(-10 ** 6, 10 ** 6), random.randint(1, 10 ** 4))
        if p.denominator == 1 and 0 <= p <= n:
            continue
        pts.add(p)
    for L in pts:
        lhs = sum(Fraction((-1) ** j, factorial(n - j) * factorial(j)) * L / (L - j) for j in range(n + 1))
        poch = Fraction(1)
        for i in range(1, n + 1):
            poch *= (i - L)
        if lhs != 1 / poch:
            ok_d = False
print('(d) Kummer identity in Q(lambda), n<=30 (n+2 points each, degree argument):', ok_d)
print('total %.1fs' % (time.time() - t0))
