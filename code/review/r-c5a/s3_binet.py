# -*- coding: utf-8 -*-
"""s3：谱分解（定理 2.2 / T4）、极点模长排序（T3）、三项渐近（T5 的加强检验）、R_k 公式（T22）。

完整性论证：U_k(m) 的 g.f. 为 W_m/P_m，deg W_m < deg P_m = 3m+1，所以 U_k(m) 对 k>=3m+1 满足
sum_i P_m[i] U_{k-i}(m) = 0；右端 sum_sigma alpha sigma^k 对一切 k 满足同一递推。故只要两边在
k = 0..3m 上相等，就对一切 k 相等。下面对 m<=25 检查 k=0..3m+40（多出 40 个冗余点）。
"""
import sys, os, time
from fractions import Fraction as Fr
from math import factorial, comb
from decimal import Decimal, getcontext
import cmath
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rlib import U_dp, U_rec_table

getcontext().prec = 100
t0 = time.time()

MMAX = 25
COL = {m: U_dp(m, 3 * m + 41) for m in range(0, MMAX + 1)}


def ypow_y2coef(j, nmax):
    """L[n] = [y^2](y^n mod y^3-y^2-j)，n=0..nmax。"""
    L = []
    a = (Fr(1), Fr(0), Fr(0))
    for n in range(nmax + 1):
        L.append(a[2])
        a = (j * a[2], a[0], a[1] + a[2])
    return L


def gt(j):
    d = {3 * j + 2: Fr(1, factorial(j))}
    for i in range(j):
        d[3 * i] = d.get(3 * i, Fr(0)) + Fr(j - i, factorial(i))
    return d


# (1) Lagrange 形式（自己实现）
LT = {j: ypow_y2coef(j, 3 * MMAX + 3 * MMAX + 50) for j in range(1, MMAX + 1)}
ok_L = True
for m in range(0, MMAX + 1):
    for k in range(0, 3 * m + 41):
        tot = Fr((-1) ** m, factorial(m))
        for j in range(1, m + 1):
            sh = k + 3 * (m - j)
            inner = sum(c * LT[j][e + sh] for e, c in gt(j).items())
            tot += Fr((-1) ** (m - j), factorial(m - j)) * inner
        if tot != COL[m][k]:
            ok_L = False
            print('  Lagrange mismatch m=%d k=%d' % (m, k))
            break
print('(1) spectral formula (Lagrange form) == own DP, m<=25, k=0..3m+40 (complete by recurrence argument):', ok_L)


# (2) c_j 形式
def cseq_list(j, nmax):
    a = [1, 1, 1]
    while len(a) <= nmax:
        a.append(a[-1] + j * a[-3])
    return a


CJ = {j: cseq_list(j, 3 * MMAX + 3 * MMAX + 50) for j in range(1, MMAX + 1)}


def cj(j, n):
    if n < 0:
        return 0
    if j == 0:
        return 1
    return CJ[j][n]


ok_c = True
for m in range(0, MMAX + 1):
    for k in range(0, 3 * m + 41):
        tot = Fr(0)
        for j in range(0, m + 1):
            tot += Fr((-1) ** (m - j) * comb(m, j) * cj(j, k + 3 * m), factorial(m))
        for j in range(1, m + 1):
            for i in range(0, j):
                tot += Fr((-1) ** (m - j) * (j - i), factorial(m - j) * factorial(i)) * cj(j, k + 3 * (m - j + i) - 2)
        if tot != COL[m][k]:
            ok_c = False
            print('  c_j-form mismatch m=%d k=%d' % (m, k))
            break
print('(2) spectral formula (c_j form) == own DP, m<=25, k=0..3m+40:', ok_c)

# (3) R_k = c_1(k+3) + c_1(k-2) - 1，k<=300
c1 = cseq_list(1, 400)
R = U_dp(1, 300)
ok_R = all(R[k] == c1[k + 3] + (c1[k - 2] if k >= 2 else 0) - 1 for k in range(0, 301))
print('(3) R_k = c_1(k+3)+c_1(k-2)-1 (T22), k<=300 vs own DP:', ok_R)


# (4) 极点模长排序：rho_m > rho_{m-1} > |sigma_m|, |sigma_j| 递增，tau_m 的定义
def roots_f(j):
    # Newton 求实根，再用 Vieta 求复根
    y = Decimal(j) ** (Decimal(1) / 3) + Decimal('0.4')
    for _ in range(300):
        y2 = y - (y ** 3 - y ** 2 - j) / (3 * y * y - 2 * y)
        if abs(y2 - y) < Decimal(10) ** -95:
            break
        y = y2
    r = y2
    # 复根 s, s̄：s + s̄ = 1 - r, |s|^2 = j / r
    return r, (Decimal(j) / r).sqrt(), (1 - r) / 2


RH = {0: Decimal(1)}
SG = {0: Decimal(0)}
for j in range(1, 2001):
    r, s_abs, re = roots_f(j)
    RH[j] = r
    SG[j] = s_abs
ok_order = all(RH[j] > RH[j - 1] for j in range(1, 2001)) and \
    all(SG[m] < RH[m - 1] for m in range(1, 2001)) and all(SG[j] > SG[j - 1] for j in range(2, 2001)) and \
    all(SG[j] < RH[j] for j in range(1, 2001)) and \
    all(abs(SG[j] ** 2 - RH[j] * (RH[j] - 1)) < Decimal('1e-80') for j in range(1, 2001))
print('(4) [numeric] rho_j increasing, |sigma_j|^2 = rho_j(rho_j-1), |sigma_j| increasing, |sigma_m| < rho_{m-1}, j,m<=2000:', ok_order)
third = {m: ('rho_{m-2}' if RH[m - 2] > SG[m] else '|sigma_m|') for m in range(2, 12)}
print('    which pole is third (tau_m) for m=2..11:', third)


# (5) 三项渐近：U_k(m) = c_m rho_m^k - c_{m-1} rho_{m-1}^{k+3} + (c_{m-2}/2) rho_{m-2}^{k+6} + O(...)，m=3..8
def c_dec(m):
    if m == 0:
        return Decimal(1)
    r = RH[m]
    e = sum(r ** (3 * i) / factorial(i) for i in range(m))
    return r * (r ** (3 * m + 1) / factorial(m) - e) / (3 * r - 2)


print('(5) remainder after two terms divided by (c_{m-2}/2) rho_{m-2}^{k+6}  (should -> 1 when rho_{m-2} > |sigma_m|):')
for m in range(3, 9):
    K = 700
    U = U_dp(m, K)
    out = []
    for k in (100, 300, 700):
        rem = Decimal(U[k]) - c_dec(m) * RH[m] ** k + c_dec(m - 1) * RH[m - 1] ** (k + 3)
        pred = c_dec(m - 2) / 2 * RH[m - 2] ** (k + 6)
        out.append('k=%d: %s' % (k, str(+(rem / pred))[:14]))
    print('    m=%d  ' % m + '; '.join(out))

# (6) m=2 的第三项是复根对（|sigma_2| > rho_0 = 1）：余项/|sigma_2|^k 应有界并振荡
U = U_dp(2, 600)
vals = []
for k in (200, 201, 202, 203, 400, 401, 600):
    rem = Decimal(U[k]) - c_dec(2) * RH[2] ** k + c_dec(1) * RH[1] ** (k + 3)
    vals.append('%d:%s' % (k, str(+(rem / SG[2] ** k))[:10]))
print('(6) m=2 remainder / |sigma_2|^k (bounded, oscillating):', ', '.join(vals))
print('elapsed %.1fs' % (time.time() - t0))
