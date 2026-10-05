# -*- coding: utf-8 -*-
"""Final audit (consistency): spot-check numbers quoted in several report sections
against code/core.py (truth from the original definition)."""
import os, sys
from fractions import Fraction as Fr
from math import comb, factorial
from decimal import Decimal, getcontext

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))
sys.stdout.reconfigure(encoding='utf-8')
from core import U_fast_table, U_list, N_from_U, U_fast_column  # noqa
from polylib import P_poly, b_poly, pmul, padd, psub, pscale, trim, series_inv, series_mul  # noqa

def out(*a):
    print(*a, flush=True)

# (1) U_100(100) digits (T2.9 / ③ table: "k=m=100 时 U 有 99 位")
col = U_fast_column(100, 100)
out('[1] digits U_100(100) =', len(str(col[100])))

# (2) N triangle values: anchors D(2d+2,d) (④A.5: 2,8,65,574,6012,70674)
T = U_fast_table(14, 16)
def N(k, q):
    return N_from_U(T, k, q)
out('[2] anchors D(2d+2,d) d=0..5:', [N(2*d+2, d+2) for d in range(6)])

# (3) norms in K_2 = Q[x]/(2x^3+x-1): N(W~_2 - 1)=17/8, N(W~_2)=103/16 (T2.6(ii))
def mulmod(a, b, f):
    # polys as lists low->high, Fractions; reduce mod monic f
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    n = len(f) - 1
    for d in range(len(r) - 1, n - 1, -1):
        c = r[d]
        if c:
            for i in range(n + 1):
                r[d - n + i] -= c * f[i]
    return (r + [Fr(0)] * n)[:n]
def norm(a, f):
    n = len(f) - 1
    basis = [[Fr(1) if i == j else Fr(0) for i in range(n)] for j in range(n)]
    M = [mulmod(a, e, f) for e in basis]  # columns
    # det
    A = [[M[j][i] for j in range(n)] for i in range(n)]
    det = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            A[c], A[p] = A[p], A[c]; det = -det
        det *= A[c][c]
        for r in range(c + 1, n):
            fac = A[r][c] / A[c][c]
            for cc in range(c, n):
                A[r][cc] -= fac * A[c][cc]
    return det
f2 = [Fr(-1, 2), Fr(1, 2), Fr(0), Fr(1)]   # x^3 + x/2 - 1/2  (monic version of 2x^3+x-1)
Wt2 = [Fr(0)] * 9; Wt2[0] = 1; Wt2[5] += 2; Wt2[8] += 4     # 1 + 1*2*x^5 + 2*2*1*x^8
Wt2m1 = Wt2[:]; Wt2m1[0] = 0
out('[3] K_2: N(W~_2 - 1) =', norm([Fr(c) for c in Wt2m1], f2), ' N(W~_2) =', norm([Fr(c) for c in Wt2], f2))
f1 = [Fr(-1), Fr(1), Fr(0), Fr(1)]  # x^3+x-1
Wt1 = [1, 0, 0, 0, 0, 1]
out('    K_1: N(W~_1) =', norm([Fr(c) for c in Wt1], f1))

# (4) c_m numerics (T5.1(3)): c_1, c_2, c_3; c_1=(10+15rho+17rho^2)/31
getcontext().prec = 60
def rho(m):
    lo, hi = Decimal(1), Decimal(3) + Decimal(m)
    for _ in range(300):
        mid = (lo + hi) / 2
        if mid**3 - mid**2 - m > 0:
            hi = mid
        else:
            lo = mid
    return lo
def cm(m):
    r = rho(m)
    s = sum(r**(3*i) / factorial(i) for i in range(m))
    return r * (r**(3*m+1) / factorial(m) - s) / (3*r - 2)
r1 = rho(1)
out('[4] c_1..c_3 =', [str(cm(m))[:14] for m in (1, 2, 3)], ' (10+15r+17r^2)/31 =', str((10 + 15*r1 + 17*r1*r1)/31)[:14])
out('    tau_1 = sqrt(rho1(rho1-1)) =', str((r1*(r1-1)).sqrt())[:8], ' W_L(1/e)~0.2785 check skipped')
# c_4 exact and c_18 exact
def cm_exact_int_rho(m, r):
    s = sum(Fr(r**(3*i), factorial(i)) for i in range(m))
    return r * (Fr(r**(3*m+1), factorial(m)) - s) / (3*r - 2)
out('    c_4 =', cm_exact_int_rho(4, 2), ' c_18 =', cm_exact_int_rho(18, 3))

# (5) Num_q low coefficients (T4.3(5)): [x^{q+1}]Num_q = q^2-q-4 (q>=3); [x^{q+2}] = (q^4-6q^3+7q^2-2q+76)/4 (q>=4)
K = 60
TT = U_fast_table(K, 14)
def Fq(q):
    return [N_from_U(TT, k, q) for k in range(K + 1)]
bad5 = []
for q in range(1, 13):
    num = series_mul(P_poly(q - 1), Fq(q), K + 1)
    if q >= 3 and num[q+1] != q*q - q - 4:
        bad5.append(('x^{q+1}', q, num[q+1]))
    if q >= 4 and Fr(num[q+2]) != Fr(q**4 - 6*q**3 + 7*q**2 - 2*q + 76, 4):
        bad5.append(('x^{q+2}', q, num[q+2]))
    if q in (2, 3):
        out('    Num_%d low coeffs:' % q, num[q:q+3], ' formula x^{q+1}:', q*q-q-4, ' x^{q+2}:', Fr(q**4-6*q**3+7*q**2-2*q+76, 4))
out('[5] Num_q low-coefficient formulas, bad =', bad5)

# (6) Num_q high coefficients (T4.3(6)): j=0:(q-1)!, j=1:0, j=2:(q-1)!(q-1+H_{q-1}), j=3:(q-1)(q-1)!(H_{q-1}-1)
bad6 = []
for q in range(2, 13):
    num = trim(series_mul(P_poly(q - 1), Fq(q), K + 1))
    d = 3*q - 2
    H = sum(Fr(1, i) for i in range(1, q))
    exp = {0: factorial(q-1), 1: 0, 2: factorial(q-1)*(q-1+H), 3: (q-1)*factorial(q-1)*(H-1)}
    for j, v in exp.items():
        got = num[d-j] if d-j >= 0 else 0
        if Fr(got) != Fr(v):
            bad6.append((q, j, got, v))
out('[6] Num_q high-coefficient formulas j<=3, q=2..12, bad =', bad6)

# (7) T5.3(1): h_k'(1) = -(k^2-3k-2) (k>=4); T5.3(4) mobius values; T5.2 [m^{k-1}] formula
out('[7] U_k(-2) for k=1..6 via binomial basis:',
    [sum(N(k, q) * (-1)**q for q in range(k+1)) for k in range(1, 7)])

# (8) d=2 Newton coefficients at 2d+2: 65,74,64,30,6
def p2(k):
    return Fr(k**4 - 10*k**3 + 43*k**2 - 98*k + 164, 4)
vals = [p2(6 + i) for i in range(5)]
newt = []
cur = vals[:]
for i in range(5):
    newt.append(cur[0]); cur = [cur[j+1]-cur[j] for j in range(len(cur)-1)]
out('[8] Newton coeffs p_2 at 6:', newt)

# (9) R_k vs F4 example R_k = c_1(k+3)+c_1(k-2)-1
c1 = series_inv([1, -1, 0, -1], 80)
Rk = [U_fast_column(1, 60)[k] for k in range(61)]
ok9 = all(Rk[k] == c1[k+3] + (c1[k-2] if k >= 2 else 0) - 1 for k in range(61))
out('[9] R_k = c_1(k+3)+c_1(k-2)-1 for k<=60:', ok9)

# (10) prompt R_k gf: coefficient of x^1 in (1-x+x^2)/((1-x)(1-x-x^3))
den = pmul([1, -1], [1, -1, 0, -1])
g = series_mul([1, -1, 1], series_inv(den, 10), 10)
out('[10] prompt gf first coeffs:', g[:6], ' R_0..R_5:', Rk[:6])
