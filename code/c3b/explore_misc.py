# -*- coding: utf-8 -*-
"""c3b 探索脚本 3：Φ 的代换恒等式、Φ 的 y-ODE、算子恒等式 ψ(ℓ1)∘β^{-1} = ((1+y)/y)ℓ_N、
Ψ_q 的留数公式、Lemma 1 与 t-ODE、饱和引理中的 rem(L_N)=1。全部精确。"""
import sys, os, time
from fractions import Fraction as Fr
from math import comb, factorial
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_fast_table, N_from_U, N_brute
from polylib import trim, padd, psub, pscale, pmul, pshift, pdiv, pderiv, P_poly, b_poly, series_inv, series_mul

t0 = time.time()
K = M = 40
T = U_fast_table(K, M)
NT = [[N_from_U(T, k, q) for q in range(M + 1)] for k in range(K + 1)]

# ---------- 二元多项式（dict (i,j)->c，x^i y^j）----------
def badd(*ps):
    r = {}
    for p in ps:
        for key, c in p.items():
            r[key] = r.get(key, 0) + c
    return {k: v for k, v in r.items() if v != 0}

def bscale(p, c):
    return {k: v * c for k, v in p.items() if v * c != 0}

def bmul(p, q):
    r = {}
    for (a, b), c in p.items():
        for (e, f), d in q.items():
            r[(a + e, b + f)] = r.get((a + e, b + f), 0) + c * d
    return {k: v for k, v in r.items() if v != 0}

def btheta_y(p):
    return {(a, b): c * b for (a, b), c in p.items() if c * b != 0}

def bdiv_y(p):
    assert all(b >= 1 for (a, b) in p)
    return {(a, b - 1): c for (a, b), c in p.items()}

ONE = {(0, 0): 1}
X = {(1, 0): 1}
Y = {(0, 1): 1}
OPY = {(0, 0): 1, (0, 1): 1}            # 1+y
OPY2 = bmul(OPY, OPY)

def ellN(g):
    """ℓ_N g = g - x g - x y g - (θ_y - 1)(x^3 (1+y)^2 g)。"""
    h = bmul(bmul({(3, 0): 1}, OPY2), g)
    return badd(g, bscale(bmul(X, g), -1), bscale(bmul(bmul(X, Y), g), -1),
                bscale(btheta_y(h), -1), h)

def lhs_iso(g):
    """y * ψ(ℓ1)( (1+y)^2 g / y )，ψ(ℓ1) = (1+y)^{-1} - x - x^3 (1+y) θ_y。"""
    h = bdiv_y(bmul(OPY2, g))               # (1+y)^2 g / y
    h_over = bdiv_y(bmul(OPY, g))           # h/(1+y) = (1+y) g / y
    term = badd(h_over, bscale(bmul(X, h), -1),
                bscale(bmul(bmul({(3, 0): 1}, OPY), btheta_y(h)), -1))
    return bmul(Y, term)

ok_iso = True
for a in range(0, 4):
    for b in range(1, 6):
        g = {(a, b): 1}
        if lhs_iso(g) != bmul(OPY, ellN(g)):
            ok_iso = False
print('operator identity y*psi(l1)*((1+y)^2/y) == (1+y)*l_N on x^a y^b (a<=3, 1<=b<=5):', ok_iso)

# ---------- Φ 代换恒等式 ----------
# Φ(x,y) = 1/(1+y) + y F(x, y/(1+y)) / (1+y)^2，逐项核对 k<=KK, q<=QQ
KK, QQ = 20, 20
# (y/(1+y))^m 的系数：sum_{n>=m} (-1)^{n-m} C(n-1, m-1) y^n (m>=1)；m=0 时为 1
def sub_coeff(m, n):
    if m == 0:
        return 1 if n == 0 else 0
    if n < m:
        return 0
    return (-1) ** (n - m) * comb(n - 1, m - 1)
ok_phi = True
for k in range(0, KK + 1):
    # A_k(y) = sum_m U_k(m) (y/(1+y))^m 截断到 y^QQ
    Ak = [sum(T[k][m] * sub_coeff(m, n) for m in range(0, n + 1)) for n in range(QQ + 1)]
    # y * A_k / (1+y)^2
    inv2 = [(-1) ** n * (n + 1) for n in range(QQ + 1)]     # 1/(1+y)^2
    yA = [0] + Ak[:QQ]
    Bk = [sum(yA[i] * inv2[n - i] for i in range(n + 1)) for n in range(QQ + 1)]
    for q in range(QQ + 1):
        val = Bk[q] + ((-1) ** q if k == 0 else 0)
        if val != NT[k][q]:
            ok_phi = False
print('Phi(x,y) = 1/(1+y) + y F(x,y/(1+y))/(1+y)^2, coefficients k<=%d q<=%d:' % (KK, QQ), ok_phi)

# ---------- Φ 的 y-ODE：(1-x-xy+x^3(1-y^2))Φ - x^3 (1+y)^2 θ_y Φ = 1 - x + x^3 + x^2 y^2 ----------
def Nv(k, q):
    if k < 0 or q < 0:
        return 0
    return NT[k][q]
ok_ode = True
bad = []
for k in range(0, K + 1):
    for q in range(0, M + 1):
        lhs = (Nv(k, q) - Nv(k - 1, q) - Nv(k - 1, q - 1) + Nv(k - 3, q) - Nv(k - 3, q - 2)
               - (q * Nv(k - 3, q) + 2 * (q - 1) * Nv(k - 3, q - 1) + (q - 2) * Nv(k - 3, q - 2)))
        rhs = {(0, 0): 1, (1, 0): -1, (3, 0): 1, (2, 2): 1}.get((k, q), 0)
        if lhs != rhs:
            ok_ode = False
            bad.append((k, q, lhs, rhs))
print('Phi y-ODE with RHS 1-x+x^3+x^2y^2 (k,q<=40):', ok_ode, bad[:5])
# 同一件事的递推形式：(C3) 在 k>=3, q>=1 成立；q>=1 时唯一例外 (k,q)=(2,2)
exc = [(k, q) for k in range(0, K + 1) for q in range(1, M + 1)
       if Nv(k, q) != Nv(k - 1, q) + Nv(k - 1, q - 1) + (q - 1) * (Nv(k - 3, q) + 2 * Nv(k - 3, q - 1) + Nv(k - 3, q - 2))]
print('(C3) triangle recurrence failures with q>=1 (k,q<=40):', exc)

# ---------- Ψ_q 公式与留数 ----------
P = {-1: [1]}
for m in range(0, 16):
    P[m] = pmul(P[m - 1], b_poly(m))
W = {-1: [1]}
for m in range(0, 16):
    W[m] = padd(W[m - 1], pshift(pscale(P[m - 1], m), 2))
ok_psi = True
for q in range(0, 13):
    # Num_q = sum_i (-1)^{q-i} C(q,i) W_{i-1} P_{q-1}/P_{i-1}
    Num = []
    for i in range(0, q + 1):
        cof = [1]
        for v in range(i, q):
            cof = pmul(cof, b_poly(v))
        Num = padd(Num, pscale(pmul(W[i - 1], cof), (-1) ** (q - i) * comb(q, i)))
    ser = series_mul(Num, series_inv(P[q - 1], K + 1), K + 1)
    if [int(c) for c in ser] != [NT[k][q] for k in range(K + 1)]:
        ok_psi = False
    # 留数公式：Res_{x_v} Ψ_q = Res_{x_v} G_v * (-1)^{q-1-v} * sum_j C(q,v+1+j) x_v^{-3j}/j!
    for v in range(0, q):
        d = q - 1 - v
        # 交叉相乘并乘 x^{3d} d!：Num * P_v' * x^{3d} d!  ≡  (-1)^d W_v P_{q-1}' * sum_j C(q,v+1+j) x^{3(d-j)} d!/j!   (mod b_v)
        lhs = pscale(pshift(pmul(Num, pderiv(P[v])), 3 * d), factorial(d))
        S = [0] * (3 * d + 1)
        for j in range(0, d + 1):
            S[3 * (d - j)] += comb(q, v + 1 + j) * (factorial(d) // factorial(j))
        rhs = pscale(pmul(pmul(W[v], pderiv(P[q - 1])), S), (-1) ** d)
        if trim(pdiv(psub(lhs, rhs), b_poly(v))[1]):
            ok_psi = False
            print('psi residue fails q,v=', q, v)
print('Psi_q = sum_i (-1)^{q-i}C(q,i)G_{i-1} vs N table (q<=12,k<=40) and residue formula mod b_v:', ok_psi)
br = N_brute(8)
print('N_brute(8) vs incl-excl:', [br.get(q, 0) for q in range(9)] == [NT[8][q] for q in range(9)])

# ---------- t-ODE (C5) 逐项 ----------
def Uv(k, m):
    if k < 0 or m < 0:
        return 0
    return T[k][m]
ok_t = all(Uv(k, m) - Uv(k - 1, m) - Uv(k, m - 1) - m * Uv(k - 3, m)
           == (1 if (k, m) == (0, 0) else 0) + (m if k == 2 else 0)
           for k in range(0, K + 1) for m in range(0, M + 1))
print('F t-ODE (1-x-t)F - x^3 t F_t = 1 + x^2 t/(1-t)^2, coefficients k,m<=40:', ok_t)

# ---------- 饱和引理：rem_{(1+Y)}(L_N) = 1 ----------
# 系数世界：c_0 = 1 - X - (q-1)X^3, c_1 = -X - 2(q-1)X^3, c_2 = -(q-1)X^3；rem = c_0 - τ^{-1}c_1 + τ^{-2}c_2，τ^{-1}: q->q+1
# 用 dict {X 幂: 关于 q 的多项式(list)} 计算
def qpoly_shift(p, s):
    # p(q) -> p(q+s)
    out = [0] * len(p)
    for i, c in enumerate(p):
        for j in range(i + 1):
            out[j] += c * comb(i, j) * s ** (i - j)
    return trim(out)
c0 = {0: [1], 1: [-1], 3: [1, -1]}       # (q-1) -> [ -1, 1 ] ; -(q-1) = [1,-1]
c1 = {1: [-1], 3: [2, -2]}               # -2(q-1) = [2,-2]
c2 = {3: [1, -1]}
rem = {}
for e, p in c0.items():
    rem[e] = padd(rem.get(e, []), p)
for e, p in c1.items():
    rem[e] = psub(rem.get(e, []), qpoly_shift(p, 1))
for e, p in c2.items():
    rem[e] = padd(rem.get(e, []), qpoly_shift(p, 2))
rem = {e: trim(p) for e, p in rem.items() if trim(p)}
print('rem_(1+Y)(L_N) =', rem, '(should be {0: [1]})')
print('elapsed %.1fs' % (time.time() - t0))
