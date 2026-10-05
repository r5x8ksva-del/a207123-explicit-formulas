# -*- coding: utf-8 -*-
"""探索 4：Ncal(x,y) = sum N(k,q) x^k y^q 与 H(z,t) = sum h_k(t) z^k。
N 的两个定义层来源：N_brute（DFS 按满射词定义，k<=9）与 N_from_U（DP 表 + 二项式反演，k<=30）。"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c3a_lib import *
from laurent import Lau
from fractions import Fraction
from math import comb

t0 = time.time()
K = 30
T = U_fast_table(K, 41)          # m <= 41
Ntab = [[N_from_U(T, k, q) for q in range(K + 1)] for k in range(K + 1)]
ok = True
for k in range(0, 10):
    br = N_brute(k)
    if [br.get(q, 0) for q in range(K + 1)] != Ntab[k]:
        ok = False; print('N_brute mismatch k=', k)
print('N: DFS(k<=9) == DP-inversion:', ok, '%.1fs' % (time.time() - t0))
# N(k,q)=0 for q>k, N(k,0)=[k=0]
print('N(k,q)=0 for q>k, N(k,0)=[k=0]:',
      all(Ntab[k][q] == 0 for k in range(K + 1) for q in range(k + 1, K + 1)) and
      all(Ntab[k][0] == (1 if k == 0 else 0) for k in range(K + 1)))


def Nc(k, q):
    if k < 0 or q < 0 or k > K or q > K:
        return 0
    return Ntab[k][q]


# (1) 三角递推（k>=3, q>=1）：N(k,q) = N(k-1,q-1)+N(k-1,q)+(q-1)[N(k-3,q-2)+2N(k-3,q-1)+N(k-3,q)]
ok = all(Nc(k, q) == Nc(k - 1, q - 1) + Nc(k - 1, q) + (q - 1) * (Nc(k - 3, q - 2) + 2 * Nc(k - 3, q - 1) + Nc(k - 3, q))
         for k in range(3, K + 1) for q in range(1, K + 1))
print('(1) N triangle recurrence k<=30:', ok)

# (2) Ncal 的 PDE：(1 - x(1+y) + x^3(1-y^2)) N - x^3 y (1+y)^2 N_y = 1 - x + x^3 + x^2 y^2
#     [x^k y^q]：N(k,q) - N(k-1,q) - N(k-1,q-1) + N(k-3,q) - N(k-3,q-2)
#                - [ (q)N(k-3,q) + 2(q-1)N(k-3,q-1) + (q-2)N(k-3,q-2) ]
def pde_N_coeff(k, q):
    s = Nc(k, q) - Nc(k - 1, q) - Nc(k - 1, q - 1) + Nc(k - 3, q) - Nc(k - 3, q - 2)
    s -= q * Nc(k - 3, q) + 2 * (q - 1) * Nc(k - 3, q - 1) + (q - 2) * Nc(k - 3, q - 2)
    return s


def rhs_N(k, q):
    return {(0, 0): 1, (1, 0): -1, (3, 0): 1, (2, 2): 1}.get((k, q), 0)


ok = all(pde_N_coeff(k, q) == rhs_N(k, q) for k in range(K + 1) for q in range(K + 1))
print('(2) Ncal PDE coefficientwise k,q<=30:', ok)

# (3) 代换：1 + t F(x,t) = Ncal(x, t/(1-t))/(1-t)，即 [x^k t^n]: [k=n=0] + U_k(n-1) = sum_q N(k,q) C(n,q)
ok = all(((1 if (k == 0 and n == 0) else 0) + (T[k][n - 1] if n >= 1 else 0)) ==
         sum(Ntab[k][q] * comb(n, q) for q in range(K + 1))
         for k in range(K + 1) for n in range(0, 41))
print('(3) 1+tF = Ncal(x,t/(1-t))/(1-t), k<=30, n<=40:', ok)

# (4) Ntilde = 1 + tF 的原生 Laplace 表示（A = 1-x+x^3, v = x^3/A），右端 A + x^2 t^2/(1-t)^2；
#     再 Ncal(x,y) = Ntilde(x, y/(1+y))/(1+y)：[y^q] = sum_n Ntilde_n (-1)^{q-n} C(q,n)
t1 = time.time()
A = [1, -1, 0, 1]
gcols = []
for n in range(K + 1):
    c = zero(K)
    if n == 0:
        c[0], c[1], c[3] = 1, -1, 1
    elif n >= 2:
        c[2] = n - 1
    gcols.append(c)
Nt = laplace_solve(gcols, A, K, K)
ok4a = all(Nt[k][n] == ((1 if (k == 0 and n == 0) else 0) + (T[k][n - 1] if n >= 1 else 0))
           for k in range(K + 1) for n in range(K + 1))
Nrep = [[sum(Nt[k][n] * (-1) ** (q - n) * comb(q, n) for n in range(q + 1)) for q in range(K + 1)] for k in range(K + 1)]
ok4b = Nrep == Ntab
print('(4) native Laplace for Ntilde vs 1+tF(DP): %s ; Ncal from it vs N (k,q<=30): %s  %.1fs'
      % (ok4a, ok4b, time.time() - t1))

# (5) 1F1(1;-lambda;a) = 1 + t*sum_m t^m/P_m（[x^k t^n] = NA[k][n-1]）
KK, MM = 30, 15
CAP = KK + 3 * MM + 10
TOT, NA, AS = stats_tables(KK, MM)
lam = Lau.poly([1, -1], CAP, shift=-3)
ok5 = True
for n in range(0, MM + 1):
    poch = Lau.poly([1], CAP)
    for i in range(0, n):
        poch = poch * (Lau.poly([i], CAP) - lam)          # (-lambda)_n = prod_{i<n} (i - lambda)
    term = Lau.poly([(-1) ** n], CAP, shift=-3 * n) * poch.inv()
    target = [1 if k == 0 else 0 for k in range(KK + 1)] if n == 0 else [NA[k][n - 1] for k in range(KK + 1)]
    if term.v is not None and term.v < 0:
        ok5 = False
    for k in range(KK + 1):
        if term.coeff(k) != target[k]:
            ok5 = False
print('(5) 1F1(1;-lambda;-t/x^3) = 1 + t sum t^m/P_m (k<=30, n<=15):', ok5)

# ---------------- H(z,t) ----------------
# h_k(t) = (1-t)^{k+1} sum_m U_k(m) t^m，取 t^0..t^40（需要 U_k(m), m<=40）
def h_from_U(k, deg=40):
    return [sum((-1) ** j * comb(k + 1, j) * T[k][i - j] for j in range(0, min(i, k + 1) + 1)) for i in range(deg + 1)]


H = [h_from_U(k) for k in range(K + 1)]
okpoly = all(all(c == 0 for c in H[k][max(k, 1):]) for k in range(K + 1))
print('(6) h_k polynomial of degree <= k-1 (k>=1), checked coefficients up to t^40, k<=30:', okpoly)
# h_k = sum_q N(k,q) t^{q-1} (1-t)^{k-q}  (k>=1)
def poly_from_N(k):
    r = [0] * 41
    for q in range(1, k + 1):
        # t^{q-1}(1-t)^{k-q}
        for i in range(k - q + 1):
            r[q - 1 + i] += Ntab[k][q] * comb(k - q, i) * (-1) ** i
    return r


ok = all(poly_from_N(k) == H[k] for k in range(1, K + 1)) and H[0][0] == 1 and not any(H[0][1:])
print('(7) h_k = sum_q N(k,q) t^{q-1}(1-t)^{k-q}, k<=30:', ok)

# (8) H 的 PDE：(1 - z - z^3 t(1-t)) H - z^4 t(1-t) H_z - z^3 t(1-t)^2 H_t = 1 + z^2 t
def padd_(p, q):
    n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def pmul_(p, q):
    if not p or not q: return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r
def pder(p):
    return [i * p[i] for i in range(1, len(p))]
def trim_(p):
    p = list(p)
    while p and p[-1] == 0: p.pop()
    return p


hp = [trim_(H[k]) for k in range(K + 1)]
t1mt = [0, 1, -1]            # t(1-t)
t1mt2 = [0, 1, -2, 1]        # t(1-t)^2
ok = True
for k in range(K + 1):
    s = list(hp[k])
    if k >= 1:
        s = padd_(s, [-c for c in hp[k - 1]])
    if k >= 3:
        s = padd_(s, [-c for c in pmul_(t1mt, hp[k - 3])])                 # z^3 t(1-t) H
        s = padd_(s, [-(k - 3) * c for c in pmul_(t1mt, hp[k - 3])])       # z^4 t(1-t) H_z
        s = padd_(s, [-c for c in pmul_(t1mt2, pder(hp[k - 3]))])          # z^3 t(1-t)^2 H_t
    rhs = [1] if k == 0 else ([0, 1] if k == 2 else [])
    if trim_(s) != rhs:
        ok = False; print('H PDE fails at k=', k, trim_(s))
print('(8) H PDE coefficientwise in z (k<=30), exact in t:', ok)

# (9) H(z,t) = 1 + (Ncal(z(1-t), t/(1-t)) - 1)/t ：
#     [z^k] 右端 = (1/t) sum_q N(k,q) (1-t)^k t^q (1-t)^{-q}  (k>=1)，与 (7) 同式；这里直接用级数核对
ok = True
for k in range(1, K + 1):
    # 计算 sum_q N(k,q) t^{q-1} (1-t)^{k-q} 作为 t 的多项式（与 (7) 的直接实现不同：用 (1-t)^{k} * (t/(1-t))^q / t 的级数展开）
    ser = [Fraction(0)] * 41
    for q in range(1, k + 1):
        # (1-t)^{k-q} as series: if k-q>=0 polynomial
        for i in range(0, 41):
            if q - 1 + i <= 40:
                ser[q - 1 + i] += Ntab[k][q] * comb(k - q, i) * (-1) ** i if i <= k - q else 0
    if [int(c) for c in ser] != H[k]:
        ok = False
print('(9) H = 1 + (Ncal(z(1-t),t/(1-t)) - 1)/t, k<=30:', ok)
print('total %.1fs' % (time.time() - t0))
