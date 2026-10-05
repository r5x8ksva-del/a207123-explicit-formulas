# -*- coding: utf-8 -*-
"""check_c3b：C-3 的 D-finite 判定（证明的组成部分 + 精确线性代数实验）。

契约：从任意目录运行 `py -3.14 <本文件>`；每条结论一行 PASS/FAIL；最后一行 SUMMARY；全部通过退出码 0。
只用精确整数 / Fraction。秩计算在素数 p < 2^31 上做（numpy int64：元素 < p，乘积 < 2^62，无溢出；
没有 numpy 时退回纯 Python 整数），这是精确的模 p 运算，不是浮点。
唯一的浮点/Decimal 用途：C3B-NUM（标明的数值渐近检查，容差 1e-3）。
所有被检公式都对照 core 里第 1 节原始定义的独立实现（高度 DP / 参考实现 / 多重链 / 直接计数 / DFS）。
"""
import sys, os, time
from fractions import Fraction as Fr
from math import comb, factorial
from decimal import Decimal, getcontext

CODE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, CODE)
from core import (U_fast_table, U_fast_column, U_list, U_multichain, a_direct, good,
                  N_from_U, N_brute)
from polylib import (trim, padd, psub, pscale, pmul, pshift, peval, pdiv, pgcd, pderiv,
                     series_inv, series_mul, b_poly)

try:
    import numpy as np
    HAVE_NP = True
except Exception:  # pragma: no cover
    HAVE_NP = False

T0 = time.time()
RESULTS = []


def report(cid, ok, desc):
    RESULTS.append(ok)
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc))
    sys.stdout.flush()


K = M = 40
KBIG, MBIG = 60, 30
TB = U_fast_table(KBIG, MBIG)            # U_k(m), k<=60, m<=30
T = U_fast_table(K, M)                   # U_k(m), k<=40, m<=40
NT = [[N_from_U(T, k, q) for q in range(M + 1)] for k in range(K + 1)]


def Uv(k, m):
    if k < 0 or m < 0:
        return 0
    return T[k][m]


def Nv(k, q):
    if k < 0 or q < 0:
        return 0
    return NT[k][q]


# =====================================================================
# A. 原始定义锚点
# =====================================================================
def brute_heights(k, m):
    from itertools import product
    if k == 0:
        return 1
    c = 0
    for h in product(range(m + 1), repeat=k):
        if all(good(h[i], h[i + 1], h[i + 2]) for i in range(k - 2)):
            c += 1
    return c


ok = all(U_list(m, 12)[k] == TB[k][m] for m in range(0, 9) for k in range(0, 13))
ok &= all(U_multichain(k, m) == TB[k][m] for k in range(1, 8) for m in range(0, 5))
ok &= all(brute_heights(k, m) == TB[k][m] for k in range(0, 7) for m in range(0, 5))
ok &= all(a_direct(n, k) == TB[k][(n + 1) // 2] * TB[k][n // 2] for k in range(1, 5) for n in range(0, 9))
report('C3B-A1', ok, 'fast DP == reference U_list (k<=12,m<=8) == multichain (k<=7,m<=4) == brute heights '
                     '(k<=6,m<=4); a_direct(n,k) == U(ceil)U(floor) (k<=4,n<=8)')

ok = all(TB[k][m] == (TB[k][m - 1] if m >= 1 else (1 if k == 0 else 0))
         + (TB[k - 1][m] if k >= 1 else 0) + m * (TB[k - 3][m] if k >= 3 else (1 if k == 2 else 0))
         for k in range(1, KBIG + 1) for m in range(0, MBIG + 1))
report('C3B-L1', ok, 'Lemma 1 U_k(m)=U_k(m-1)+U_{k-1}(m)+m U_{k-3}(m) (conventions U_{-1}=1,U_{-2}=0,U_k(-1)=0) '
                     'vs DP, 1<=k<=60, 0<=m<=30')

ok = all(Uv(k, m) - Uv(k - 1, m) - Uv(k, m - 1) - m * Uv(k - 3, m)
         == (1 if (k, m) == (0, 0) else 0) + (m if k == 2 else 0)
         for k in range(0, K + 1) for m in range(0, M + 1))
report('C3B-TODE', ok, 't-ODE (1-x-t)F - x^3 t dF/dt = 1 + x^2 t/(1-t)^2 coefficientwise, k,m<=40')

# =====================================================================
# B. 三次式 y^3 - y^2 - i
# =====================================================================
def fcub(i, y):
    return y * y * y - y * y - i


def isolate_rho(i, bits):
    lo, hi = Fr(1), Fr(i + 1)
    assert fcub(i, lo) < 0 < fcub(i, hi)
    while hi - lo > Fr(1, 2 ** bits):
        mid = (lo + hi) / 2
        if fcub(i, mid) < 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


def disc_cubic(a, b, c):
    return 18 * a * b * c - 4 * a ** 3 * c + a * a * b * b - 4 * b ** 3 - 27 * c * c


IMAX = 60
iv = {i: isolate_rho(i, 60) for i in range(1, IMAX + 1)}
ok = all(disc_cubic(-1, 0, -i) == -i * (27 * i + 4) < 0 for i in range(1, IMAX + 1))
ok &= all(iv[i][1] < iv[i + 1][0] for i in range(1, IMAX)) and Fr(1) < iv[1][0]
ok &= all(i < iv[i][0] ** 3 for i in range(1, IMAX + 1))
report('C3B-CUB', ok, 'y^3-y^2-i: disc=-i(27i+4)<0, unique real root rho_i>1 isolated in rational intervals, '
                      'rho_i strictly increasing, i<rho_i^3 (=> complex roots |w|=sqrt(i/rho_i)<rho_i), 1<=i<=60')

# =====================================================================
# C. G_m = W_m/P_m 与极点
# =====================================================================
MMAX = 60
P = {-1: [1]}
W = {-1: [1]}
for m in range(0, MMAX + 1):
    P[m] = pmul(P[m - 1], b_poly(m))
    W[m] = padd(W[m - 1], pshift(pscale(P[m - 1], m), 2))

ok = True
for m in range(0, MBIG + 1):
    ser = series_mul(W[m], series_inv(P[m], KBIG + 1), KBIG + 1)
    if [int(c) for c in ser] != [TB[k][m] for k in range(KBIG + 1)]:
        ok = False
report('C3B-G', ok, 'G_m = W_m/P_m with W_m = 1 + x^2 sum_{j=1}^m j P_{j-1}, P_m = prod_{i<=m}(1-x-i x^3): '
                    'series == DP, k<=60, m<=30')


def falling(m, j):
    r = 1
    for v in range(j):
        r *= (m - v)
    return r


ok = True
for m in range(1, 31):
    bm = b_poly(m)
    for v in range(0, m):
        # b_v - b_m = (m-v) x^3
        if trim(psub(b_poly(v), bm)) != trim([0, 0, 0, m - v]):
            ok = False
    for j in range(1, m + 1):
        r = pdiv(P[j - 1], bm)[1]
        if trim(psub(r, pdiv(pshift([falling(m, j)], 3 * j), bm)[1])):
            ok = False
    Om = [0] * (3 * m + 3)
    Om[0] = 1
    for j in range(1, m + 1):
        Om[3 * j + 2] += j * falling(m, j)
    if trim(psub(pdiv(W[m], bm)[1], pdiv(Om, bm)[1])) or any(c < 0 for c in Om):
        ok = False
report('C3B-PX', ok, 'b_v-b_m=(m-v)x^3; P_{j-1} == (m)_j x^{3j} and W_m == 1+sum_j j(m)_j x^{3j+2} (positive coeffs) '
                     'mod b_m, so W_m(x_m)>=1; 1<=j<=m<=30')


def peval_interval(p, lo, hi):
    pos = [c if c > 0 else 0 for c in p]
    neg = [-c if c < 0 else 0 for c in p]
    return peval(pos, lo) - peval(neg, hi), peval(pos, hi) - peval(neg, lo)


ok = True
for m in range(1, 31):
    rlo, rhi = isolate_rho(m, 40 + 12 * m)
    xlo, xhi = 1 / rhi, 1 / rlo
    wl, _ = peval_interval(W[m], xlo, xhi)
    nl, _ = peval_interval(W[m - 1], xlo, xhi)
    dl, dh = peval_interval(P[m - 1], xlo, xhi)
    if not (wl > 0 and dl > 0):
        ok = False
        continue
    lowerG = (nl / dh if nl > 0 else nl / dl) + m * xlo * xlo
    if not lowerG > 0:
        ok = False
report('C3B-INT', ok, 'rational interval arithmetic: W_m(x_m)>0 and G_{m-1}(x_m)+m x_m^2>0 at x_m=1/rho_m, 1<=m<=30')

ok = True
for m in range(1, 13):
    for v in range(0, m):
        d = m - v
        lhs = pscale(pshift(pmul(W[m], pderiv(P[v])), 3 * d), factorial(d))
        rhs = pscale(pmul(W[v], pderiv(P[m])), (-1) ** d)
        if trim(pdiv(psub(lhs, rhs), b_poly(v))[1]):
            ok = False
report('C3B-RES', ok, 'Res_z G_m = Res_z G_v * (-1)^{m-v}/((m-v)! z^{3(m-v)}) at every root z of b_v '
                      '(exact, mod b_v), 0<=v<m<=12')

ok = all(pgcd(W[m], b_poly(m)) == [Fr(1)] for m in range(0, MMAX + 1))
report('C3B-GCD1', ok, 'gcd(W_m, b_m) = 1 (exact Euclid over Q), 0<=m<=60')


def W_mod(poly_mod, m):
    Pm, Wm = [Fr(1)], [Fr(1)]
    for v in range(0, m + 1):
        Wm = pdiv(padd(Wm, pshift(pscale(Pm, v), 2)), poly_mod)[1]
        Pm = pdiv(pmul(Pm, b_poly(v)), poly_mod)[1]
    return trim(Wm)


ok = True
for n in range(2, 9):
    m = n * n * (n - 1)
    qf = [1, n - 1, n * (n - 1)]
    if trim(pmul([1, -n], qf)) != trim(b_poly(m)) or not W_mod(qf, m):
        ok = False
report('C3B-GCD2', ok, 'exceptional m=n^2(n-1) (b_m reducible): quadratic factor 1+(n-1)x+n(n-1)x^2 does not divide W_m, '
                       'n=2..8 (m=4,18,48,100,180,294,448)')

ok = all(pgcd(W[m], P[m]) == [Fr(1)] for m in range(0, 11))
report('C3B-GCD3', ok, 'gcd(W_m, P_m) = 1 by direct Euclid, 0<=m<=10 (=> G_m has exactly 3m+1 simple poles)')

# 数值渐近（标明的浮点/Decimal 检查）
getcontext().prec = 50
ok = True
for m in range(1, 6):
    col = U_fast_column(m, 300)
    lo, hi = isolate_rho(m, 80)
    rho = Decimal(lo.numerator) / Decimal(lo.denominator)
    ratio = Decimal(col[300]) / Decimal(col[299])
    if abs(ratio - rho) > Decimal('1e-3'):
        ok = False
report('C3B-NUM', ok, '[numeric, Decimal, tol 1e-3] U_{300}(m)/U_{299}(m) -> rho_m (dominant simple pole x_m), 1<=m<=5')

# =====================================================================
# D. N 与 Φ
# =====================================================================
ok = True
for k in range(0, 9):
    br = N_brute(k)
    if [br.get(q, 0) for q in range(0, k + 1)] != [NT[k][q] for q in range(0, k + 1)]:
        ok = False
for q in range(0, 13):
    Num = []
    for i in range(0, q + 1):
        cof = [1]
        for v in range(i, q):
            cof = pmul(cof, b_poly(v))
        Num = padd(Num, pscale(pmul(W[i - 1], cof), (-1) ** (q - i) * comb(q, i)))
    ser = series_mul(Num, series_inv(P[q - 1], K + 1), K + 1)
    if [int(c) for c in ser] != [NT[k][q] for k in range(K + 1)]:
        ok = False
    for v in range(0, q):
        d = q - 1 - v
        lhs = pscale(pshift(pmul(Num, pderiv(P[v])), 3 * d), factorial(d))
        S = [0] * (3 * d + 1)
        for j in range(0, d + 1):
            S[3 * (d - j)] += comb(q, v + 1 + j) * (factorial(d) // factorial(j))
        rhs = pscale(pmul(pmul(W[v], pderiv(P[q - 1])), S), (-1) ** d)
        if trim(pdiv(psub(lhs, rhs), b_poly(v))[1]):
            ok = False
report('C3B-PSI', ok, 'N: DFS definition == inclusion-exclusion (k<=8); Psi_q=sum_k N(k,q)x^k = sum_i (-1)^{q-i}C(q,i)G_{i-1} '
                      '(q<=12,k<=40); Res_{x_v}Psi_q = (-1)^{q-1-v}Res_{x_v}G_v sum_j C(q,v+1+j)x_v^{-3j}/j! (mod b_v, v<q<=12)')


def sub_coeff(m, n):
    if m == 0:
        return 1 if n == 0 else 0
    if n < m:
        return 0
    return (-1) ** (n - m) * comb(n - 1, m - 1)


ok = True
QQ = 20
inv2 = [(-1) ** n * (n + 1) for n in range(QQ + 1)]
for k in range(0, 21):
    Ak = [sum(T[k][m] * sub_coeff(m, n) for m in range(0, n + 1)) for n in range(QQ + 1)]
    yA = [0] + Ak[:QQ]
    Bk = [sum(yA[i] * inv2[n - i] for i in range(n + 1)) for n in range(QQ + 1)]
    for q in range(QQ + 1):
        if Bk[q] + ((-1) ** q if k == 0 else 0) != NT[k][q]:
            ok = False
report('C3B-PHI', ok, 'Phi(x,y)=sum N(k,q)x^k y^q = 1/(1+y) + y F(x, y/(1+y))/(1+y)^2, coefficients k<=20, q<=20')

ok = True
for k in range(0, K + 1):
    for q in range(0, M + 1):
        lhs = (Nv(k, q) - Nv(k - 1, q) - Nv(k - 1, q - 1) + Nv(k - 3, q) - Nv(k - 3, q - 2)
               - (q * Nv(k - 3, q) + 2 * (q - 1) * Nv(k - 3, q - 1) + (q - 2) * Nv(k - 3, q - 2)))
        if lhs != {(0, 0): 1, (1, 0): -1, (3, 0): 1, (2, 2): 1}.get((k, q), 0):
            ok = False
exc = [(k, q) for k in range(0, K + 1) for q in range(1, M + 1)
       if Nv(k, q) != Nv(k - 1, q) + Nv(k - 1, q - 1) + (q - 1) * (Nv(k - 3, q) + 2 * Nv(k - 3, q - 1) + Nv(k - 3, q - 2))]
ok &= (exc == [(2, 2)])
report('C3B-YODE', ok, 'Phi y-ODE (1-x-xy+x^3(1-y^2))Phi - x^3(1+y)^2 theta_y Phi = 1-x+x^3+x^2y^2 (k,q<=40); '
                       'triangle recurrence L_N holds for all q>=1 except (k,q)=(2,2) (k,q<=40)')


# ---- 算子恒等式 y*psi(l1)∘((1+y)^2/y) == (1+y)*l_N （作用在单项式上）----
def badd(*ps):
    r = {}
    for p_ in ps:
        for key, c in p_.items():
            r[key] = r.get(key, 0) + c
    return {k_: v for k_, v in r.items() if v != 0}


def bmul(p_, q_):
    r = {}
    for (a, b), c in p_.items():
        for (e, f), d in q_.items():
            r[(a + e, b + f)] = r.get((a + e, b + f), 0) + c * d
    return {k_: v for k_, v in r.items() if v != 0}


def bscale(p_, c):
    return {k_: v * c for k_, v in p_.items() if v * c != 0}


def bth(p_):
    return {(a, b): c * b for (a, b), c in p_.items() if c * b != 0}


def bdy(p_):
    return {(a, b - 1): c for (a, b), c in p_.items()}


OPY = {(0, 0): 1, (0, 1): 1}
OPY2 = bmul(OPY, OPY)
X1, Y1, X3 = {(1, 0): 1}, {(0, 1): 1}, {(3, 0): 1}


def ellN(g):
    h = bmul(bmul(X3, OPY2), g)
    return badd(g, bscale(bmul(X1, g), -1), bscale(bmul(bmul(X1, Y1), g), -1), bscale(bth(h), -1), h)


def lhs_iso(g):
    h = bdy(bmul(OPY2, g))
    term = badd(bdy(bmul(OPY, g)), bscale(bmul(X1, h), -1), bscale(bmul(bmul(X3, OPY), bth(h)), -1))
    return bmul(Y1, term)


ok = all(lhs_iso({(a, b): 1}) == bmul(OPY, ellN({(a, b): 1})) for a in range(0, 4) for b in range(1, 7))
# 饱和引理用到的 rem_(1+Y)(L_N) = 1
def qshift(p_, s):
    out = [0] * len(p_)
    for i, c in enumerate(p_):
        for j in range(i + 1):
            out[j] += c * comb(i, j) * s ** (i - j)
    return trim(out)
c0 = {0: [1], 1: [-1], 3: [1, -1]}
c1 = {1: [-1], 3: [2, -2]}
c2 = {3: [1, -1]}
rem = {}
for e, pp in c0.items():
    rem[e] = padd(rem.get(e, []), pp)
for e, pp in c1.items():
    rem[e] = psub(rem.get(e, []), qshift(pp, 1))
for e, pp in c2.items():
    rem[e] = padd(rem.get(e, []), qshift(pp, 2))
rem = {e: trim(pp) for e, pp in rem.items() if trim(pp)}
ok &= (rem == {0: [1]})
report('C3B-ISO', ok, 'transport identity  y*psi(l1)*((1+y)^2/y) == (1+y)*l_N  on x^a y^b (a<=3,1<=b<=6), '
                      'psi(l1)=(1+y)^{-1}-x-x^3(1+y)theta_y; and rem_{(1+Y)}(L_N)=1 (saturation lemma input)')

# =====================================================================
# E. 线性代数实验（模 p 秩 + 精确整数核对）
# =====================================================================
PR = 2147483647  # 2^31-1，素数


def rank_mod(rows, p):
    if HAVE_NP:
        A = np.array(rows, dtype=np.int64) % p
        nr, nc = A.shape
        r = 0
        for c in range(nc):
            if r == nr:
                break
            nz = np.nonzero(A[r:, c])[0]
            if len(nz) == 0:
                continue
            i = r + int(nz[0])
            if i != r:
                A[[r, i]] = A[[i, r]]
            inv = pow(int(A[r, c]), p - 2, p)
            A[r, c:] = (A[r, c:] * inv) % p
            col = A[r + 1:, c].copy()
            idx = np.nonzero(col)[0]
            if len(idx):
                A[r + 1 + idx, c:] = (A[r + 1 + idx, c:] - (col[idx, None] * A[r, c:][None, :]) % p) % p
            r += 1
        return r
    A = [[x % p for x in row] for row in rows]
    nr, nc = len(A), len(A[0]) if A else 0
    r = 0
    for c in range(nc):
        piv = next((i for i in range(r, nr) if A[i][c]), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(r + 1, nr):
            f = A[i][c]
            if f:
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        r += 1
    return r


def unknowns(A, B, monos):
    return [(a, b, i, j) for a in range(A + 1) for b in range(B + 1) for (i, j) in monos]


def rows_mod(tab, unk, k0, m0, p):
    emax = 1 + max(max(i, j) for (_, _, i, j) in unk)
    out = []
    for k in range(k0, K + 1):
        kp = [pow(k, e, p) for e in range(emax)]
        for m in range(m0, M + 1):
            mp = [pow(m, e, p) for e in range(emax)]
            out.append([(tab[k - a][m - b] % p) * kp[i] % p * mp[j] % p for (a, b, i, j) in unk])
    return out


def left_multiple(gen, alpha, beta, i, j):
    out = {}
    for (a, b), poly in gen.items():
        sh = {}
        for (ii, jj), c in poly.items():
            for s in range(ii + 1):
                for t in range(jj + 1):
                    cf = c * comb(ii, s) * (-alpha) ** (ii - s) * comb(jj, t) * (-beta) ** (jj - t)
                    if cf:
                        sh[(s, t)] = sh.get((s, t), 0) + cf
        for (s, t), c in sh.items():
            key = (a + alpha, b + beta, s + i, t + j)
            out[key] = out.get(key, 0) + c
    return {k_: v for k_, v in out.items() if v != 0}


L1OP = {(0, 0): {(0, 0): 1}, (0, 1): {(0, 0): -1}, (1, 0): {(0, 0): -1}, (3, 0): {(0, 1): -1}}
LNOP = {(0, 0): {(0, 0): 1}, (1, 0): {(0, 0): -1}, (1, 1): {(0, 0): -1},
        (3, 0): {(0, 1): -1, (0, 0): 1}, (3, 1): {(0, 1): -2, (0, 0): 2}, (3, 2): {(0, 1): -1, (0, 0): 1}}


def gens_in_box(gen, gbox, A, B, mono_ok):
    ga, gb = gbox
    res = []
    if A < ga or B < gb:
        return res
    for alpha in range(0, A - ga + 1):
        for beta in range(0, B - gb + 1):
            for i in range(0, 8):
                for j in range(0, 8):
                    op = left_multiple(gen, alpha, beta, i, j)
                    if all(a <= A and b <= B and mono_ok(ii, jj) for (a, b, ii, jj) in op):
                        res.append(op)
    return res


def exact_ok(tab, unk, vec, k0, m0):
    nz = [(c, u) for c, u in zip(vec, unk) if c]
    for k in range(k0, K + 1):
        for m in range(m0, M + 1):
            if sum(c * k ** i * m ** j * tab[k - a][m - b] for c, (a, b, i, j) in nz) != 0:
                return False
    return True


def konly_exp(tab, cid, name, params):
    allok = True
    desc = []
    for (A, B, D) in params:
        unk = unknowns(A, B, [(i, 0) for i in range(D + 1)])
        rows = rows_mod(tab, unk, A, B, PR)
        r = rank_mod(rows, PR)
        allok &= (r == len(unk))
        desc.append('(A,B,deg)=(%d,%d,%d):%d unknowns/%d eqs rank %d' % (A, B, D, len(unk), len(rows), r))
    report(cid, allok, '%s: NO recurrence sum_{a<=A,b<=B} p_ab(k) X(k-a,m-b)=0 with coefficients depending on k only, on '
                       'quadrant [A..40]x[B..40] (full column rank mod p=2^31-1 => none over Q; each set covers all '
                       'smaller A,B,deg): %s' % (name, '; '.join(desc)))


def km_exp(tab, cid, name, gen, gbox, params, pred, sep=False):
    allok = True
    desc = []
    for prm in params:
        if sep:
            A, B, Dk, Dm = prm
            monos = [(i, j) for i in range(Dk + 1) for j in range(Dm + 1)]
            mono_ok = (lambda Dk_, Dm_: (lambda ii, jj: ii <= Dk_ and jj <= Dm_))(Dk, Dm)
        else:
            A, B, D = prm
            monos = [(i, j) for i in range(D + 1) for j in range(D + 1 - i)]
            mono_ok = (lambda D_: (lambda ii, jj: ii + jj <= D_))(D)
        unk = unknowns(A, B, monos)
        rows = rows_mod(tab, unk, A, B, PR)
        r = rank_mod(rows, PR)
        kd = len(unk) - r
        gs = gens_in_box(gen, gbox, A, B, mono_ok)
        idx = {u: t for t, u in enumerate(unk)}
        vecs = []
        for g in gs:
            v = [0] * len(unk)
            for key, c in g.items():
                v[idx[key]] += c
            vecs.append(v)
        gr = rank_mod(vecs, PR) if vecs else 0
        ex = all(exact_ok(tab, unk, v, A, B) for v in vecs)
        pv = pred(*prm)
        this = (kd == gr == len(vecs) == pv) and ex
        allok &= this
        desc.append('%s:%du/%deq ker=%d pred=%d gens=%d' % (str(prm), len(unk), len(rows), kd, pv, len(vecs)))
    report(cid, allok, '%s: kernel (mod p) == span of exact left multiples of the generator, dimension == formula; %s'
           % (name, '; '.join(desc)))


def predU(A, B, D):
    return (A - 2) * B * D * (D + 1) // 2 if (A >= 3 and B >= 1 and D >= 1) else 0


def predUsep(A, B, Dk, Dm):
    return (A - 2) * B * (Dk + 1) * Dm if (A >= 3 and B >= 1 and Dm >= 1) else 0


def predN(A, B, D):
    return (A - 2) * (B - 1) * D * (D + 1) // 2 if (A >= 3 and B >= 2 and D >= 1) else 0


def predNsep(A, B, Dk, Dm):
    return (A - 2) * (B - 1) * (Dk + 1) * Dm if (A >= 3 and B >= 2 and Dm >= 1) else 0


konly_exp(T, 'C3B-E1', 'U', [(6, 6, 6), (10, 3, 6), (3, 10, 6), (4, 4, 12), (15, 1, 8), (1, 15, 8)])
km_exp(T, 'C3B-E2', 'U, coefficients in Q[k,m] (total degree<=D), generator L1=1-S_m^-1-S_k^-1-m S_k^-3, '
                    'formula (A-2)B D(D+1)/2', L1OP, (3, 1),
       [(3, 1, 1), (3, 1, 3), (5, 2, 2), (6, 2, 3), (4, 3, 4), (6, 4, 2), (2, 6, 4), (6, 0, 4)], predU)
km_exp(T, 'C3B-E2S', 'U, coefficients with deg_k<=Dk, deg_m<=Dm, formula (A-2)B(Dk+1)Dm', L1OP, (3, 1),
       [(4, 2, 3, 2), (5, 3, 1, 3), (3, 2, 5, 0)], predUsep, sep=True)
konly_exp(NT, 'C3B-E3A', 'N', [(6, 6, 6), (10, 3, 6), (3, 10, 6), (4, 4, 12), (15, 1, 8), (1, 15, 8)])
km_exp(NT, 'C3B-E3B', 'N, coefficients in Q[k,q] (total degree<=D), generator L_N=1-S_k^-1-S_k^-1S_q^-1-(q-1)S_k^-3(1+S_q^-1)^2, '
                      'formula (A-2)(B-1)D(D+1)/2', LNOP, (3, 2),
       [(3, 2, 1), (3, 2, 3), (5, 3, 2), (6, 3, 3), (4, 4, 4), (6, 4, 2), (3, 1, 3), (2, 4, 3)], predN)
km_exp(NT, 'C3B-E3S', 'N, coefficients with deg_k<=Dk, deg_q<=Dq, formula (A-2)(B-1)(Dk+1)Dq', LNOP, (3, 2),
       [(4, 3, 3, 2), (5, 4, 1, 3), (3, 3, 5, 0)], predNsep, sep=True)

npass = sum(1 for r in RESULTS if r)
nfail = len(RESULTS) - npass
print('# elapsed %.1fs (numpy=%s)' % (time.time() - T0, HAVE_NP))
print('SUMMARY c3b pass=%d fail=%d' % (npass, nfail))
sys.exit(0 if nfail == 0 else 1)
