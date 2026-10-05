# -*- coding: utf-8 -*-
"""check_c2a：C-2 最简显式公式（代数路线）的正式核对模块。

契约：从任意目录 `py -3.14 check_c2a.py` 运行；只导入 code/core.py 与 code/polylib.py；
每条结论一行 PASS/FAIL <id> <描述含范围>；最后一行 SUMMARY c2a pass=<n> fail=<n>；全部通过退出码 0。
只用精确整数 / Fraction（本模块没有任何浮点检查）。
对照基准：core.U_fast_table（第 1 节 (b) 的高度 DP），并在 dp_anchor 中把它锚定到参考实现、多重链定义与原题直接计数。
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial
from itertools import product

CODE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, CODE)
from core import (binom, h_complete, stirling2_table, U_fast_table, U_height_table,  # noqa: E402
                  U_multichain, a_direct, good, N_brute, N_from_U)
from polylib import (P_poly, b_poly, pmul, padd, psub, pscale, pshift, pdiv, pderiv, trim,  # noqa: E402
                     series_inv, series_mul)

T0 = time.time()
RESULTS = []


# ASCII-only descriptions (stdout encoding independent); the Chinese text passed to report() is kept as source comments.
DESC = {
    'dp_anchor': 'baseline: core.U_fast_table == reference U_list (k<=30,m<=12) == multichain definition (k<=7,m<=4); a_direct(n,k)=U(ceil)U(floor) (k<=4,n<=8)',
    'rstirling_def': 'Broder r-Stirling S_r(n,k) (set partitions of [n] into k blocks, 1..r in distinct blocks; brute force) == h_{n-k}(r..k) (core.h_complete), 0<=r<=k<=n<=9; zero for k<r',
    'rstirling_rec_gf': 'r-Stirling recurrence == h_{n-k}(r..k) (n<=30); GF sum_n S_r(n,k) z^n = z^k/prod_{i=r}^k(1-iz) (r<=k<=10, 21 coeffs); h_s(0..m)=h_s(1..m)=S(m+s,m) (m,s<=20)',
    'rstirling_cross': 'Broder cross identity h_s(j..m) = sum_t C(m-j+s,m-j+t) S(m-j+t,m-j) j^(s-t) (positive Stirling form of the r-Stirling atoms), 0<=j<=m<=20, s<=20',
    'nabla_rstirling':'(1/t!) nabla^t i^p at i=m equals h_{p-t}(m-t..m) = S_{m-t}(p+m-t,m) (0 if p<t), 0<=t<=m<=20, p<=40',
    'theta_rational_identity': 'polynomial identity sum_r (-1)^r C(t,r) prod_{v in [m-t,m], v!=m-r} b_v = t! x^{3t}, i.e. sum_r (-1)^r C(t,r)/b_{m-r} = t! x^{3t}/prod_{v=m-t}^m b_v, 0<=t<=m<=20',
    'theta_inner': 'Theta_t(n) = [x^{n-3t}] prod_{v=m-t}^m 1/b_v (series division) = sum_s h_s(m-t..m) C(n-2t-2s,t+s) = termwise c_i-expansion (p=s+t), m<=12, t<=m, 0<=n<3t+45',
    'gf_blocks': 'G_m = 1/P_m + x^2 sum_{j=1}^m j/prod_{v=j}^m b_v = W_m/P_m, coefficientwise vs DP, k<=60, m<=20',
    'form_H': 'H form (all-positive double sum) == DP for k<=30,m<=12 and k<=60,m<=20',
    'form_F3': 'F3 form [x^{k+1}]1/P_m - sum_{j>=1} [x^k] prod_{v=j}^m 1/b_v (r-Stirling inner) == DP for k<=30,m<=12 and k<=60,m<=20',
    'form_Theta': 'prompt (C4) Theta form (incl. k=0) == DP for k<=30,m<=12 and k<=60,m<=20',
    'form_ThetaH': 'H outer + c_i inner (Theta_m(k+3m) + sum_j j Theta_{m-j}(k-2+3(m-j))) == DP for k<=30,m<=12 and k<=60,m<=20',
    'form_F4': 'new c_i partial-fraction form (1/m!) sum_i (-1)^{m-i}C(m,i)[c_i(k+3m)+sum_{j<=i} j i^(j) c_i(k+3m-3j-2)] == DP for k<=30,m<=12 and k<=60,m<=20',
    'gamma_triangle': 'Gamma_m(n;j)=[x^n]prod_{v=j}^m 1/b_v: triangle recurrence == r-Stirling single sum; U = Gamma_m(k;0)+sum_j j Gamma_m(k-2;j) == DP, k<=60, m<=20',
    'theta_vs_H_outer': 'telescoping identity x^3 sum_j j P_{j-1} = P_0 - P_m - x sum_{j=1}^m P_{j-1} (m<=20) => F3-outer == H-outer coefficientwise (k<=60,m<=20); NOT termwise equal: m=1,k=3 terms (8,-2) vs (5,1), both sum to 6',
    'block_factorization': 'unique block factorization: h in {0..m}^k legal <=> parses into S=[v], T=[a,v,v] blocks with weakly decreasing levels plus optional final E=[a,j]; all (m+1)^k sequences, m<=3, k<=7',
    'bijection_phi': 'phi(h)=h.0 (no final ascent) or h.j (ends with E_j) is a bijection onto length-(k+1) legal sequences whose last block is T or [0]; no-final-ascent count = sum_s S(m+s,m)C(k+m-2s,m+s); E_j-ending count = j*Gamma_m(k-2;j); brute force m<=3, k<=8',
    'F4_reduction': 'P_{j-1} == i^(j) x^{3j} and W_m == 1+sum_{j<=i} j i^(j) x^{3j+2} mod b_i, quotient degree <= 3m-1 (0<=i<=m<=15); sum_i (-1)^{m-i}C(m,i) prod_{v!=i} b_v = m! x^{3m} (m<=20)',
    'single_family_facts': 'facts for Theorem S: b_1 has no rational root; N(xi)=1, N(1+xi)=3; mod b_1: x(1+3x^2)==3-2x, (1-x)^2==x^6, W_m==x+x^2, P_m/b_1==(-1)^{m-1}(m-1)! x^{3m}; residue identity W_m(xi)*du/dx(xi)/(dP_m/dx)(xi) = (-1)^m (1+xi) xi^{-3m-2}/(m-1)! exactly in Q(xi), m=1..20',
    'single_family_linsys': 'evidence: linear systems U_k(m) = sum_s A(s) C(k+c-2s,s+e) (k0<=k<=45) inconsistent for m=1..3, k0 in {0,6}, c in [-4,4], e in [-4,6] (594 systems); controls U_k(0)=1 and [x^k]1/P_m (m<=3) solvable',
    'two_family_residue': 'two-family necessary residue conditions: theta_v ~ W_v(xi) xi^{-3m-3} (v=1,2; m<=8); fiber-1 condition has exactly 14 solutions with |a|,|b|<=150 and none satisfies fiber 2 => for every m>=2 no representation x^{g1}A1(u)+x^{g2}A2(u)+Laurent poly with |g_i+3m+3|<=150',
    'N_inversion': 'N(k,q) = sum_{i=1}^q (-1)^{q-i} C(q,i) U_H(k,i-1) == DFS definition N_brute (k<=8) and core inclusion-exclusion N_from_U (k<=40, q<=20)',
}


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, DESC.get(cid, desc)))


# ======================================================================= 公共函数
def hgrid(M, S):
    """H[m][j][s] = h_s(j..m)（递推 h_s(j..m) = h_s(j+1..m) + j h_{s-1}(j..m)），j=m+1 为空集。"""
    H = []
    for m in range(M + 1):
        Hm = [None] * (m + 2)
        Hm[m + 1] = [1] + [0] * S
        for j in range(m, -1, -1):
            nxt, row = Hm[j + 1], [1] + [0] * S
            for s in range(1, S + 1):
                row[s] = nxt[s] + j * row[s - 1]
            Hm[j] = row
        H.append(Hm)
    return H


def c_explicit(i, n):
    """c_i(n) = sum_{0<=l<=n/3} C(n-2l, l) i^l，n<0 时 0。"""
    if n < 0:
        return 0
    return sum(comb(n - 2 * l, l) * i ** l for l in range(n // 3 + 1))


def Gamma_rs(n, j, m, H):
    """Gamma_m(n;j) = sum_s h_s(j..m) C(n+m-j-2s, m-j+s)（n<0 时 0）。"""
    if n < 0:
        return 0
    row = H[m][j]
    return sum(row[s] * binom(n + m - j - 2 * s, m - j + s) for s in range(n // 3 + 1))


def Theta(t, n, m, C):
    s = sum((-1) ** r * comb(t, r) * (C[m - r][n] if n >= 0 else 0) for r in range(t + 1))
    q, rem = divmod(s, factorial(t))
    if rem:
        raise ArithmeticError('Theta not integral')
    return q


def U_H(k, m, H):
    tot = Gamma_rs(k, 0, m, H)
    if k >= 2:
        tot += sum(j * Gamma_rs(k - 2, j, m, H) for j in range(1, m + 1))
    return tot


def U_F3(k, m, H):
    return Gamma_rs(k + 1, 0, m, H) - sum(Gamma_rs(k, j, m, H) for j in range(1, m + 1))


def U_Theta(k, m, C):
    return Theta(m, k + 1 + 3 * m, m, C) - sum(Theta(t, k + 3 * t, m, C) for t in range(m))


def U_ThetaH(k, m, C):
    def Gc(n, j):
        t = m - j
        return Theta(t, n + 3 * t, m, C)
    tot = Gc(k, 0)
    tot += sum(j * Gc(k - 2, j) for j in range(1, m + 1))
    return tot


def U_F4(k, m, C):
    tot = 0
    for i in range(m + 1):
        def cv(n):
            return C[i][n] if n >= 0 else 0
        inner, ff = cv(k + 3 * m), 1
        for j in range(1, i + 1):
            ff *= (i - j + 1)
            inner += j * ff * cv(k + 3 * m - 3 * j - 2)
        tot += (-1) ** (m - i) * comb(m, i) * inner
    q, rem = divmod(tot, factorial(m))
    if rem:
        raise ArithmeticError('F4 not integral')
    return q


def W_poly(m):
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
    return W


def prod_b(lo, hi):
    p = [1]
    for v in range(lo, hi + 1):
        p = pmul(p, b_poly(v))
    return p


KMAX, MMAX = 60, 20
T = U_fast_table(KMAX, MMAX)
H = hgrid(MMAX, KMAX + 2)
C = [[c_explicit(i, n) for n in range(KMAX + 3 * MMAX + 5)] for i in range(MMAX + 1)]

# ======================================================================= 0. 基准锚定
ok = U_height_table(30, 12) == [row[:13] for row in T[:31]]
ok = ok and all(U_multichain(k, m) == T[k][m] for k in range(1, 8) for m in range(0, 5))
ok = ok and all(a_direct(n, k) == T[k][(n + 1) // 2] * T[k][n // 2] for k in range(1, 5) for n in range(0, 9))
report('dp_anchor', ok, 'core.U_fast_table == 参考实现 U_list (k<=30,m<=12) == 多重链定义 (k<=7,m<=4)，且 a_direct(n,k)=U(ceil)U(floor) (k<=4,n<=8)')

# ======================================================================= 1. r-Stirling 数
def set_partitions(n):
    if n == 0:
        yield ()
        return
    a = [0] * n

    def rec(i, mx):
        if i == n:
            yield tuple(a)
            return
        for v in range(mx + 2):
            a[i] = v
            yield from rec(i + 1, max(mx, v))
    yield from rec(1, 0)


NB = 9
brute = {}
for n in range(NB + 1):
    for a in set_partitions(n):
        k = (max(a) + 1) if n else 0
        for r in range(n + 1):
            if len(set(a[:r])) == r:
                brute[(n, k, r)] = brute.get((n, k, r), 0) + 1
ok = all(brute.get((n, k, r), 0) == h_complete(n - k, r, k) for n in range(NB + 1) for r in range(n + 1) for k in range(r, n + 1))
ok = ok and all(brute.get((n, k, r), 0) == 0 for n in range(NB + 1) for r in range(n + 1) for k in range(0, r))
report('rstirling_def', ok, 'Broder r-Stirling {n\\k}_r（{1..n} 分成 k 块且 1..r 两两异块，暴力枚举分拆）== h_{n-k}(r..k)（core.h_complete），0<=r<=k<=n<=%d；k<r 时为 0' % NB)

R = {}
for r in range(0, 31):
    for n in range(r, 31):
        for k in range(0, n + 1):
            R[(n, k, r)] = (1 if k == r else 0) if n == r else k * R.get((n - 1, k, r), 0) + R.get((n - 1, k - 1, r), 0)
ok = all(R[(n, k, r)] == h_complete(n - k, r, k) for r in range(31) for n in range(r, 31) for k in range(r, n + 1))
ok2 = True
for r in range(0, 11):
    for k in range(r, 11):
        den = [1]
        for i in range(r, k + 1):
            den = pmul(den, [1, -i])
        ser = series_inv(den, 21)
        ok2 = ok2 and all(R[(n, k, r)] == ser[n - k] for n in range(k, min(k + 21, 31)))
S2 = stirling2_table(45)
ok3 = all(h_complete(s, 0, m) == h_complete(s, 1, m) == S2[m + s][m] for m in range(21) for s in range(21))
report('rstirling_rec_gf', ok and ok2 and ok3,
       '递推 {n\\k}_r = k{n-1\\k}_r + {n-1\\k-1}_r（{r\\k}_r=[k=r]）== h_{n-k}(r..k) (n<=30)；母函数 sum_n {n\\k}_r z^n = z^k/prod_{i=r}^k(1-iz) (r<=k<=10, 21 项)；h_s(0..m)=h_s(1..m)=S(m+s,m) (m,s<=20)')

ok = all(sum(comb(m - j + s, m - j + t) * S2[m - j + t][m - j] * j ** (s - t) for t in range(s + 1)) == h_complete(s, j, m)
         for m in range(21) for j in range(m + 1) for s in range(21))
report('rstirling_cross', ok, 'cross')

ok = True
for m in range(0, 21):
    for t in range(0, m + 1):
        for p in range(0, 41):
            s = sum((-1) ** r * comb(t, r) * (m - r) ** p for r in range(t + 1))
            if p < t:
                ok = ok and s == 0
            else:
                q, rem = divmod(s, factorial(t))
                ok = ok and rem == 0 and q == h_complete(p - t, m - t, m)
                if p + m - t <= 30:
                    ok = ok and q == R[(p + m - t, m, m - t)]
report('nabla_rstirling', ok, '(1/t!) nabla^t i^p |_{i=m} = h_{p-t}(m-t..m) = {p+m-t\\m}_{m-t}（p<t 时为 0），0<=t<=m<=20, p<=40（0^0=1）')

# ======================================================================= 2. Theta 的内层恒等式
ok = True
for m in range(0, 21):
    for t in range(0, m + 1):
        lhs = []
        for r in range(t + 1):
            others = [1]
            for v in range(m - t, m + 1):
                if v != m - r:
                    others = pmul(others, b_poly(v))
            lhs = padd(lhs, pscale(others, (-1) ** r * comb(t, r)))
        ok = ok and trim(lhs) == trim(pscale(pshift([1], 3 * t), factorial(t)))
report('theta_rational_identity', ok, '多项式恒等式 sum_r (-1)^r C(t,r) prod_{v=m-t..m, v!=m-r} b_v = t! x^{3t}（即 sum_r (-1)^r C(t,r)/b_{m-r} = t! x^{3t}/prod_{v=m-t}^m b_v），0<=t<=m<=20')

ok = True
for m in range(0, 13):
    for t in range(0, m + 1):
        ser = series_inv(prod_b(m - t, m), 45)
        for n in range(0, 3 * t + 45):
            th = Theta(t, n, m, C)
            ref = int(ser[n - 3 * t]) if n >= 3 * t else 0
            via_h = sum(binom(n - 2 * t - 2 * s, t + s) * H[m][m - t][s] for s in range(0, max(n, 0) // 3 + 1))
            via_c_terms = sum(binom(n - 2 * p, p) * (h_complete(p - t, m - t, m) if p >= t else 0) for p in range(0, n // 3 + 1))
            ok = ok and th == ref == via_h == via_c_terms
report('theta_inner', ok, 'Theta_t(n) = [x^{n-3t}] prod_{v=m-t}^m b_v^{-1}（级数除法）= sum_s h_s(m-t..m) C(n-2t-2s, t+s)（与 c_i 展开逐项相同，p=s+t），m<=12, t<=m, 0<=n<3t+45（n<3t 时为 0）')

# ======================================================================= 3. 母函数与各显式形式
ok = True
for m in range(0, MMAX + 1):
    G = series_inv(P_poly(m), KMAX + 1)
    for j in range(1, m + 1):
        q = series_inv(prod_b(j, m), KMAX + 1)
        G = [a + j * (q[k - 2] if k >= 2 else 0) for k, a in enumerate(G)]
    ok = ok and [int(v) for v in G] == [T[k][m] for k in range(KMAX + 1)]
    W = series_mul(W_poly(m), series_inv(P_poly(m), KMAX + 1), KMAX + 1)
    ok = ok and [int(v) for v in W] == [T[k][m] for k in range(KMAX + 1)]
report('gf_blocks', ok, 'G_m = 1/P_m + x^2 sum_{j=1}^m j/prod_{v=j}^m b_v = W_m/P_m（W_m = 1 + x^2 sum_j j P_{j-1}），逐项对照 DP，k<=%d, m<=%d' % (KMAX, MMAX))

forms = [('form_H', lambda k, m: U_H(k, m, H), 'H 型（草稿 §2，全正项双和）U = sum_s S(m+s,m)C(k+m-2s,m+s) + sum_{j=1}^m j sum_s h_s(j..m) C(k-2+m-j-2s, m-j+s)'),
         ('form_F3', lambda k, m: U_F3(k, m, H), 'F3 型 U = sum_s S(m+s,m)C(k+1+m-2s,m+s) - sum_{j=1}^m sum_s h_s(j..m) C(k+m-j-2s, m-j+s)'),
         ('form_Theta', lambda k, m: U_Theta(k, m, C), '提示词 (C4) Θ 型 U = Theta_m(k+1+3m) - sum_{t<m} Theta_t(k+3t)（含 k=0）'),
         ('form_ThetaH', lambda k, m: U_ThetaH(k, m, C), 'H 外层 + c_i 内层 U = Theta_m(k+3m) + sum_{j=1}^m j Theta_{m-j}(k-2+3(m-j))'),
         ('form_F4', lambda k, m: U_F4(k, m, C), 'c_i 偏分式型（新）U = (1/m!) sum_i (-1)^{m-i} C(m,i)[c_i(k+3m) + sum_{j=1}^i j i^(j) c_i(k+3m-3j-2)]')]
for cid, f, desc in forms:
    ok1 = all(f(k, m) == T[k][m] for k in range(31) for m in range(13))
    ok2 = all(f(k, m) == T[k][m] for k in range(KMAX + 1) for m in range(MMAX + 1))
    report(cid, ok1 and ok2, desc + '，对照 DP：k<=30,m<=12 与 k<=%d,m<=%d 全部相等' % (KMAX, MMAX))

# Gamma 三角递推 + 单 j 和
ok = True
Gm = {}
for m in range(0, MMAX + 1):
    Gm[m] = [1] + [0] * KMAX
    for j in range(m + 1):
        old, new = Gm[j], [0] * (KMAX + 1)
        for n in range(KMAX + 1):
            new[n] = old[n] + (new[n - 1] if n >= 1 else 0) + (m * new[n - 3] if n >= 3 else 0)
        Gm[j] = new
        ok = ok and all(new[n] == Gamma_rs(n, j, m, H) for n in range(KMAX + 1))
    ok = ok and all(Gm[0][k] + (sum(j * Gm[j][k - 2] for j in range(1, m + 1)) if k >= 2 else 0) == T[k][m] for k in range(KMAX + 1))
report('gamma_triangle', ok, 'Gamma_m(n;j) := [x^n] prod_{v=j}^m b_v^{-1} 满足 Gamma_m(n;j) = Gamma_{m-1}(n;j) + Gamma_m(n-1;j) + m Gamma_m(n-3;j) 且 = sum_s h_s(j..m)C(n+m-j-2s,m-j+s)；U = Gamma_m(k;0) + sum_j j Gamma_m(k-2;j)，k<=%d, m<=%d' % (KMAX, MMAX))

# ======================================================================= 4. Θ 与 H 的关系：内层逐项相同，外层差一个望远镜恒等式
ok = True
for m in range(0, MMAX + 1):
    lhs = []
    for j in range(1, m + 1):
        lhs = padd(lhs, pscale(pshift(P_poly(j - 1), 3), j))      # x^3 sum_j j P_{j-1}
    s = []
    for j in range(1, m + 1):
        s = padd(s, P_poly(j - 1))
    rhs = psub(psub(P_poly(0), P_poly(m)), pshift(s, 1))           # P_0 - P_m - x sum_{j<=m} P_{j-1}
    ok = ok and trim(lhs) == trim(rhs)
    for k in range(0, KMAX + 1):
        lhsF3 = Gamma_rs(k + 1, 0, m, H) - sum(Gamma_rs(k, j, m, H) for j in range(1, m + 1))
        rhsH = Gamma_rs(k, 0, m, H) + sum(j * Gamma_rs(k - 2, j, m, H) for j in range(1, m + 1))
        ok = ok and lhsF3 == rhsH
# 反例：项并不逐项相同（m=1,k=3：Θ 型各项 (8,-2)，H 型各项 (5,1)）
th_terms = (Theta(1, 3 + 1 + 3, 1, C), -Theta(0, 3, 1, C))
h_terms = (Gamma_rs(3, 0, 1, H), 1 * Gamma_rs(1, 1, 1, H))
ok = ok and th_terms == (8, -2) and h_terms == (5, 1) and sum(th_terms) == sum(h_terms) == T[3][1]
report('theta_vs_H_outer', ok, '望远镜多项式恒等式 x^3 sum_j jP_{j-1} = P_0 - P_m - x sum_{j=1}^m P_{j-1}（m<=20）⇒ Gamma(k+1;0) - sum_{j>=1} Gamma(k;j) = Gamma(k;0) + sum_j j Gamma(k-2;j)（k<=60,m<=20）；外层并非逐项相同：m=1,k=3 时 Θ 型两项 (8,-2)、H 型两项 (5,1)，和都=6')

# ======================================================================= 5. 块分解与双射 φ（组合证明的暴力核对）
def parse_blocks(h):
    """把序列切成块：返回 [(type, level)] 或 None（切不出来/等级不单调）。"""
    blocks, i, k = [], 0, len(h)
    while i < k:
        if i + 1 < k and h[i + 1] > h[i]:
            if i + 2 < k and h[i + 2] == h[i + 1]:
                blocks.append(('T', h[i + 1]))
                i += 3
            elif i + 2 == k:
                blocks.append(('E', h[i + 1]))
                i += 2
            else:
                return None
        else:
            blocks.append(('S', h[i]))
            i += 1
    lv = [b[1] for b in blocks]
    if any(lv[t] < lv[t + 1] for t in range(len(lv) - 1)):
        return None
    if any(b[0] == 'E' for b in blocks[:-1]):
        return None
    return blocks


def legal(h):
    return all(good(h[i], h[i + 1], h[i + 2]) for i in range(len(h) - 2))


ok = True
for m in range(0, 4):
    for k in range(0, 8):
        for h in product(range(m + 1), repeat=k):
            ok = ok and (parse_blocks(h) is not None) == legal(h)
report('block_factorization', ok, '唯一块分解：h in {0..m}^k 合法 <=> h 能切成 S=[v]、T=[a,v,v](a<v) 块（等级弱减）并可在末尾带一个 E=[a,j](a<j) 块；全体 (m+1)^k 个序列暴力核对，m<=3, k<=7')

ok = True
for m in range(0, 4):
    leg = {k: [h for h in product(range(m + 1), repeat=k) if legal(h)] for k in range(0, 10)}
    for k in range(0, 9):
        img = set()
        for h in leg[k]:
            bl = parse_blocks(h)
            if bl and bl[-1][0] == 'E':
                g = h + (h[-1],)
            else:
                g = h + (0,)
            img.add(g)
        target = set()
        for g in leg[k + 1]:
            bl = parse_blocks(g)
            if bl[-1][0] == 'T' or bl[-1] == ('S', 0):
                target.add(g)
        noasc = sum(1 for h in leg[k] if not (k >= 2 and h[-1] > h[-2]))
        ok = ok and img == target and len(img) == len(leg[k]) == T[k][m]
        ok = ok and noasc == Gamma_rs(k, 0, m, H)
        for j in range(1, m + 1):
            endE = sum(1 for h in leg[k] if k >= 2 and h[-1] == j and h[-2] < j)
            ok = ok and endE == j * Gamma_rs(k - 2, j, m, H)
report('bijection_phi', ok, 'φ(h)=h·0（不以上升结尾）或 h·j（以 E_j 结尾）是 {长 k 合法序列} -> {长 k+1、末块为 T 或 [0] 的合法序列} 的双射；不以上升结尾的个数 = sum_s S(m+s,m)C(k+m-2s,m+s)，以 E_j 结尾的个数 = j·Gamma_m(k-2;j)；暴力 m<=3, k<=8')

# ======================================================================= 6. F4 的模 b_i 约化
ok = True
for m in range(0, 16):
    W = W_poly(m)
    for i in range(0, m + 1):
        bi = b_poly(i)
        V = [1]
        ff = 1
        for j in range(1, i + 1):
            ff *= (i - j + 1)
            V = padd(V, pscale(pshift([1], 3 * j + 2), j * ff))
        q, r = pdiv(psub(W, V), bi)
        ok = ok and trim(r) == [] and len(trim(q)) - 1 <= 3 * m - 1
        for j in range(1, m + 1):
            ffj = 1
            for t in range(j):
                ffj *= (i - t)
            q2, r2 = pdiv(psub(P_poly(j - 1), pscale(pshift([1], 3 * j), ffj)), bi)
            ok = ok and trim(r2) == []
for m in range(0, 21):
    lhs = []
    for i in range(m + 1):
        others = [1]
        for v in range(m + 1):
            if v != i:
                others = pmul(others, b_poly(v))
        lhs = padd(lhs, pscale(others, (-1) ** (m - i) * comb(m, i)))
    ok = ok and trim(lhs) == trim(pscale(pshift([1], 3 * m), factorial(m)))
report('F4_reduction', ok, 'P_{j-1} ≡ i^(j) x^{3j}、W_m ≡ 1 + sum_{j=1}^i j i^(j) x^{3j+2} (mod b_i)，商的次数 <= 3m-1（0<=i<=m<=15）；sum_i (-1)^{m-i}C(m,i) prod_{v!=i} b_v = m! x^{3m}（m<=20）')

# ======================================================================= 7. 否定命题：单族单和不存在
FQ = [Fr(-1), Fr(1), Fr(0), Fr(1)]      # f = x^3 + x - 1 = -b_1


def red(p):
    p = trim(p)
    if not p:
        return []
    return trim([Fr(c) for c in pdiv(p, FQ)[1]])


def finv(a):
    r0, r1 = list(FQ), red(a)
    s0, s1 = [], [Fr(1)]
    while trim(r1):
        q, r = pdiv(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, padd(s0, pscale(pmul(q, s1), -1))
    r0 = trim(r0)
    return red(pscale(s0, Fr(1) / r0[0]))


def fnorm(a):
    cols = [red(pmul(a, pshift([1], i))) for i in range(3)]
    Mx = [[(cols[j][i] if i < len(cols[j]) else Fr(0)) for j in range(3)] for i in range(3)]
    (a1, b1, c1), (a2, b2, c2), (a3, b3, c3) = Mx
    return a1 * (b2 * c3 - b3 * c2) - b1 * (a2 * c3 - a3 * c2) + c1 * (a2 * b3 - a3 * b2)


ok = all(sum(cf * Fr(x) ** e for e, cf in enumerate([1, -1, 0, -1])) != 0 for x in (1, -1))
ok = ok and fnorm([Fr(0), Fr(1)]) == 1 and fnorm([Fr(1), Fr(1)]) == 3
ok = ok and red(psub(pmul([0, 1], [1, 0, 3]), [3, -2])) == [] and red(psub(pmul([1, -1], [1, -1]), pshift([1], 6))) == []
xi = [Fr(0), Fr(1)]
up = red(pmul(red(pmul(pmul(xi, xi), [3, -2])), finv(pmul([1, -1], [1, -1]))))
xinv = finv(xi)
for m in range(1, 21):
    W, Pm = W_poly(m), P_poly(m)
    q, r = pdiv(Pm, b_poly(1))
    ok = ok and trim(r) == []
    ok = ok and red(psub(W, [0, 1, 1])) == []
    ok = ok and red(psub(q, pscale(pshift([1], 3 * m), (-1) ** (m - 1) * factorial(m - 1)))) == []
    lhs = red(pmul(red(pmul(red(W), up)), finv(red(pderiv(Pm)))))
    rhs = [Fr(1), Fr(1)]
    for _ in range(3 * m + 2):
        rhs = red(pmul(rhs, xinv))
    rhs = pscale(rhs, Fr((-1) ** m, factorial(m - 1)))
    ok = ok and red(psub(lhs, rhs)) == []
report('single_family_facts', ok, '定理 S 用到的代数事实：b_1 无有理根（不可约）；N(xi)=1, N(1+xi)=3；mod b_1: x(1+3x^2)≡3-2x, (1-x)^2≡x^6, W_m≡x+x^2, P_m/b_1≡(-1)^{m-1}(m-1)! x^{3m}；留数式 W_m(xi)u\'(xi)/P_m\'(xi) = (-1)^m(1+xi)xi^{-3m-2}/(m-1)!（m=1..20，Q(xi) 中精确运算）')


def solvable(seq, c, e, k0, K):
    s_lo, s_hi = max(0, -e), (K + c - e) // 3
    if s_hi < s_lo:
        return False
    unk = list(range(s_lo, s_hi + 1))
    rows = [[Fr(binom(k + c - 2 * s, s + e)) for s in unk] + [Fr(seq[k])] for k in range(k0, K + 1)]
    pr_ = 0
    for col in range(len(unk)):
        p = next((i for i in range(pr_, len(rows)) if rows[i][col] != 0), None)
        if p is None:
            continue
        rows[pr_], rows[p] = rows[p], rows[pr_]
        pv = rows[pr_][col]
        for i in range(len(rows)):
            if i != pr_ and rows[i][col] != 0:
                fac = rows[i][col] / pv
                rows[i] = [a - fac * b for a, b in zip(rows[i], rows[pr_])]
        pr_ += 1
    return all(rows[i][-1] == 0 for i in range(pr_, len(rows)))


KL = 45
found = [(m, k0, c, e) for m in range(1, 4) for k0 in (0, 6) for c in range(-4, 5) for e in range(-4, 7)
         if solvable([T[k][m] for k in range(KL + 1)], c, e, k0, KL)]
ctrl = solvable([1] * (KL + 1), 0, 0, 0, KL) and all(
    solvable([int(v) for v in series_inv(P_poly(m), KL + 1)], m, m, 0, KL) for m in range(1, 4))
report('single_family_linsys', found == [] and ctrl,
       '数值佐证：U_k(m) = sum_s A(s) C(k+c-2s, s+e) (k0<=k<=45) 的线性方程组对 m=1..3, k0 in {0,6}, c in [-4,4], e in [-4,6] 全部无解（594 个）；对照组 U_k(0)=1 与 [x^k]1/P_m (m<=3) 可解')

# 两族：纤维 1、2 的 m 无关必要条件
class Fld:
    def __init__(self, v):
        self.f = [Fr(-1, v), Fr(1, v), Fr(0), Fr(1)]

    def red(self, p):
        p = trim(p)
        if not p:
            return [Fr(0)] * 3
        r = [Fr(c) for c in pdiv(p, self.f)[1]]
        return r + [Fr(0)] * (3 - len(r))

    def mul(self, a, b):
        return self.red(pmul(a, b))

    def inv(self, a):
        r0, r1 = list(self.f), trim(self.red(a))
        s0, s1 = [], [Fr(1)]
        while trim(r1):
            q, r = pdiv(r0, r1)
            r0, r1 = r1, r
            s0, s1 = s1, padd(s0, pscale(pmul(q, s1), -1))
        r0 = trim(r0)
        return self.red(pscale(s0, Fr(1) / r0[0]))


def det3(a, b, c):
    return a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0]) + a[2] * (b[0] * c[1] - b[1] * c[0])


AMAX = 150
data = {}
ok = True
for v, Wv in ((1, [1, 0, 0, 0, 0, 1]), (2, [1, 0, 0, 0, 0, 2, 0, 0, 4])):
    Fd = Fld(v)
    x_ = [Fr(0), Fr(1), Fr(0)]
    w = Fd.red(Wv)
    upv = Fd.mul(Fd.mul(pmul(x_, x_), [3, -2]), Fd.inv(pmul([1, -1], [1, -1])))
    xi_inv = Fd.inv(x_)
    for m in range(v, 9):
        theta = Fd.mul(Fd.mul(Fd.red(W_poly(m)), upv), Fd.inv(Fd.red(pderiv(P_poly(m)))))
        refv = w
        for _ in range(3 * m + 3):
            refv = Fd.mul(refv, xi_inv)
        ratio = Fd.mul(theta, Fd.inv(refv))
        ok = ok and ratio[1] == 0 and ratio[2] == 0
    pw = {0: [Fr(1), Fr(0), Fr(0)]}
    for g in range(1, AMAX + 1):
        pw[g] = Fd.mul(pw[g - 1], x_)
        pw[-g] = Fd.mul(pw[-g + 1], xi_inv)
    data[v] = (w, pw)
(w1, p1), (w2, p2) = data[1], data[2]
sol1 = [(a, b) for a in range(-AMAX, AMAX + 1) for b in range(a + 1, AMAX + 1) if det3(w1, p1[a], p1[b]) == 0]
both = [(a, b) for (a, b) in sol1 if det3(w2, p2[a], p2[b]) == 0]
report('two_family_residue', ok and both == [] and len(sol1) == 14,
       '两族必要条件：theta_v ∝ W_v(xi)xi^{-3m-3}（v=1,2; m<=8）；纤维 1 条件在 |a|,|b|<=%d 内恰有 14 组解，与纤维 2 条件无公共解 ⇒ 对每个 m>=2，指数满足 |g_i+3m+3|<=%d 的两族表示 x^{g1}A1(u)+x^{g2}A2(u)+Laurent 多项式 不存在' % (AMAX, AMAX))

# ======================================================================= 8. N(k,q) 的显式式（H 型 + 二项式反演）
def N_explicit(k, q):
    if k == 0:
        return 1 if q == 0 else 0
    return sum((-1) ** (q - i) * comb(q, i) * U_H(k, i - 1, H) for i in range(1, q + 1))


ok = True
for k in range(1, 9):
    br = N_brute(k)
    ok = ok and all(N_explicit(k, q) == br.get(q, 0) for q in range(0, k + 1))
ok = ok and all(N_explicit(k, q) == N_from_U(T, k, q) for k in range(1, 41) for q in range(0, 21))
report('N_inversion', ok, 'N(k,q) = sum_{i=1}^q (-1)^{q-i} C(q,i) U_H(k,i-1)（U_H 为 H 型显式式）== DFS 定义 N_brute (k<=8) 与 core 容斥 N_from_U (k<=40, q<=20)')

# ======================================================================= 9. 扩大范围 + 计时比较（k<=200, m<=30）
KB, MB = 200, 30
tm = {}


def timed(name, fn):
    t0 = time.perf_counter()
    out = fn()
    tm[name] = time.perf_counter() - t0
    return out


def lemma1_table(K, M):
    L1 = [[1] * (M + 1)] + [[0] * (M + 1) for _ in range(K)]

    def g(k, m):
        return 1 if k in (0, -1) else (0 if k == -2 else L1[k][m])
    for k in range(1, K + 1):
        for m in range(M + 1):
            L1[k][m] = (L1[k][m - 1] if m else 0) + g(k - 1, m) + m * g(k - 3, m)
    return L1


def linrec_table(K, M):
    out = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        P = P_poly(m)
        n0 = min(K + 1, 3 * m + 1)
        col = [int(v) for v in series_mul(W_poly(m), series_inv(P, n0), n0)]
        for k in range(n0, K + 1):
            col.append(-sum(P[l] * col[k - l] for l in range(1, len(P))))
        for k in range(K + 1):
            out[k][m] = col[k]
    return out


def ntri_table(K, M):
    N = [[0] * (K + 2) for _ in range(K + 1)]
    N[0][0], N[1][1], N[2][1], N[2][2] = 1, 1, 1, 2

    def g(k, q):
        return N[k][q] if (0 <= k and 0 <= q <= K + 1) else 0
    for k in range(3, K + 1):
        for r in range(0, k):
            N[k][r + 1] = g(k - 1, r) + g(k - 1, r + 1) + r * (g(k - 3, r - 1) + 2 * g(k - 3, r) + g(k - 3, r + 1))
    return [[sum(N[k][q] * comb(m + 1, q) for q in range(0, min(k, m + 1) + 1)) for m in range(M + 1)] for k in range(K + 1)]


def tab(f):
    return [[f(k, m) for m in range(MB + 1)] for k in range(KB + 1)]


TB = timed('DP', lambda: U_fast_table(KB, MB))
cands = {}
cands['Lemma1'] = timed('Lemma1', lambda: lemma1_table(KB, MB))
cands['linrec'] = timed('linrec', lambda: linrec_table(KB, MB))
cands['Ntri'] = timed('Ntri', lambda: ntri_table(KB, MB))
HB = timed('rStirling_table', lambda: hgrid(MB, KB // 3 + 2))
CB = timed('c_table', lambda: [[c_explicit(i, n) for n in range(KB + 3 * MB + 5)] for i in range(MB + 1)])
cands['H'] = timed('H', lambda: tab(lambda k, m: U_H(k, m, HB)))
cands['F3'] = timed('F3', lambda: tab(lambda k, m: U_F3(k, m, HB)))
cands['Theta'] = timed('Theta', lambda: tab(lambda k, m: U_Theta(k, m, CB)))
cands['ThetaH'] = timed('ThetaH', lambda: tab(lambda k, m: U_ThetaH(k, m, CB)))
cands['F4'] = timed('F4', lambda: tab(lambda k, m: U_F4(k, m, CB)))
ok = all(v == TB for v in cands.values())
report('bench_k200_m30', ok, 'all U_k(m), 0<=k<=200, 0<=m<=30: Lemma-1 recurrence, fixed-m linear recurrence, N triangle, H, F3, Theta, H-outer+c_i, F4 all == DP; '
       'seconds (this run, noisy): ' + ', '.join('%s %.3f' % (n_, tm[n_]) for n_ in
                                                ['DP', 'Lemma1', 'linrec', 'Ntri', 'rStirling_table', 'c_table', 'H', 'F3', 'Theta', 'ThetaH', 'F4']))

# ======================================================================= 汇总
npass = sum(RESULTS)
nfail = len(RESULTS) - npass
print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY c2a pass=%d fail=%d' % (npass, nfail))
sys.exit(0 if nfail == 0 else 1)
