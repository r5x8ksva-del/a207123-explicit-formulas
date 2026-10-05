# -*- coding: utf-8 -*-
"""c3a（C-3 显式母函数）探索用的公共函数。只依赖 core/polylib，纯整数 / Fraction。

记号：U_k(m)、F(x,t)=sum U_k(m) x^k t^m、b_i=1-x-i x^3、P_m=prod_{i<=m} b_i、
lambda=(1-x)/x^3、u=x^3/(1-x)、a=-t/x^3。
"""
import sys
import os
from fractions import Fraction
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(HERE)
if CODE not in sys.path:
    sys.path.insert(0, CODE)

from core import U_fast_table, good, U_multichain, U_list, N_brute, N_from_U, PROMPT_TABLE  # noqa: E402
from polylib import P_poly, b_poly, pmul, padd, psub, pscale, trim, series_inv  # noqa: E402


# ---------------------------------------------------------------------------
# 1. 定义层：高度 DP 的细分统计（直接实现第 1 节 (b) 的三元组条件）
# ---------------------------------------------------------------------------
def dp_stats(m, K):
    """对固定 m 返回 (tot, notasc, asc_to)：
    tot[k]      = 合法序列数 U_k(m)
    notasc[k]   = 不以上升结尾（k<=1，或 h_{k-1} >= h_k）的合法序列数
    asc_to[k][j]= 以上升结尾且末项为 j（h_{k-1} < h_k = j）的合法序列数
    k = 0..K。直接按 good(a,b,c) 做状态 (h_{k-1}, h_k) 的转移。"""
    n = m + 1
    tot, notasc, asc_to = [1], [1], [[0] * n]
    if K >= 1:
        tot.append(n); notasc.append(n); asc_to.append([0] * n)
    if K >= 2:
        cnt = [[1] * n for _ in range(n)]   # cnt[a][b]
        for k in range(2, K + 1):
            if k > 2:
                new = [[0] * n for _ in range(n)]
                for a in range(n):
                    for b in range(n):
                        v = cnt[a][b]
                        if v:
                            for c in range(n):
                                if good(a, b, c):
                                    new[b][c] += v
                cnt = new
            tot.append(sum(map(sum, cnt)))
            notasc.append(sum(cnt[a][b] for a in range(n) for b in range(n) if a >= b))
            asc_to.append([sum(cnt[a][j] for a in range(j)) for j in range(n)])
    return tot, notasc, asc_to


def brute_stats(m, k):
    """DFS 枚举 {0..m}^k 中全部合法序列（小规模锚点），返回 (tot, notasc, asc_to)。"""
    res = [0, 0, [0] * (m + 1)]
    seq = []

    def dfs():
        if len(seq) == k:
            res[0] += 1
            if k <= 1 or seq[-2] >= seq[-1]:
                res[1] += 1
            else:
                res[2][seq[-1]] += 1
            return
        for v in range(m + 1):
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            dfs()
            seq.pop()

    dfs()
    return res[0], res[1], res[2]


def stats_tables(K, M):
    """TOT[k][m], NA[k][m], AS[k][m][j]（j<=m）。"""
    cols = [dp_stats(m, K) for m in range(M + 1)]
    TOT = [[cols[m][0][k] for m in range(M + 1)] for k in range(K + 1)]
    NA = [[cols[m][1][k] for m in range(M + 1)] for k in range(K + 1)]
    AS = [[cols[m][2][k] for m in range(M + 1)] for k in range(K + 1)]
    return TOT, NA, AS


# ---------------------------------------------------------------------------
# 2. 截断幂级数（x 的整数系数，长度 K+1）
# ---------------------------------------------------------------------------
def zero(K):
    return [0] * (K + 1)


def one(K):
    r = [0] * (K + 1)
    r[0] = 1
    return r


def smul(p, q, K):
    """截断乘法 mod x^{K+1}（p,q 为长度 K+1 的列表）。"""
    r = [0] * (K + 1)
    for i in range(K + 1):
        a = p[i]
        if a:
            for j in range(K + 1 - i):
                b = q[j]
                if b:
                    r[i + j] += a * b
    return r


def sadd(p, q):
    return [a + b for a, b in zip(p, q)]


def sinv_int(p, K):
    """1/p mod x^{K+1}，要求 p[0] = ±1（整数系数保持整数）。"""
    assert p[0] in (1, -1)
    r = [0] * (K + 1)
    r[0] = p[0]
    for k in range(1, K + 1):
        s = 0
        for i in range(1, k + 1):
            if i < len(p) and p[i]:
                s += p[i] * r[k - i]
        r[k] = -s * p[0]
    return r


def pad(p, K):
    p = list(p)[:K + 1]
    return p + [0] * (K + 1 - len(p))


# ---------------------------------------------------------------------------
# 3. 形式 Laplace 表示的直接展开（EGF 记法：存 N!·[s^N]，于是 L_s = 各 EGF 系数之和）
#    Y = (1/A) * L_s[ exp((t/x^3)(e^{v s}-1)) * gamma(x, t e^{v s}) ],  v = x^3/A
#    A = 1-x 时就是 F 的表示（gamma = 1 + x^2 t/(1-t)^2）。
# ---------------------------------------------------------------------------
def egf_mul(f, g, K, Nmax):
    """两个 EGF（dict N->poly）的乘积，只保留 N<=Nmax。"""
    r = {}
    for i, fi in f.items():
        for j, gj in g.items():
            N = i + j
            if N > Nmax:
                continue
            c = comb(N, i)
            prod = smul(fi, gj, K)
            if any(prod):
                if N in r:
                    r[N] = [a + c * b for a, b in zip(r[N], prod)]
                else:
                    r[N] = [c * b for b in prod]
    return r


def laplace_solve(gamma_cols, A, K, M):
    """gamma_cols[m] = gamma_m(x)（长度 K+1 的整数列表），gamma(x,t)=sum_m gamma_m(x) t^m。
    A：首项 1 的整数多项式（列表）。返回 Y[k][m]（Fraction 或 int），
    Y = (1/A) L_s[ Phi_A(s) gamma(x, t e^{v s}) ]，v = x^3/A。"""
    Ainv = sinv_int(pad(A, K), K)
    Nmax = K // 3 + M + 1              # [s^N t^m] 的 x 赋值 >= 3N-3m，故 N <= K/3 + m
    # (1/A)^N
    Ainv_pow = [one(K)]
    for N in range(1, Nmax + 2):
        Ainv_pow.append(smul(Ainv_pow[-1], Ainv, K))
    # E(s) = (e^{vs}-1)/x^3 的 EGF 系数：v^N/x^3 = x^{3N-3} A^{-N}
    E = {}
    for N in range(1, Nmax + 1):
        if 3 * N - 3 <= K:
            E[N] = [0] * (3 * N - 3) + Ainv_pow[N][:K + 1 - (3 * N - 3)]
    # Pw[n] = E^n / n!
    Pw = [{0: one(K)}]
    for n in range(1, M + 1):
        prod = egf_mul(E, Pw[-1], K, Nmax)
        q = {}
        for N, p in prod.items():
            assert all(c % n == 0 for c in p), 'E^n/n! 非整数？'
            q[N] = [c // n for c in p]
        Pw.append(q)
    # Gam[m] = gamma_m(x) e^{m v s} 的 EGF：m^N x^{3N} A^{-N} gamma_m(x)
    Gam = []
    for m in range(M + 1):
        gm = pad(gamma_cols[m], K) if m < len(gamma_cols) else zero(K)
        d = {}
        if any(gm):
            for N in range(0, Nmax + 1):
                if 3 * N > K:
                    break
                if m == 0 and N > 0:
                    break
                base = [0] * (3 * N) + Ainv_pow[N][:K + 1 - 3 * N]
                coef = m ** N
                d[N] = [coef * c for c in smul(base, gm, K)]
        Gam.append(d)
    # Y_m = sum_n L[Pw[n] * Gam[m-n]]
    Ycols = []
    for m in range(M + 1):
        acc = zero(K)
        for n in range(m + 1):
            pr = egf_mul(Pw[n], Gam[m - n], K, Nmax)
            for N, p in pr.items():
                acc = sadd(acc, p)
        Ycols.append(smul(acc, Ainv, K))
    return [[Ycols[m][k] for m in range(M + 1)] for k in range(K + 1)]


def gamma_F_cols(K, M):
    """F 的右端 1 + x^2 t/(1-t)^2 按 t^m 拆列。"""
    cols = []
    for m in range(M + 1):
        c = zero(K)
        if m == 0:
            c[0] = 1
        elif K >= 2:
            c[2] = m
        cols.append(c)
    return cols


def laplace_F(K, M):
    A = [1, -1]
    return laplace_solve(gamma_F_cols(K, M), A, K, M)


# ---------------------------------------------------------------------------
# 4. PDE 检查
# ---------------------------------------------------------------------------
def pde_residual_F(T, K, M):
    """(1-x-t)F - x^3 t F_t - (1 + x^2 t/(1-t)^2) 的系数，返回非零项列表。"""
    def c(k, m):
        if k < 0 or m < 0:
            return 0
        return T[k][m]
    bad = []
    for k in range(K + 1):
        for m in range(M + 1):
            lhs = c(k, m) - c(k - 1, m) - c(k, m - 1) - m * c(k - 3, m)
            rhs = (1 if (k == 0 and m == 0) else 0) + (m if (k == 2 and m >= 1) else 0)
            if lhs != rhs:
                bad.append((k, m, lhs, rhs))
    return bad
