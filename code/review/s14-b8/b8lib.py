# -*- coding: utf-8 -*-
"""复核者 s14-b8 的独立工具（2026-10-08）。不 import 项目里的任何代码。

真值的出发点是原始定义：合法序列 h=(h_1..h_k) ∈ {0..m}^k，每个相邻三元组 (a,b,c) 满足 b==c 或 a>=max(b,c)。
本模块提供：
  - legal / U_brute / N_brute：按定义暴力枚举（小 k）；
  - U_dp_exact_row：按定义的转移 DP（状态=最后两个值，用后缀和），精确整数；
  - U_dp_modp_all：同一个 DP 的 numpy 模素数版本；
  - U_rec_table：自己推导的「最大值第一次出现位置」递推 U_k(m)=U_k(m-1)+U_{k-1}(m)+m*U_{k-3}(m)，
    （U_{-1}=1、U_{-2}=0）——只当作快速的精确表，所有用途都对照上面两个 DP；
  - newton_coeffs / N_row：由 U_k(0..k) 得牛顿前向差分系数（U_k(m)=Σ d_q C(m,q)）与 N(k,q)（值域恰为 {1..q} 的合法词数，
    由 U_k(m)=Σ N(k,q) C(m+1,q) 反演）；
  - gneg_iter：G_{-j} 递推（c5a 定理 4.3）截到 x^K。
"""
import itertools
from fractions import Fraction
from math import comb, isqrt

import numpy as np


# ---------------------------------------------------------------- 定义与暴力枚举
def legal(seq):
    for i in range(len(seq) - 2):
        a, b, c = seq[i], seq[i + 1], seq[i + 2]
        if not (b == c or a >= max(b, c)):
            return False
    return True


def U_brute(k, m):
    return sum(1 for s in itertools.product(range(m + 1), repeat=k) if legal(s))


def N_brute(k):
    """N(k,q)，q=0..k：枚举 {1..k}^k 中的合法词，按值域是否恰为某个 {1..q} 归类。"""
    out = [0] * (k + 1)
    if k == 0:
        out[0] = 1
        return out
    for s in itertools.product(range(1, k + 1), repeat=k):
        st = set(s)
        q = len(st)
        if max(st) == q and legal(s):
            out[q] += 1
    return out


# ---------------------------------------------------------------- 按定义的转移 DP
def U_dp_exact_row(K, m):
    """[U_0(m),...,U_K(m)]，精确整数。cnt[a][b]=以 (a,b) 结尾的合法前缀数；
    转移到 c：c==b 时任意 a 都合法；c!=b 时要 a>=max(b,c)。"""
    n = m + 1
    res = [1, n, n * n][:K + 1]
    if K < 3:
        return res
    cnt = np.ones((n, n), dtype=object)
    idx = np.arange(n)
    Mx = np.maximum.outer(idx, idx)
    Bi = np.broadcast_to(idx[:, None], (n, n))
    for _k in range(3, K + 1):
        S = np.cumsum(cnt[::-1, :], axis=0)[::-1, :]      # S[t,b] = Σ_{a>=t} cnt[a,b]
        new = S[Mx, Bi]                                   # new[b,c] = S[max(b,c), b]
        new[idx, idx] = S[0, idx]                         # c==b：Σ_a cnt[a,b]
        cnt = new
        res.append(int(cnt.sum()))
    return res


def U_dp_modp_all(K, M, P):
    """V[k,m] = U_k(m) mod P（0<=k<=K，0<=m<=M），同一个 DP 的 int64 版本（P<2^31）。"""
    V = np.zeros((K + 1, M + 1), dtype=np.int64)
    for m in range(M + 1):
        n = m + 1
        V[0, m] = 1 % P
        if K >= 1:
            V[1, m] = n % P
        if K >= 2:
            V[2, m] = (n * n) % P
        if K < 3:
            continue
        cnt = np.ones((n, n), dtype=np.int64)
        idx = np.arange(n)
        Mx = np.maximum.outer(idx, idx)
        Bi = np.broadcast_to(idx[:, None], (n, n))
        for k in range(3, K + 1):
            S = np.cumsum(cnt[::-1, :], axis=0)[::-1, :] % P
            new = S[Mx, Bi]
            new[idx, idx] = S[0, idx]
            cnt = new
            V[k, m] = int(cnt.sum() % P)
    return V


# ---------------------------------------------------------------- 自己推导的快速递推（对照 DP 使用）
def U_rec_table(K, M):
    """U[k][m]，0<=k<=K，0<=m<=M。按最大值 m 第一次出现的位置 i 分类：
    不出现 U_k(m-1)；i=1 时后面任意，U_{k-1}(m)；i=2 时 h_1<m 有 m 种、且必须 h_3=m，之后任意，m*U_{k-3}(m)；
    i>=3 不可能。约定 U_{-1}=1（k=2），U_{-2}=0（k=1）。"""
    U = [[0] * (M + 1) for _ in range(K + 1)]

    def get(k, m):
        if k == -1:
            return 1
        if k == -2:
            return 0
        return U[k][m]

    for m in range(M + 1):
        for k in range(K + 1):
            if k == 0 or m == 0:
                U[k][m] = 1
            else:
                U[k][m] = U[k][m - 1] + get(k - 1, m) + m * get(k - 3, m)
    return U


# ---------------------------------------------------------------- 多项式基
def diff_table_first(vals):
    """返回 [Δ^0 f(0), Δ^1 f(0), ..., Δ^{n-1} f(0)]，vals[i]=f(i)。"""
    d = list(vals)
    out = [d[0]]
    for _ in range(1, len(vals)):
        d = [d[i + 1] - d[i] for i in range(len(d) - 1)]
        out.append(d[0])
    return out


def newton_coeffs(Urow_k, k):
    """U_k(m) = Σ_{q=0}^{k} d_q C(m,q)，d_q = Δ^q U_k(0)；需要 Urow_k[0..k]。"""
    return diff_table_first([Urow_k[m] for m in range(k + 1)])


def N_row(Urow_k, k):
    """N(k,q)，q=0..k。F(n):=Σ_q N(k,q)C(n,q)，F(n)=U_k(n-1)（n>=1，按值域选取的计数），F(0)=N(k,0)=[k==0]。"""
    f = [1 if k == 0 else 0] + [Urow_k[m] for m in range(k)]
    return diff_table_first(f)


def binom_any(n, q):
    """整数 n（任意符号）上的 C(n,q)=n(n-1)...(n-q+1)/q!。"""
    if q < 0:
        return 0
    if n >= 0:
        return comb(n, q)
    return (-1) ** q * comb(q - n - 1, q)


def eval_newton(dq, m):
    """Σ_q dq[q]·C(m,q)，m 为任意整数或 Fraction（逐项递推 C(m,q)=C(m,q-1)(m-q+1)/q）。"""
    if isinstance(m, Fraction):
        tot, b = Fraction(0), Fraction(1)
        for q, c in enumerate(dq):
            if q > 0:
                b = b * (m - q + 1) / q
            tot += c * b
        return tot
    tot, b = 0, 1
    for q, c in enumerate(dq):
        if q > 0:
            b = b * (m - q + 1) // q
        tot += c * b
    return tot


def eval_Nbasis(Nk, m):
    """Σ_q N(k,q) C(m+1,q)（作者笔记 (0.1) 的基；这里只作第二种求值对照）。"""
    return sum(Nk[q] * binom_any(m + 1, q) for q in range(len(Nk)))


# ---------------------------------------------------------------- G_{-j} 递推
def gneg_iter(K, J):
    """依次给出 (j, g)，g[k]=U_k(-j)（k<=K），j=1..J。G_{-1}=1，G_{-j-1}=(1-x+jx^3)G_{-j}+jx^2。"""
    g = [0] * (K + 1)
    g[0] = 1
    yield 1, g
    for j in range(1, J):
        new = [0] * (K + 1)
        for k in range(K + 1):
            v = g[k]
            if k >= 1:
                v -= g[k - 1]
            if k >= 3:
                v += j * g[k - 3]
            if k == 2:
                v += j
            new[k] = v
        g = new
        yield j + 1, g


# ---------------------------------------------------------------- 数论小工具
def is_prime_td(n):
    """试除法（n < 2^62 足够快到 ~5·10^9）。"""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    r = isqrt(n)
    f = 3
    while f <= r:
        if n % f == 0:
            return False
        f += 2
    return True


def primes_upto(n):
    if n < 2:
        return []
    sieve = bytearray([1]) * (n + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n + 1) if sieve[i]]


def vp(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def lcm_upto(k):
    L = 1
    for p in primes_upto(k):
        pe = p
        while pe * p <= k:
            pe *= p
        L *= pe
    return L


def s_of(k):
    return (k + 2) // 3


def J_formula(k):
    return k * (k * k - k - 4) // 2 - k + 2


def theta_fracs(Nk, k):
    """θ_q=(q+1)N(k,q)/N(k,q+1)-q+1，q=1..k-1（Fraction）。"""
    return [Fraction((q + 1) * Nk[q], Nk[q + 1]) - q + 1 for q in range(1, k)]


def Jcut(Nk, k):
    """max_q ceil(θ_q)（k>=2）；k=1 时返回 1（窗口 (s_1,1] 为空）。j>Jcut 时 T_1<...<T_k。"""
    if k < 2:
        return 1
    best = None
    for th in theta_fracs(Nk, k):
        c = -((-th.numerator) // th.denominator)
        best = c if best is None else max(best, c)
    return best
