# -*- coding: utf-8 -*-
"""c2a 子方向（C-2 代数路线）的公式实现库：U_k(m) 的各种显式形式。

约定：binom(a,b)=0 除非 0<=b<=a（与 core.binom 一致）；c_i(n)=0 (n<0)；0^0=1。
所有函数只用精确整数；带除法的公式在除法处断言整除。
"""
import os
import sys
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(HERE)
if CODE not in sys.path:
    sys.path.insert(0, CODE)
from core import binom  # noqa: E402


# ---------------------------------------------------------------- 基本数表
def hgrid(M, S):
    """H[m][j][s] = h_s(j, j+1, ..., m)（完全齐次对称多项式），0<=j<=m+1<=M+1, 0<=s<=S。
    j = m+1 表示空变量集（h_0 = 1, h_s = 0）。递推 h_s(j..m) = h_s(j+1..m) + j*h_{s-1}(j..m)。"""
    H = []
    for m in range(M + 1):
        Hm = [None] * (m + 2)
        Hm[m + 1] = [1] + [0] * S
        for j in range(m, -1, -1):
            nxt = Hm[j + 1]
            row = [0] * (S + 1)
            row[0] = 1
            for s in range(1, S + 1):
                row[s] = nxt[s] + j * row[s - 1]
            Hm[j] = row
        H.append(Hm)
    return H


def c_explicit(i, n):
    """c_i(n) = [x^n] 1/(1-x-i x^3) = sum_{l=0}^{floor(n/3)} C(n-2l, l) i^l；n<0 时为 0。"""
    if n < 0:
        return 0
    return sum(comb(n - 2 * l, l) * i ** l for l in range(n // 3 + 1))


def ctable(I, Nmax):
    """C[i][n] = c_i(n)，0<=i<=I, 0<=n<=Nmax（逐项用显式和计算）。"""
    return [[c_explicit(i, n) for n in range(Nmax + 1)] for i in range(I + 1)]


def cval(C, i, n):
    return C[i][n] if n >= 0 else 0


def binom_table(N):
    """B[a][b] = C(a,b), 0<=a,b<=N（Pascal）。"""
    B = [[0] * (N + 1) for _ in range(N + 1)]
    for a in range(N + 1):
        B[a][0] = 1
        for b in range(1, a + 1):
            B[a][b] = B[a - 1][b - 1] + (B[a - 1][b] if b <= a - 1 else 0)
    return B


# ---------------------------------------------------------------- Gamma 数（三次 Stirling 型）
def Gamma_rs(n, j, m, H):
    """Gamma_m(n; j) := [x^n] prod_{v=j}^m (1-x-v x^3)^{-1}，内层形式 (a)：
    sum_s h_s(j..m) C(n+m-j-2s, m-j+s)。n<0 时为 0。"""
    if n < 0:
        return 0
    row = H[m][j]
    return sum(row[s] * binom(n + m - j - 2 * s, m - j + s) for s in range(n // 3 + 1))


def Theta(t, n, m, C):
    """提示词 (C4) 的 Theta_t(n) = (1/t!) sum_{r=0}^t (-1)^r C(t,r) c_{m-r}(n)（断言整除）。"""
    s = 0
    for r in range(t + 1):
        s += (-1) ** r * comb(t, r) * cval(C, m - r, n)
    q, rem = divmod(s, factorial(t))
    assert rem == 0, ('Theta not integral', t, n, m)
    return q


def Gamma_c(n, j, m, C):
    """内层形式 (b)：Gamma_m(n; j) = Theta_{m-j}(n + 3(m-j))（c_i 交错和）。对所有整数 n 成立（n<0 给 0）。"""
    t = m - j
    return Theta(t, n + 3 * t, m, C)


# ---------------------------------------------------------------- U_k(m) 的各种形式
def U_H(k, m, H):
    """H 型（草稿 §2，全正项双和）：
    U = sum_s h_s(0..m) C(k+m-2s, m+s) + sum_{j=1}^m j sum_s h_s(j..m) C(k-2+m-j-2s, m-j+s)。"""
    tot = Gamma_rs(k, 0, m, H)
    if k >= 2:
        for j in range(1, m + 1):
            tot += j * Gamma_rs(k - 2, j, m, H)
    return tot


def U_F3(k, m, H):
    """F3 型：U = [x^{k+1}] 1/P_m - sum_{j=1}^m [x^k] prod_{v=j}^m b_v^{-1}（r-Stirling 内层）。"""
    tot = Gamma_rs(k + 1, 0, m, H)
    for j in range(1, m + 1):
        tot -= Gamma_rs(k, j, m, H)
    return tot


def U_Theta(k, m, C):
    """Θ 型（提示词 (C4)）：U = Theta_m(k+1+3m) - sum_{t=0}^{m-1} Theta_t(k+3t)。"""
    tot = Theta(m, k + 1 + 3 * m, m, C)
    for t in range(m):
        tot -= Theta(t, k + 3 * t, m, C)
    return tot


def U_ThetaH(k, m, C):
    """H 外层 + c_i 内层：U = Gamma(k;0) + sum_j j Gamma(k-2;j)，Gamma 用 c_i 交错和。"""
    tot = Gamma_c(k, 0, m, C)
    for j in range(1, m + 1):
        tot += j * Gamma_c(k - 2, j, m, C)
    return tot


def U_F4(k, m, C):
    """c_i 偏分式型（新）：
    U = (1/m!) sum_{i=0}^m (-1)^{m-i} C(m,i) [ c_i(k+3m) + sum_{j=1}^{i} j * i^{(j)} * c_i(k+3m-3j-2) ]，
    i^{(j)} = i(i-1)...(i-j+1)（下降阶乘）。"""
    tot = 0
    for i in range(m + 1):
        inner = cval(C, i, k + 3 * m)
        ff = 1
        for j in range(1, i + 1):
            ff *= (i - j + 1)
            inner += j * ff * cval(C, i, k + 3 * m - 3 * j - 2)
        tot += (-1) ** (m - i) * comb(m, i) * inner
    q, rem = divmod(tot, factorial(m))
    assert rem == 0, ('F4 not integral', k, m)
    return q


def stirling2_row_formula(n, k):
    """S(n,k) = (1/k!) sum_i (-1)^{k-i} C(k,i) i^n（显式式，仅用于独立核对）。"""
    s = sum((-1) ** (k - i) * comb(k, i) * i ** n for i in range(k + 1))
    q, r = divmod(s, factorial(k))
    assert r == 0
    return q


def rstirling_explicit(n, k, r):
    """r-Stirling {n \\ k}_r 的显式式 (1/(k-r)!) sum_{i=0}^{k-r} (-1)^{k-r-i} C(k-r,i) (i+r)^{n-r}（n>=r, k>=r）。"""
    t = k - r
    s = sum((-1) ** (t - i) * comb(t, i) * (i + r) ** (n - r) for i in range(t + 1))
    q, rem = divmod(s, factorial(t))
    assert rem == 0
    return q


# ---------------------------------------------------------------- 递推类方法（对照用）
def U_rec_table(K, M):
    """引理 1：U_k(m) = U_k(m-1) + U_{k-1}(m) + m U_{k-3}(m)，边界 U_0=U_{-1}=1, U_{-2}=0, U_k(-1)=0 (k>=1)。"""
    T = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        T[0][m] = 1

    def get(k, m):
        if k == 0 or k == -1:
            return 1
        if k == -2:
            return 0
        return T[k][m]

    for k in range(1, K + 1):
        for m in range(M + 1):
            T[k][m] = (T[k][m - 1] if m >= 1 else 0) + get(k - 1, m) + m * get(k - 3, m)
    return T


def N_triangle(K):
    """(C3) 的三角递推：N(k,r+1) = N(k-1,r) + N(k-1,r+1) + r[N(k-3,r-1) + 2N(k-3,r) + N(k-3,r+1)]（k>=3）。"""
    N = [[0] * (K + 2) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1], N[2][2] = 1, 2

    def g(k, q):
        if k < 0 or q < 0 or q > K + 1:
            return 0
        return N[k][q]

    for k in range(3, K + 1):
        for r in range(0, k):
            N[k][r + 1] = g(k - 1, r) + g(k - 1, r + 1) + r * (g(k - 3, r - 1) + 2 * g(k - 3, r) + g(k - 3, r + 1))
    return N
