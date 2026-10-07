# -*- coding: utf-8 -*-
"""s10-b1：从定义出发计算 U_k(m) 与 N(k,q)（自写，不导入项目里别的脚本）。

  U_brute(k, m)  ：枚举 {0..m}^k，逐个检查连续三元组是否 good（论文 Definition 2.1）。
  U_dp(K, M)     ：按定义的转移计数（状态 = 最后两项），用后缀和加速：
                   new[b][c] = Σ_a cnt[a][b]·[good(a,b,c)]，good ⇔ b==c 或 a≥max(b,c)。
  N_brute(k)     ：DFS 枚举字母表 {1..k} 上长 k 的 good 词，按值域是否恰为 {1..q} 计数。
  N_from_U       ：论文 Proposition 2.6 的容斥式 N(k,q)=Σ_i (−1)^(q−i) C(q,i) U_k(i−1)。
  N_tri(K)       ：论文 Proposition 2.7 的三角递推（只用于 k>60 的延伸，k≤60 与 N_from_U 对照）。
"""
from itertools import product
from math import comb


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def U_brute(k, m):
    cnt = 0
    for h in product(range(m + 1), repeat=k):
        if all(good(h[j], h[j + 1], h[j + 2]) for j in range(k - 2)):
            cnt += 1
    return cnt


def U_dp(K, M):
    """返回 U[k][m]，0≤k≤K，0≤m≤M。"""
    U = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        n = m + 1
        U[0][m] = 1
        if K >= 1:
            U[1][m] = n
        if K >= 2:
            U[2][m] = n * n
            cnt = [[1] * n for _ in range(n)]          # cnt[a][b]
            for k in range(3, K + 1):
                new = [[0] * n for _ in range(n)]
                for b in range(n):
                    col = [cnt[a][b] for a in range(n)]
                    suf = [0] * (n + 1)
                    for a in range(n - 1, -1, -1):
                        suf[a] = suf[a + 1] + col[a]
                    tot = suf[0]
                    row = new[b]
                    for c in range(n):
                        row[c] = tot if c == b else suf[max(b, c)]
                cnt = new
                U[k][m] = sum(sum(r) for r in cnt)
    return U


def N_brute(k):
    """dict q -> N(k,q)，字母表 {1..k}。"""
    res = {}
    if k == 0:
        return {0: 1}
    w = []

    def dfs():
        if len(w) == k:
            s = set(w)
            q = len(s)
            if s == set(range(1, q + 1)):
                res[q] = res.get(q, 0) + 1
            return
        for v in range(1, k + 1):
            if len(w) >= 2 and not good(w[-2], w[-1], v):
                continue
            w.append(v)
            dfs()
            w.pop()

    dfs()
    return res


def N_from_U(U, k, q):
    s = 0
    for i in range(q + 1):
        if i == 0:
            u = 1 if k == 0 else 0
        else:
            u = U[k][i - 1]
        s += (-1) ** (q - i) * comb(q, i) * u
    return s


def N_table_from_U(U, K):
    """N[k][q]，0≤q≤k≤K（需要 U 的列 m ≤ K−1）。"""
    return [[N_from_U(U, k, q) for q in range(k + 1)] for k in range(K + 1)]


def N_tri(K):
    """三角递推（论文 Prop. 2.7）：k≥3、q≥1，越界取 0；初值 N(0,0)=1, N(1,1)=1, N(2,1)=1, N(2,2)=2。"""
    N = [[0] * (k + 1) for k in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1] = 1
        N[2][2] = 2

    def g(k, q):
        if k < 0 or q < 0 or q > k:
            return 0
        return N[k][q]

    for k in range(3, K + 1):
        for q in range(1, k + 1):
            N[k][q] = g(k - 1, q - 1) + g(k - 1, q) + (q - 1) * (g(k - 3, q - 2) + 2 * g(k - 3, q - 1) + g(k - 3, q))
    return N


def nrow(N, k):
    """n_k(z) = Σ_{q=1}^k N(k,q) z^(q−1)（k≥1），低次在前。"""
    assert k >= 1
    p = [N[k][q] for q in range(1, k + 1)]
    while p and p[-1] == 0:
        p.pop()
    return p
