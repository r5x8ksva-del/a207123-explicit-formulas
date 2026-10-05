# -*- coding: utf-8 -*-
"""任务 C 的公共底座：只依赖第 1 节的原始定义，纯整数运算。

三种互相独立的 U_k(m) / a_k(n) 计算方式：
  a_direct(n, k)    —— 直接按原题（行禁 001/010、列禁 001/011）逐行转移计数，列规则逐个三元组字面检查
  a_brute(n, k)     —— 2^(nk) 暴力枚举（仅小规模）
  U_multichain(k,m) —— 允许行偏序集里长度 m 的多重链 r_1 >= ... >= r_m（逐分量序）
  U_height_table    —— 高度向量 DP（第 1 节 (b)），一次算出 k<=K, m<=M 的整张表
"""
from collections import defaultdict
from itertools import product
from functools import lru_cache


def row_ok(bits):
    """行规则：任意连续三个位置都不是 001 也不是 010（从左到右）。"""
    for i in range(len(bits) - 2):
        t = (bits[i], bits[i + 1], bits[i + 2])
        if t == (0, 0, 1) or t == (0, 1, 0):
            return False
    return True


def col_ok(bits):
    """列规则：任意连续三个位置都不是 001 也不是 011（从上到下）。"""
    for i in range(len(bits) - 2):
        t = (bits[i], bits[i + 1], bits[i + 2])
        if t == (0, 0, 1) or t == (0, 1, 1):
            return False
    return True


@lru_cache(maxsize=None)
def allowed_rows(k):
    return tuple(r for r in product((0, 1), repeat=k) if row_ok(r))


def a_brute(n, k):
    """直接枚举所有 n×k 0/1 矩阵（n*k 不宜超过 ~22）。"""
    cnt = 0
    for cells in product((0, 1), repeat=n * k):
        rows = [cells[i * k:(i + 1) * k] for i in range(n)]
        if not all(row_ok(r) for r in rows):
            continue
        if all(col_ok(tuple(rows[i][j] for i in range(n))) for j in range(k)):
            cnt += 1
    return cnt


def a_direct(n, k):
    """按原题定义的行转移计数：状态 = 最后两行；列规则逐列字面检查三元组。"""
    rows = allowed_rows(k)
    if n == 0:
        return 1
    if n == 1:
        return len(rows)
    R = len(rows)
    bad = [[0, 0, 1], [0, 1, 1]]
    # ok3[a][b][c] 是否三行 (a,b,c) 在每列都合法
    def triple_ok(x, y, z):
        for j in range(k):
            if [x[j], y[j], z[j]] in bad:
                return False
        return True
    nxt = {}
    for ia in range(R):
        for ib in range(R):
            nxt[(ia, ib)] = [ic for ic in range(R) if triple_ok(rows[ia], rows[ib], rows[ic])]
    cur = {(ia, ib): 1 for ia in range(R) for ib in range(R)}
    for _ in range(n - 2):
        new = defaultdict(int)
        for (ia, ib), v in cur.items():
            for ic in nxt[(ia, ib)]:
                new[(ib, ic)] += v
        cur = new
    return sum(cur.values())


def U_multichain(k, m):
    """允许行（长度 k）在逐分量序下长度 m 的多重链 r_1 >= r_2 >= ... >= r_m 的个数。"""
    if m == 0:
        return 1
    rows = allowed_rows(k)
    geq = [[all(x >= y for x, y in zip(r, s)) for s in rows] for r in rows]
    f = [1] * len(rows)
    for _ in range(m - 1):
        f = [sum(f[i] for i in range(len(rows)) if geq[i][j]) for j in range(len(rows))]
    return sum(f)


def good(a, b, c):
    """第 1 节 (b) 的三元组条件：b == c 或 a >= max(b, c)。"""
    return b == c or (a >= b and a >= c)


def U_list(m, K):
    """第 1 节给出的参考实现（逐字照抄，K>=2）：返回 [U_0(m), ..., U_K(m)]。"""
    out = [1, m + 1]
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    out.append(sum(cnt.values()))
    for k in range(3, K + 1):
        new = defaultdict(int)
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] += v
        cnt = new
        out.append(sum(cnt.values()))
    return out


def U_height_table(K, M):
    """T[k][m] = U_k(m)，0<=k<=K，0<=m<=M（高度 DP，按 m 逐个调用参考实现）。"""
    cols = [U_list(m, max(K, 2)) for m in range(M + 1)]
    return [[cols[m][k] for m in range(M + 1)] for k in range(K + 1)]


# 第 2 节给的校验数据：U_k(m)，k=1..10，m=0..6
PROMPT_TABLE = {
    1: [1, 2, 3, 4, 5, 6, 7],
    2: [1, 4, 9, 16, 25, 36, 49],
    3: [1, 6, 17, 36, 65, 106, 161],
    4: [1, 9, 32, 80, 165, 301, 504],
    5: [1, 14, 64, 192, 457, 938, 1736],
    6: [1, 21, 119, 419, 1136, 2604, 5306],
    7: [1, 31, 214, 873, 2669, 6778, 15108],
    8: [1, 46, 388, 1837, 6334, 17802, 43326],
    9: [1, 68, 694, 3788, 14666, 45488, 120650],
    10: [1, 100, 1222, 7629, 32971, 112349, 323647],
}
PROMPT_A3 = [6, 36, 102, 289, 612, 1296]  # a_3(n), n=1..6


# ---------------------------------------------------------------------------
# 快速高度 DP（后缀和，O(m^2) 每步）。仍是第 1 节 (b) 定义的直接实现：
#   new[b][c] = sum_a cnt[a][b] * [good(a,b,c)]
#   good(a,b,c) <=> b==c 或 a>=max(b,c)
# 所以 b==c 时对 a 全求和，b!=c 时对 a>=max(b,c) 求后缀和。
# ---------------------------------------------------------------------------
def U_fast_column(m, K):
    """[U_0(m), ..., U_K(m)]，m>=0，K>=0。"""
    out = [1]
    if K == 0:
        return out
    out.append(m + 1)
    if K == 1:
        return out
    n = m + 1
    cnt = [[1] * n for _ in range(n)]          # cnt[a][b]：最后两项为 (a,b) 的合法前缀数
    out.append(n * n)
    for _k in range(3, K + 1):
        # suf[b][t] = sum_{a>=t} cnt[a][b]
        new = [[0] * n for _ in range(n)]
        for b in range(n):
            suf = [0] * (n + 1)
            for a in range(n - 1, -1, -1):
                suf[a] = suf[a + 1] + cnt[a][b]
            tot = suf[0]
            row = new[b]
            for c in range(n):
                row[c] = tot if c == b else suf[max(b, c)]
        cnt = new
        out.append(sum(map(sum, cnt)))
    return out


def U_fast_table(K, M):
    """T[k][m] = U_k(m)，0<=k<=K，0<=m<=M。"""
    cols = [U_fast_column(m, K) for m in range(M + 1)]
    return [[cols[m][k] for m in range(M + 1)] for k in range(K + 1)]


def binom(n, k):
    """整数二项式；k<0 或 k>n>=0 时为 0；n<0 时按 0 处理（本项目里只在 n>=0 时使用）。"""
    if k < 0 or n < 0 or k > n:
        return 0
    from math import comb
    return comb(n, k)


def N_from_U(T, k, q):
    """N(k,q) = sum_i (-1)^(q-i) C(q,i) U_k(i-1)（容斥，U_k(-1)=0 当 k>=1；U_0(-1)=1）。
    T 为 U 表（T[k][m]，m>=0），需要 q-1 <= M。"""
    s = 0
    for i in range(q + 1):
        if i == 0:
            u = 1 if k == 0 else 0
        else:
            u = T[k][i - 1]
        s += (-1) ** (q - i) * binom(q, i) * u
    return s


def N_brute(k):
    """按定义：长度 k、值域恰为 {0..q-1} 的合法词个数（DFS 枚举合法序列），返回 dict q->N(k,q)。"""
    res = defaultdict(int)
    if k == 0:
        res[0] = 1
        return dict(res)
    vals = range(k)
    seq = []

    def dfs():
        if len(seq) == k:
            s = set(seq)
            q = len(s)
            if s == set(range(q)):
                res[q] += 1
            return
        for v in vals:
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            dfs()
            seq.pop()

    dfs()
    return dict(res)


def stirling2_table(nmax):
    """S[n][k]，0<=k<=n<=nmax。"""
    S = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    S[0][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
    return S


def h_complete(s, lo, hi):
    """完全齐次对称多项式 h_s(lo, lo+1, ..., hi)；区间为空时 h_0=1, h_s=0 (s>0)；s<0 时为 0。"""
    if s < 0:              # 2026-10-04 第二轮复核后补上：原实现对负 s 会返回 1（所有现有调用点都已自行判断 s<0）
        return 0
    # DP over variables
    row = [1] + [0] * s
    for v in range(lo, hi + 1):
        for t in range(1, s + 1):
            row[t] += v * row[t - 1]
    return row[s]
