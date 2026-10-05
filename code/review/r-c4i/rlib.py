# -*- coding: utf-8 -*-
"""r-c4i 复核者的独立工具库（不导入 core.py / polylib.py，全部自写）。

只依赖第 1 节的原始定义：
  - 三元组条件 legal(a,b,c) <=> b==c 或 a>=max(b,c)   （第 1 节 (b)）
  - U_k(m)：高度向量 (h_1..h_k) in {0..m}^k 且每个相邻三元组合法 的个数
  - N(k,q)：长度 k、值域恰为 {1..q} 的合法词个数（由序不变性，= 容斥 sum_i (-1)^{q-i} C(q,i) U_k(i-1)）
另外给出：按定义 DFS 枚举满射合法词；原题 0/1 矩阵的小规模暴力（锚定归约 (b)）。
多项式：Fraction 系数列表（升幂）。
"""
from fractions import Fraction
from math import comb, factorial
from itertools import product


def legal(a, b, c):
    return b == c or (a >= b and a >= c)


def word_ok(w):
    return all(legal(w[i], w[i + 1], w[i + 2]) for i in range(len(w) - 2))


# ---------------------------------------------------------------------------
# U_k(m)：高度 DP。写法与 core 不同：状态 f[b][c] = 以 (b,c) 结尾的合法前缀数；
# 转移 g[c][e] = sum_{b} f[b][c]*[legal(b,c,e)]。
#   legal(b,c,e): c==e 时对一切 b 成立；c!=e 时需 b>=max(c,e)。
# 用列前缀累计（从大到小）实现：colsuf[c][t] = sum_{b>=t} f[b][c]。
# ---------------------------------------------------------------------------
def U_column(m, K):
    """返回 [U_0(m),...,U_K(m)]。"""
    n = m + 1
    out = [1]
    if K >= 1:
        out.append(n)
    if K >= 2:
        out.append(n * n)
    if K <= 2:
        return out[:K + 1]
    f = [[1] * n for _ in range(n)]  # f[b][c]
    for _ in range(3, K + 1):
        g = [[0] * n for _ in range(n)]
        for c in range(n):
            # colsuf over b of f[b][c]
            suf = [0] * (n + 1)
            acc = 0
            for b in range(n - 1, -1, -1):
                acc += f[b][c]
                suf[b] = acc
            total = suf[0]
            gc = g[c]
            for e in range(n):
                if e == c:
                    gc[e] = total
                else:
                    gc[e] = suf[c if c > e else e]
        f = g
        out.append(sum(sum(r) for r in f))
    return out


def U_slow(k, m):
    """直接枚举 {0..m}^k 并逐个检查三元组（仅小规模）。"""
    return sum(1 for h in product(range(m + 1), repeat=k) if word_ok(h))


def U_table(K, M):
    cols = [U_column(m, K) for m in range(M + 1)]
    return [[cols[m][k] for m in range(M + 1)] for k in range(K + 1)]


def N_table_from_U(T, K):
    """N[k][q]，0<=q<=k<=K。U_k(-1) := [k==0]。"""
    N = [[0] * (K + 2) for _ in range(K + 1)]
    for k in range(K + 1):
        for q in range(0, k + 1):
            s = 0
            for i in range(0, q + 1):
                u = (1 if k == 0 else 0) if i == 0 else T[k][i - 1]
                s += (-1) ** (q - i) * comb(q, i) * u
            N[k][q] = s
    return N


def N_brute_surj(k, q):
    """按定义 DFS：长度 k、值域恰为 {1..q} 的合法词个数（满射剪枝）。"""
    if k == 0:
        return 1 if q == 0 else 0
    if q == 0 or q > k:
        return 0
    cnt = [0]
    used = [0] * (q + 1)
    seq = []

    def dfs(missing):
        L = len(seq)
        if missing > k - L:
            return
        if L == k:
            cnt[0] += 1
            return
        for v in range(1, q + 1):
            if L >= 2 and not legal(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            used[v] += 1
            dfs(missing - (1 if used[v] == 1 else 0))
            used[v] -= 1
            seq.pop()

    dfs(q)
    return cnt[0]


# ---------------------------------------------------------------------------
# 原题矩阵层面的锚定：m x k 0/1 矩阵，列从上到下单调不增 + 行不含 001/010
# ---------------------------------------------------------------------------
def row_rule(r):
    for i in range(len(r) - 2):
        t = (r[i], r[i + 1], r[i + 2])
        if t == (0, 0, 1) or t == (0, 1, 0):
            return False
    return True


def U_matrix_brute(k, m):
    """枚举 m x k 0/1 矩阵，列单调不增（上到下），每行满足行规则。"""
    rows = [r for r in product((0, 1), repeat=k) if row_rule(r)]
    # 多重链 r_1 >= r_2 >= ... >= r_m（逐分量）
    if m == 0:
        return 1
    cnt = 0
    for chain in product(range(len(rows)), repeat=m):
        ok = True
        for t in range(m - 1):
            a, b = rows[chain[t]], rows[chain[t + 1]]
            if any(x < y for x, y in zip(a, b)):
                ok = False
                break
        if ok:
            cnt += 1
    return cnt


# ---------------------------------------------------------------------------
# Fraction 多项式（升幂）
# ---------------------------------------------------------------------------
def ptrim(p):
    p = [Fraction(c) for c in p]
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return ptrim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def psub(p, q):
    n = max(len(p), len(q))
    return ptrim([(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(n)])


def pmul(p, q):
    if not p or not q:
        return []
    r = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return ptrim(r)


def pscale(p, c):
    return ptrim([c * a for a in p])


def peval(p, x):
    r = Fraction(0)
    for a in reversed(p):
        r = r * x + a
    return r


def pshift(p, s):
    """返回 q(k) = p(k+s) 的系数。"""
    res = []
    for a in reversed(p):
        res = padd(pmul(res, [Fraction(s), Fraction(1)]), [a])
    return res


def interp(xs, ys):
    """Newton 均差插值（Fraction），返回升幂系数。"""
    n = len(xs)
    dd = [Fraction(y) for y in ys]
    coef = [dd[0]]
    for j in range(1, n):
        dd = [(dd[i + 1] - dd[i]) / (xs[i + j] - xs[i]) for i in range(len(dd) - 1)]
        coef.append(dd[0])
    poly = []
    for i in range(n - 1, -1, -1):
        poly = padd(pmul(poly, [Fraction(-xs[i]), Fraction(1)]), [coef[i]])
    return poly


def newton_coeffs(p, base, deg):
    vals = [peval(p, base + i) for i in range(deg + 1)]
    out = []
    for _ in range(deg + 1):
        out.append(vals[0])
        vals = [vals[j + 1] - vals[j] for j in range(len(vals) - 1)]
    return out


def dfact(n):
    """(n)!! for odd n>=-1."""
    r = 1
    while n > 1:
        r *= n
        n -= 2
    return r
