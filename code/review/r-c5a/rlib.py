# -*- coding: utf-8 -*-
"""r-c5a 复核者自己的底座：不导入 core.py / polylib.py，全部从第 1 节原始定义重写。

U_dp(m, K)      高度向量 DP（定义 (b)），自己写的实现：状态 = 最后两个高度
U_rec_table     引理 1 三项递推（已由复核者独立重证），只用于把范围扩大
matrix_brute    原题 n x k 0/1 矩阵逐个枚举（行禁 001/010，列禁 001/011）
height_brute    高度向量逐个枚举（定义 (b) 的字面实现）
"""
from fractions import Fraction
from itertools import product
from math import comb, factorial


def ok3(a, b, c):
    # 定义 (b)：b == c 或 a >= max(b, c)
    return b == c or (a >= b and a >= c)


def height_brute(k, m):
    if k == 0:
        return 1
    cnt = 0
    for h in product(range(m + 1), repeat=k):
        if all(ok3(h[i], h[i + 1], h[i + 2]) for i in range(k - 2)):
            cnt += 1
    return cnt


def matrix_brute(n, k):
    """原题定义：n x k 0/1 矩阵，行内任意连续三位不是 001/010，列内任意连续三位不是 001/011。"""
    tot = 0
    for cells in product((0, 1), repeat=n * k):
        rows = [cells[i * k:(i + 1) * k] for i in range(n)]
        good = True
        for r in rows:
            for i in range(k - 2):
                t = r[i:i + 3]
                if t == (0, 0, 1) or t == (0, 1, 0):
                    good = False
                    break
            if not good:
                break
        if not good:
            continue
        for j in range(k):
            col = [rows[i][j] for i in range(n)]
            for i in range(n - 2):
                t = (col[i], col[i + 1], col[i + 2])
                if t == (0, 0, 1) or t == (0, 1, 1):
                    good = False
                    break
            if not good:
                break
        if good:
            tot += 1
    return tot


def U_dp(m, K):
    """[U_0(m), ..., U_K(m)]：高度 DP。f[b][c] = 以 (b,c) 结尾的合法前缀数。
    转移 (a,b) -> (b,c) 合法 <=> b==c 或 a>=max(b,c)。对固定 b 做 a 的“前缀和（从大到小）”。"""
    out = [1]
    if K >= 1:
        out.append(m + 1)
    if K >= 2:
        out.append((m + 1) ** 2)
    if K <= 2:
        return out[:K + 1]
    n = m + 1
    f = [[1] * n for _ in range(n)]  # f[a][b]
    for _ in range(3, K + 1):
        g = [[0] * n for _ in range(n)]
        for b in range(n):
            col = [f[a][b] for a in range(n)]
            # top[t] = sum_{a >= t} col[a]
            top = [0] * (n + 1)
            s = 0
            for a in range(n - 1, -1, -1):
                s += col[a]
                top[a] = s
            total = top[0]
            for c in range(n):
                g[b][c] = total if c == b else top[b if b > c else c]
        f = g
        out.append(sum(sum(r) for r in f))
    return out


def U_rec_table(K, M):
    """引理 1：U_k(m)=U_k(m-1)+U_{k-1}(m)+m U_{k-3}(m)；U_{-1}=1, U_{-2}=0, U_k(-1)=0 (k>=1), U_0=1。
    返回 T[k][m]，0<=k<=K, 0<=m<=M。"""
    def Uv(T, k, m):
        if k == -1:
            return 1
        if k <= -2:
            return 0
        if m == -1:
            return 1 if k == 0 else 0
        return T[k][m]
    T = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        T[0][m] = 1
    for k in range(1, K + 1):
        for m in range(M + 1):
            T[k][m] = Uv(T, k, m - 1) + Uv(T, k - 1, m) + m * Uv(T, k - 3, m)
    return T


# ------------------------------------------------------------------ 多项式（Fraction，升幂）
def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def pmul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return trim(r)


def pscale(a, c):
    return trim([c * x for x in a])


def peval(p, x):
    r = 0
    for c in reversed(p):
        r = r * x + c
    return r


def pderiv(p):
    return trim([i * p[i] for i in range(1, len(p))])


def interp_newton(xs, ys):
    """Newton 插值，Fraction 系数。"""
    n = len(xs)
    coef = [Fraction(y) for y in ys]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (xs[i] - xs[i - j])
    poly = []
    for i in range(n - 1, -1, -1):
        poly = padd(pmul(poly, [Fraction(-xs[i]), Fraction(1)]), [coef[i]]) if poly else [coef[i]]
    return trim(poly)


def poly_from_values_0(vals):
    """给定 p(0..d) 的值（d+1 个），返回 p 的单项式系数（Fraction）。"""
    return interp_newton(list(range(len(vals))), vals)


def gbinom(x, q):
    if q < 0:
        return 0
    num = 1
    for i in range(q):
        num *= (x - i)
    return num // factorial(q)
