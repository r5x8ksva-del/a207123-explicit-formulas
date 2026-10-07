# -*- coding: utf-8 -*-
"""表 B 的 B8（U_k 没有其他负整数零点）探索脚本。

U_k(-j) := u_k(-j)，u_k 为 T1.2 的插值多项式。用 T5.3(2) 的
G_{-j-1} = (1 - x + j x^3) G_{-j} + j x^2，G_{-1} = 1 计算，
并对 k <= 12 用 DP 数据插值独立核对。
输出：符号表（k 行、j 列），以及 u_k 的复根分布（numpy，只作观察）。
"""
import sys
from fractions import Fraction
sys.path.insert(0, __file__.rsplit('code', 1)[0] + 'code')
from core import U_fast_table  # noqa: E402


def Gneg_table(J):
    """返回 dict j -> 系数列表 [U_0(-j), ..., U_{3j-3}(-j)]，1<=j<=J。"""
    G = {1: [1]}
    for j in range(1, J):
        g = G[j]
        n = len(g) + 3
        c = [0] * n
        for k in range(n):
            v = 0
            if k < len(g):
                v += g[k]
            if 0 <= k - 1 < len(g):
                v -= g[k - 1]
            if 0 <= k - 3 < len(g):
                v += j * g[k - 3]
            if k == 2:
                v += j
            c[k] = v
        while len(c) > 1 and c[-1] == 0:
            c.pop()
        G[j + 1] = c
    return G


def interp_check(K=12, M=30):
    T = U_fast_table(K, M)
    G = Gneg_table(20)
    bad = 0
    for k in range(0, K + 1):
        xs = list(range(0, k + 2))
        ys = [T[k][m] for m in xs]
        # Lagrange 外推到负整数
        for j in range(1, 20):
            y = -j
            s = Fraction(0)
            for i, xi in enumerate(xs):
                num = Fraction(1)
                for l, xl in enumerate(xs):
                    if l != i:
                        num *= Fraction(y - xl, xi - xl)
                s += ys[i] * num
            g = G[j]
            val = g[k] if k < len(g) else 0
            if s != val:
                bad += 1
    return bad


if __name__ == '__main__':
    print('interp mismatches (k<=12, j<20):', interp_check())
    J = 40
    G = Gneg_table(J)
    # 零系数检查：0<=k<=3j-3 范围内有没有 0
    zeros = [(j, k) for j in range(1, J + 1) for k, v in enumerate(G[j]) if v == 0]
    print('zero coefficients with k<=3j-3:', zeros[:20])
    # 符号表：行 k，列 j
    K = 30
    for k in range(0, K + 1):
        row = []
        for j in range(1, J + 1):
            g = G[j]
            v = g[k] if k < len(g) else 0
            row.append('+' if v > 0 else ('-' if v < 0 else '0'))
        print('k=%2d (k%%3=%d) ' % (k, k % 3) + ''.join(row))
