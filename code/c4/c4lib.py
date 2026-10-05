# -*- coding: utf-8 -*-
"""C-4 探索用小工具（只读调用 core / polylib，不修改它们）。"""
import sys, os
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(HERE)
sys.path.insert(0, CODE)
from core import U_fast_table, N_from_U, N_brute, binom, stirling2_table  # noqa: E402
from polylib import trim, padd, psub, pscale, pmul, pshift, peval, pdiv, pgcd, \
    series_inv, series_mul, interpolate, P_poly, b_poly  # noqa: E402


# ---------------- N 三角 ----------------
def N_table_rec(K):
    """按三角递推（k>=3）+ k<=2 的初值计算 N[k][q]，0<=q<=k+3（多留几列便于越界取 0）。"""
    N = [[0] * (K + 5) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1] = 1
        N[2][2] = 2

    def g(k, q):
        if k < 0 or q < 0 or q > k + 3:
            return 0
        return N[k][q]
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            r = q - 1
            N[k][q] = g(k - 1, q - 1) + g(k - 1, q) + r * (g(k - 3, q - 2) + 2 * g(k - 3, q - 1) + g(k - 3, q))
    return N


def N_table_dp(K):
    """用 core 的高度 DP 表 + 容斥得到 N[k][q]（0<=q<=k），独立于三角递推。"""
    T = U_fast_table(K, max(K - 1, 0))
    N = [[0] * (K + 5) for _ in range(K + 1)]
    for k in range(K + 1):
        for q in range(0, k + 1):
            N[k][q] = N_from_U(T, k, q)
    return N, T


def Dval(N, k, d):
    """D(k,d) = N(k,k-d)；越界取 0。"""
    q = k - d
    if k < 0 or q < 0 or q > k:
        return 0
    return N[k][q]


# ---------------- k 的多项式（Fraction 系数，升幂） ----------------
def pcompose_shift(p, s):
    """返回 p(k+s) 的系数（s 为整数或 Fraction）。"""
    res = []
    # Horner: p(k+s) = (...((a_n)(k+s) + a_{n-1})(k+s) + ...)
    for a in reversed(p):
        res = padd(pmul(res, [Fraction(s), Fraction(1)]), [Fraction(a)])
    return trim(res)


def binom_poly(c, n):
    """C(k+c, n) 作为 k 的多项式（Fraction 系数）。"""
    p = [Fraction(1)]
    for i in range(n):
        p = pmul(p, [Fraction(c - i), Fraction(1)])
    f = 1
    for i in range(1, n + 1):
        f *= i
    return pscale(p, Fraction(1, f))


def pval(p, k):
    return peval([Fraction(a) for a in p], Fraction(k))
