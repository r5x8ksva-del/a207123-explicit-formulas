# -*- coding: utf-8 -*-
"""B4 探索：Stirling 类比型单和
    U_k(m) = sum_{i=0}^m sum_{r=0}^2 gamma_r(m,i) c_i(k+3m-r)
的系数唯一，等于 (-1)^{m-i}/(i!(m-i)!) * A_i^{(r)}，其中 (A_i^{(0)},A_i^{(1)},A_i^{(2)}) 是
W~_i = 1 + sum_{j=1}^i j*i^{(j)} x^{3j+2}  在 Q[x]/(b_i) 里化成 A0 + A1 x + A2 x^2 的坐标（b_i = 1-x-i x^3）。
（推导：c_i(n-r) 对应 x^r/b_i；W_m ≡ W~_i (mod b_i)；在 b_i 的根处 prod_{v!=i} b_v = (-1)^{m-i} i!(m-i)! x^{3m}。）
这里先数值核对这个公式，再看 A_i^{(r)} 的 p 进赋值（p 为素数、i=p）。
"""
import os, sys
from fractions import Fraction
from math import factorial, comb
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from core import U_fast_table


def polymod_bi(coeffs, i):
    """把多项式（系数表，低次在前，Fraction）模 b_i = 1 - x - i x^3 化为次数 <= 2。x^3 = (1-x)/i。"""
    c = [Fraction(v) for v in coeffs]
    for d in range(len(c) - 1, 2, -1):
        if c[d] == 0:
            continue
        t = c[d] / i
        c[d] = Fraction(0)
        # x^d = x^{d-3} * (1 - x)/i
        c[d - 3] += t
        c[d - 2] -= t
    c = (c + [Fraction(0)] * 3)[:3]
    return c


def Wtilde(i):
    deg = 3 * i + 2
    c = [0] * (deg + 1)
    c[0] = 1
    for j in range(1, i + 1):
        ff = 1
        for l in range(j):
            ff *= (i - l)
        c[3 * j + 2] += j * ff
    return c


def coords(i):
    if i == 0:
        return [Fraction(1), Fraction(0), Fraction(0)]   # b_0 = 1-x：W~_0 = 1，常数
    return polymod_bi(Wtilde(i), i)


def c_seq(i, N):
    c = [0] * (N + 1)
    for n in range(N + 1):
        c[n] = (c[n - 1] if n >= 1 else (1 if n == 0 else 0)) + (i * c[n - 3] if n >= 3 else 0)
        if n == 0:
            c[0] = 1
    return c


def vp(x, p):
    x = Fraction(x)
    if x == 0:
        return None
    v = 0
    n, d = x.numerator, x.denominator
    while n % p == 0:
        n //= p; v += 1
    while d % p == 0:
        d //= p; v -= 1
    return v


if __name__ == '__main__':
    # 1) 核对公式 U_k(m) = sum_i (-1)^{m-i}/(i!(m-i)!) * sum_r A_i^{(r)} c_i(k+3m-r)
    K, M = 30, 9
    T = U_fast_table(K, M)
    CS = {i: c_seq(i, K + 3 * M + 5) for i in range(M + 1)}
    def cval(i, n):
        if i == 0:
            return 1 if n >= 0 else 0
        return CS[i][n] if n >= 0 else 0
    bad = 0
    for m in range(M + 1):
        for k in range(0, K + 1):
            tot = Fraction(0)
            for i in range(m + 1):
                A = coords(i)
                coef = Fraction((-1) ** (m - i), factorial(i) * factorial(m - i))
                tot += coef * sum(A[r] * cval(i, k + 3 * m - r) for r in range(3))
            if tot != T[k][m]:
                bad += 1
                if bad < 5:
                    print('mismatch', m, k, tot, T[k][m])
    print('formula check bad =', bad)
    # 2) 坐标与 p 进赋值
    for i in range(1, 13):
        A = coords(i)
        print(i, [str(a) for a in A])
    primes = [p for p in range(2, 80) if all(p % q for q in range(2, p))]
    for p in primes:
        A = coords(p)
        print('p=%d' % p, 'v_p(A0,A1,A2)=', [vp(a, p) for a in A])
