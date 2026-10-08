# -*- coding: utf-8 -*-
"""B5 探索：N_q（固定 q）的 u 型单族表示 N(k,q) = sum_s A(s) C(k+c-2s, s+d) 是否存在。
纤维 u=1（b_1 的三个根 ξ）上的判据：若存在，则 θ = W~_1(ξ) * Ψ_q(ξ) * ξ^{-g} ∈ Q（g 为某个整数），其中
    Res_ξ F_q * u'(ξ) = (-1)^{q-1}/1 * W~_1(ξ) * Σ_{M=1}^{q-1} C(q,M+1) ξ^{-3(M+1)}/(M-1)!   （i=1 的情形，i^2 i! = 1）
W~_1(ξ)=ξ(1+ξ)，N(ξ)=1，N(1+ξ)=3。取范数：3*N(Ψ_q) 必须是有理数的立方。
同样处理 N^c_q（W~ 换成 1）与 N^E_q（W~ 换成 W~-1 = x^5，此时纤维 1 没有阻碍，要用纤维 2）。
这里只算 N(Ψ_q) 的素因子分解，看 3*N(Ψ_q) 是否可能是立方。
"""
from fractions import Fraction
from math import comb, factorial


def mul(a, b):
    # Q(ξ)，ξ^3 = 1 - ξ；元素为 (a0,a1,a2)
    c = [Fraction(0)] * 5
    for i in range(3):
        for j in range(3):
            c[i + j] += a[i] * b[j]
    # ξ^4 = ξ - ξ^2, ξ^3 = 1 - ξ
    c[2] += -c[4]; c[1] += c[4]; c[4] = 0
    c[0] += c[3]; c[1] += -c[3]; c[3] = 0
    return [c[0], c[1], c[2]]


def inv_xi():
    # ξ^{-1}: ξ(ξ^2+1) = 1 => ξ^{-1} = ξ^2 + 1
    return [Fraction(1), Fraction(0), Fraction(1)]


def power(a, n):
    r = [Fraction(1), Fraction(0), Fraction(0)]
    base = a
    if n < 0:
        raise ValueError
    while n:
        if n & 1:
            r = mul(r, base)
        base = mul(base, base)
        n >>= 1
    return r


def norm(a):
    # 乘法矩阵的行列式
    cols = [a, mul(a, [0, 1, 0]), mul(a, [0, 0, 1])]
    M = [[cols[j][i] for j in range(3)] for i in range(3)]
    det = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
           - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
           + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    return det


def factor(n):
    n = abs(n)
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def icbrt(n):
    """非负整数的整数立方根（向下取整）。"""
    if n < 0:
        raise ValueError
    lo, hi = 0, 1
    while hi ** 3 <= n:
        hi *= 2
    while lo < hi - 1:
        mid = (lo + hi) // 2
        if mid ** 3 <= n:
            lo = mid
        else:
            hi = mid
    return lo


def cube_obstruction(r):
    """有理数 r（既约）是有理数的立方 <=> 分子、分母都是整数立方。返回 None 表示是立方，否则返回说明。"""
    r = Fraction(r)
    a, b = abs(r.numerator), r.denominator
    ca, cb = icbrt(a), icbrt(b)
    if ca ** 3 == a and cb ** 3 == b:
        return None
    return 'numerator cube=%s, denominator cube=%s' % (ca ** 3 == a, cb ** 3 == b)


if __name__ == '__main__':
    xi_inv3 = power(inv_xi(), 3)
    bad = []
    for q in range(2, 61):
        psi = [Fraction(0)] * 3
        for M in range(1, q):
            term = power(xi_inv3, M + 1)
            coef = Fraction(comb(q, M + 1), factorial(M - 1))
            psi = [psi[t] + coef * term[t] for t in range(3)]
        Npsi = norm(psi)
        cert = cube_obstruction(3 * Npsi)
        if cert is None:
            bad.append(q)
        if q <= 12 or cert is None:
            print('q=%d  N(Psi)=%s  3N obstruction prime %s' % (q, Npsi, cert))
    print('q in [2,60] without fiber-1 norm obstruction:', bad)
