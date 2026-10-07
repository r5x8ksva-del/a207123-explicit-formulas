# -*- coding: utf-8 -*-
"""表 B 的 B2 探索：两族 u 型和的纤维条件（与 m 无关的形式）。

纤维 u=1/i 上（b_i 的三个根 eta），G_m 的留数元 Res_eta G_m * u'(eta) 等于
  (-1)^{m-i+1} * What_i(eta) * eta^{-3m-4} / (i! (m-i)! i^2),
What_i(x) := 1 - x * sum_{j<i} P_j(x)。两族表示 x^{g1}A1(u)+x^{g2}A2(u)+Laurent 多项式 要求：
  在 K_i=Q(eta) 中，1, eta^b, What_i(eta) eta^n 在 Q 上线性相关（b=g2-g1, n=-3m-4-g1）。
条件与 m 无关。这里在 |n|,|b|<=R 内列出 i=1、i=2 各自的解。
"""
import sys
from fractions import Fraction


def make_field(minpoly):
    """minpoly = [c0, c1, c2] 表示 x^3 = c0 + c1 x + c2 x^2（有理系数）。返回乘法函数。"""
    c0, c1, c2 = [Fraction(c) for c in minpoly]

    def mul(a, b):
        # a, b: 长度 3 的系数列表（基 1, x, x^2）
        prod = [Fraction(0)] * 5
        for i in range(3):
            if a[i] == 0:
                continue
            for j in range(3):
                prod[i + j] += a[i] * b[j]
        # 约化 x^4 = x*x^3, x^3 = c0 + c1 x + c2 x^2
        for d in (4, 3):
            v = prod[d]
            if v:
                prod[d] = Fraction(0)
                prod[d - 3] += v * c0
                prod[d - 2] += v * c1
                prod[d - 1] += v * c2
        return prod[:3]
    return mul


def inverse(mul, a):
    """解 a * y = 1（3x3 线性方程组，Fraction 高斯消元）。"""
    cols = [mul(a, e) for e in ([1, 0, 0], [0, 1, 0], [0, 0, 1])]
    M = [[cols[j][i] for j in range(3)] + [Fraction(1 if i == 0 else 0)] for i in range(3)]
    for c in range(3):
        p = next(r for r in range(c, 3) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]
        M[c] = [v / pv for v in M[c]]
        for r in range(3):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [M[r][t] - f * M[c][t] for t in range(4)]
    return [M[i][3] for i in range(3)]


def powers(mul, x, R):
    """返回 dict e -> x^e，-R<=e<=R。"""
    one = [Fraction(1), Fraction(0), Fraction(0)]
    xi = inverse(mul, x)
    P = {0: one}
    cur = one
    for e in range(1, R + 1):
        cur = mul(cur, x)
        P[e] = cur
    cur = one
    for e in range(1, R + 1):
        cur = mul(cur, xi)
        P[-e] = cur
    return P


def dependent(v, w):
    """1, v, w 在 Q 上线性相关 ⇔ v、w 在基 1,x,x^2 下的后两个坐标构成的 2x2 行列式为 0。"""
    return v[1] * w[2] - v[2] * w[1] == 0


def solutions(minpoly, What, R):
    mul = make_field(minpoly)
    x = [Fraction(0), Fraction(1), Fraction(0)]
    P = powers(mul, x, 2 * R + 10)
    sols = []
    for n in range(-R, R + 1):
        w = mul(What, P[n])
        for b in range(-R, R + 1):
            if b == 0:
                continue
            if dependent(P[b], w):
                sols.append((n, b))
    return sols


def main():
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    # 纤维 1：b_1 = 1 - x - x^3，x^3 = 1 - x。What_1 = 1 - x*P_0 = 1 - x(1-x) = 1 - x + x^2。
    f1 = [1, -1, 0]
    W1 = [Fraction(1), Fraction(-1), Fraction(1)]
    s1 = solutions(f1, W1, R)
    print('fiber 1 solutions (n,b), |n|,|b|<=%d:' % R, s1)
    # 纤维 2：b_2 = 1 - x - 2x^3，x^3 = (1 - x)/2。What_2 = 1 - x(P_0 + P_1)，P_0 = 1-x，P_1 = (1-x)(1-x-x^3)。
    f2 = [Fraction(1, 2), Fraction(-1, 2), 0]
    mul2 = make_field(f2)
    x = [Fraction(0), Fraction(1), Fraction(0)]
    one = [Fraction(1), Fraction(0), Fraction(0)]
    P0 = [Fraction(1), Fraction(-1), Fraction(0)]
    x3 = mul2(mul2(x, x), x)
    b1 = [one[i] - x[i] - x3[i] for i in range(3)]
    P1 = mul2(P0, b1)
    S = [P0[i] + P1[i] for i in range(3)]
    xS = mul2(x, S)
    W2 = [one[i] - xS[i] for i in range(3)]
    print('What_2 in basis (1,eta,eta^2):', W2)
    s2 = solutions(f2, W2, R)
    print('fiber 2 solutions (n,b), |n|,|b|<=%d:' % R, s2)
    common = sorted(set(s1) & set(s2))
    print('common:', common)


if __name__ == '__main__':
    main()
