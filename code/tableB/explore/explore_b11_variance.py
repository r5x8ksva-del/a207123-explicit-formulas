# -*- coding: utf-8 -*-
"""表 B 的 B11 探索：p_d 的「根方差」与 h*-非负所需的上界 ((2d)^2-1)/12 比较。

若 p(k)=sum_j h_j C(k+c-j, n)（n=2d，h_j>=0，c 为任意整数），则 p 的根方差
V(p) := (1/n) sum (r_i - rbar)^2 = (n^2-1)/12 - (n-1) Var_h(j) <= (n^2-1)/12。
这里只做观察：用三角递推算 N，插值得 p_d，精确算 V(p_d)。
"""
import sys
from fractions import Fraction


def N_table(K):
    """N[k][q]，0<=q<=k<=K，按 T1.4(2) 的三角递推（k>=3），初值 k<=2 直接给出。"""
    N = [[0] * (K + 2) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1], N[2][2] = 1, 2

    def g(k, q):
        if k < 0 or q < 0 or q > k:
            return 0
        return N[k][q]
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            r = q - 1
            N[k][q] = g(k - 1, r) + g(k - 1, r + 1) + r * (g(k - 3, r - 1) + 2 * g(k - 3, r) + g(k - 3, r + 1))
    return N


def interp_coeffs(xs, ys):
    """Newton 插值后展开为单项式系数（Fraction），返回 c[0..n]。"""
    n = len(xs)
    coef = [Fraction(y) for y in ys]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (xs[i] - xs[i - j])
    poly = [Fraction(0)] * n
    poly[0] = coef[n - 1]
    deg = 0
    for i in range(n - 2, -1, -1):
        # poly = poly*(x - xs[i]) + coef[i]
        new = [Fraction(0)] * n
        for t in range(deg + 1):
            new[t + 1] += poly[t]
            new[t] -= poly[t] * xs[i]
        new[0] += coef[i]
        poly = new
        deg += 1
    return poly


def main():
    D = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    K = 4 * D + 4
    N = N_table(K)
    print('d  V(p_d)           bound=(n^2-1)/12   V-bound')
    for d in range(1, D + 1):
        xs = list(range(2 * d + 2, 4 * d + 3))
        ys = [N[k][k - d] for k in xs]
        c = interp_coeffs(xs, ys)
        n = 2 * d
        assert c[n] != 0 and all(x == 0 for x in c[n + 1:])
        a = c[n - 1] / c[n]        # monic: x^n + a x^{n-1} + b x^{n-2}
        b = c[n - 2] / c[n]
        s1 = -a                    # sum of roots
        s2 = a * a - 2 * b         # sum of squares
        V = s2 / n - (s1 / n) ** 2
        bound = Fraction(n * n - 1, 12)
        print('%2d %16.4f %16.4f %16.4f   mean=%s' % (d, float(V), float(bound), float(V - bound), s1 / n))


if __name__ == '__main__':
    main()
