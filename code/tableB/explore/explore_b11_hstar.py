# -*- coding: utf-8 -*-
"""表 B 的 B11 探索：对每个整数平移 s，算 p_d 的 h*-向量（基 C(k-s+2d-j, 2d)），看哪些分量为负。

h*_j(s) = sum_{i=0}^{j} (-1)^i C(2d+1, i) p_d(s+j-i)。
只做观察。
"""
import sys
from fractions import Fraction
from math import comb
sys.path.insert(0, __file__.rsplit('explore', 1)[0] + 'explore')
from explore_b11_variance import N_table, interp_coeffs  # noqa: E402


def peval(c, x):
    v = Fraction(0)
    for a in reversed(c):
        v = v * x + a
    return v


def hstar(c, d, s):
    n = 2 * d
    vals = {}
    out = []
    for j in range(n + 1):
        t = Fraction(0)
        for i in range(j + 1):
            x = s + j - i
            if x not in vals:
                vals[x] = peval(c, x)
            t += (-1) ** i * comb(n + 1, i) * vals[x]
        out.append(t)
    return out


def main():
    D = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    K = 4 * D + 4
    N = N_table(K)
    for d in range(1, D + 1):
        xs = list(range(2 * d + 2, 4 * d + 3))
        ys = [N[k][k - d] for k in xs]
        c = interp_coeffs(xs, ys)
        n = 2 * d
        print('d=%d  2(2d-1)!!=%d' % (d, 2 * eval('*'.join(str(i) for i in range(1, 2 * d, 2)))))
        for s in range(-2, 4 * d + 3):
            h = hstar(c, d, s)
            negs = [j for j in range(n + 1) if h[j] < 0]
            mark = ''.join('-' if x < 0 else ('0' if x == 0 else '+') for x in h)
            print('  s=%3d  %s  neg=%s  h0=%s h1=%s h_{2d-1}=%s h_2d=%s' % (
                s, mark, negs[:6], h[0], h[1], h[n - 1], h[n]))


if __name__ == '__main__':
    main()
