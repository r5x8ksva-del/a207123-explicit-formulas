# -*- coding: utf-8 -*-
"""B5 探索：
(1) 核对 N(k,q) = sum_{i=0}^{q-1} sum_{t=0}^{q-1-i} (-1)^{q-1-i} C(q,t)/(i!(q-1-i-t)!) * w_i(k+3(q-1-t))   (k>=1)
    w_i(n) = c_i(n) + sum_{j=1}^i j*i^(j) * c_i(n-3j-2)，c_i(n)=[x^n]1/(1-x-i x^3)（n<0 时为 0）；
    以及 N^c、N^E 的对应式（w 换成 c_i、换成 w-c_i）。
(2) N^E 在 c_i 原子下的系数卷积 K(q,i,l) = sum_j j*i^(j) * C(q,l-j)/(q-1-i-l+j)! 是否关于 l 超几何：
    看 K(l+1)/K(l) 能否用低次有理函数插值（固定 q,i）。
"""
import os, sys
from fractions import Fraction
from math import factorial, comb
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from explore_b5_ansatz import build_tables


def c_list(i, N):
    c = [0] * (N + 1)
    for n in range(N + 1):
        c[n] = (1 if n == 0 else c[n - 1]) + (i * c[n - 3] if n >= 3 else 0)
    return c


def ff(i, j):
    r = 1
    for l in range(j):
        r *= (i - l)
    return r


def main():
    K = 26
    Q = 12
    N, Nc, NE = build_tables(K, Q)
    NN = K + 3 * Q + 5
    C = {i: c_list(i, NN) for i in range(Q + 1)}
    def cval(i, n):
        if n < 0:
            return 0
        return 1 if i == 0 else C[i][n]
    def wpart(i, n, which):
        base = cval(i, n)
        ext = sum(j * ff(i, j) * cval(i, n - 3 * j - 2) for j in range(1, i + 1))
        return {'N': base + ext, 'Nc': base, 'NE': ext}[which]
    bad = {'N': 0, 'Nc': 0, 'NE': 0}
    for which, tab in (('N', N), ('Nc', Nc), ('NE', NE)):
        for q in range(1, Q + 1):
            for k in range(1, K + 1):
                tot = Fraction(0)
                for i in range(q):
                    for t in range(q - i):
                        coef = Fraction((-1) ** (q - 1 - i) * comb(q, t), factorial(i) * factorial(q - 1 - i - t))
                        tot += coef * wpart(i, k + 3 * (q - 1 - t), which)
                if tot != tab[k][q]:
                    bad[which] += 1
    print('double-sum check (k=1..%d, q=1..%d): bad =' % (K, Q), bad)
    # (2) K(q,i,l) 是否关于 l 超几何
    def Kc(q, i, l):
        s = Fraction(0)
        for j in range(1, min(i, l) + 1):
            if q - 1 - i - l + j < 0 or l - j > q:
                continue
            s += Fraction(j * ff(i, j) * comb(q, l - j), factorial(q - 1 - i - l + j))
        return s
    for (q, i) in ((8, 3), (10, 4), (12, 5), (14, 6)):
        vals = [Kc(q, i, l) for l in range(1, q + 4)]
        rat = [vals[t + 1] / vals[t] for t in range(len(vals) - 1) if vals[t] != 0 and vals[t + 1] != 0]
        print('q=%d i=%d K(l) for l>=1:' % (q, i), [str(v) for v in vals[:8]])
        print('   ratios:', [str(r) for r in rat[:8]])


if __name__ == '__main__':
    main()
