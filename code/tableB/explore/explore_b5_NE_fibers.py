# -*- coding: utf-8 -*-
"""B5 附带：N^E_q 的 u 型单族表示。纤维 w（b_w 不可约）上的条件：
    θ_w = (W~_w - 1)(η) * Λ_{q,w}(η) * η^{-g} ∈ Q，Λ_{q,w}(η) = Σ_{M=w}^{q-1} C(q,M+1) η^{-3M-3}/(M-w)!
取范数：N(W~_w - 1) * N((q-1-w)! Λ) * w^{g} 必须是有理数的立方（N(η)=1/w；(q-1-w)!^3 是立方）。
对每个 q 找一条纤维 w∈{2,3,5,6,7}（b_w 不可约）和一个素数 ℓ ∤ w，使 ℓ 的指数之和不被 3 整除，作为证书。
（ℓ 不整除 w 时 g 的选择不影响 ℓ 的指数。）
"""
from fractions import Fraction as Fr
from math import comb, factorial
import sys


def field(w):
    def mul(a, b):
        c = [Fr(0)] * 5
        for i in range(3):
            if a[i] == 0:
                continue
            for j in range(3):
                c[i + j] += a[i] * b[j]
        c[1] += c[4] / w; c[2] -= c[4] / w; c[4] = Fr(0)
        c[0] += c[3] / w; c[1] -= c[3] / w; c[3] = Fr(0)
        return c[:3]

    def norm(a):
        cols = [a, mul(a, [Fr(0), Fr(1), Fr(0)]), mul(a, [Fr(0), Fr(0), Fr(1)])]
        M = [[cols[j][i] for j in range(3)] for i in range(3)]
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    return mul, norm


def vl(n, l):
    n = abs(n); c = 0
    while n and n % l == 0:
        n //= l; c += 1
    return c


def vq(r, l):
    r = Fr(r)
    return vl(r.numerator, l) - vl(r.denominator, l)


def Wt_minus1(w, mul):
    x = [Fr(0), Fr(1), Fr(0)]
    tot = [Fr(0)] * 3
    for j in range(1, w + 1):
        ff = 1
        for t in range(j):
            ff *= (w - t)
        p = [Fr(1), Fr(0), Fr(0)]
        for _ in range(3 * j + 2):
            p = mul(p, x)
        tot = [a + j * ff * b for a, b in zip(tot, p)]
    return tot


if __name__ == '__main__':
    Qmax = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    FIB = [2, 3, 5, 6, 7]
    data = {}
    for w in FIB:
        mul, norm = field(w)
        xinv = [Fr(1), Fr(0), Fr(w)]
        z = mul(mul(xinv, xinv), xinv)          # η^{-3}
        Wm1 = Wt_minus1(w, mul)
        NW = norm(Wm1)
        zp = [[Fr(1), Fr(0), Fr(0)]]
        for _ in range(Qmax + 2):
            zp.append(mul(zp[-1], z))
        data[w] = (mul, norm, NW, zp)
        print('fiber w=%d: N(W~_w - 1) = %s' % (w, NW), flush=True)
    uncovered = []
    for q in range(3, Qmax + 1):
        cert = None
        for w in FIB:
            if w > q - 1:
                continue
            mul, norm, NW, zp = data[w]
            L = [Fr(0)] * 3
            for M in range(w, q):
                co = Fr(comb(q, M + 1) * factorial(q - 1 - w), factorial(M - w))
                L = [a + co * b for a, b in zip(L, zp[M + 1])]
            NL = norm(L)
            tot = NW * NL
            for l in (17, 2, 3, 5, 7, 11, 13, 19, 23, 29, 31, 37, 41, 43, 47):
                if w % l == 0:
                    continue
                if vq(tot, l) % 3:
                    cert = (w, l, vq(tot, l)); break
            if cert:
                break
        if cert is None:
            uncovered.append(q)
        if q % 10 == 0:
            print('q=%d cert=%s' % (q, cert), flush=True)
    print('uncovered q in [3,%d]:' % Qmax, uncovered)
