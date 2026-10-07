# -*- coding: utf-8 -*-
"""表 B 的 B2 探索（E 部分）：纤维 i=1,2,3 上留数元 (Wt_i - 1) eta^{-3m-3}，
条件 1, eta^b, (Wt_i(eta)-1) eta^n 在 Q 上线性相关（与 m 无关）。Wt_i - 1 = sum_{j=1}^i j * i^(j) * x^(3j+2)。"""
import sys
from fractions import Fraction
sys.path.insert(0, __file__.rsplit('explore', 1)[0] + 'explore')
from explore_b2_fibers import make_field, powers, dependent  # noqa: E402


def falling(i, j):
    r = 1
    for t in range(j):
        r *= (i - t)
    return r


def Wt_minus_1(mul, P, i):
    acc = [Fraction(0)] * 3
    for j in range(1, i + 1):
        c = j * falling(i, j)
        v = P[3 * j + 2]
        acc = [acc[t] + c * v[t] for t in range(3)]
    return acc


def sols(i, R):
    f = [Fraction(1, i), Fraction(-1, i), 0]   # x^3 = (1-x)/i
    mul = make_field(f)
    x = [Fraction(0), Fraction(1), Fraction(0)]
    P = powers(mul, x, 2 * R + 40)
    W = Wt_minus_1(mul, P, i)
    out = []
    for n in range(-R, R + 1):
        w = mul(W, P[n])
        for b in range(-R, R + 1):
            if b and dependent(P[b], w):
                out.append((n, b))
    return out


if __name__ == '__main__':
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    S = {}
    for i in (1, 2, 3):
        S[i] = sols(i, R)
        print('E fiber %d (|n|,|b|<=%d): %d sols' % (i, R, len(S[i])), S[i][:80])
    print('E common 1&2:', sorted(set(S[1]) & set(S[2])))
    print('E common 1&2&3:', sorted(set(S[1]) & set(S[2]) & set(S[3])))
