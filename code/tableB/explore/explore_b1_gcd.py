# -*- coding: utf-8 -*-
"""B1 探索（续四）：相邻 n_k 的公因子是否只有 (1+z) 的幂（关系到 h_k 的根两两不同）。
精确有理数 gcd。只做观察。"""
import sys
from fractions import Fraction
sys.path.insert(0, __file__.rsplit('code', 1)[0] + 'code')
from tableB.explore.explore_b1_interlace import N_table  # noqa: E402
from tableB.explore.explore_b1_chain import T, Phi  # noqa: E402


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def pmod(a, b):
    a = [Fraction(x) for x in a]
    b = trim([Fraction(x) for x in b])
    a = trim(a)
    while len(a) >= len(b) and any(a):
        c = a[-1] / b[-1]
        s = len(a) - len(b)
        for i, x in enumerate(b):
            a[s + i] -= c * x
        a = trim(a)
        if len(a) == 1 and a[0] == 0:
            break
    return a


def pgcd(a, b):
    a, b = trim(a), trim(b)
    while not (len(b) == 1 and b[0] == 0):
        a, b = b, pmod(a, b)
    lc = a[-1]
    return [Fraction(x) / lc for x in a]


def mult_minus_one(p):
    """(1+z) 在 p 中的重数。"""
    from math import comb
    p = [Fraction(x) for x in p]
    m = 0
    while len(p) > 1:
        v = sum(x * (-1) ** i for i, x in enumerate(p))
        if v != 0:
            break
        hi = list(reversed(p))
        out = [hi[0]]
        for a in hi[1:]:
            out.append(a - out[-1])
        out.pop()
        p = list(reversed(out))
        m += 1
    return m, p


if __name__ == '__main__':
    K = 40
    N = N_table(K)
    n = {k: [N[k][q] for q in range(1, k + 1)] for k in range(1, K + 1)}
    bad = []
    for k in range(2, K + 1):
        g = pgcd(n[k], n[k - 1])
        m, rest = mult_minus_one(g)
        if len(trim(rest)) > 1:
            bad.append(k)
        # 也看 n_k 本身去掉 (1+z) 后有没有重根：gcd(p, p')
    print('k with gcd(n_k,n_{k-1}) not a power of (1+z):', bad)
    bad2 = []
    for k in range(1, K + 1):
        m, rest = mult_minus_one(n[k])
        rest = trim(rest)
        d = [i * rest[i] for i in range(1, len(rest))] or [0]
        g = pgcd(rest, d) if len(rest) > 1 else [1]
        if len(trim(g)) > 1:
            bad2.append(k)
    print('k with repeated roots in n_k/(1+z)^a:', bad2)
