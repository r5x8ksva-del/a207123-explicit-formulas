# -*- coding: utf-8 -*-
"""探索：(C2) 的最简性。
1) 直接 pgcd(W_m, P_m)（Fraction 欧几里得）；
2) 约化：gcd(W_m, P_m) = prod_i gcd(W_i mod b_i, b_i)；
3) Berlekamp-Massey 直接从高度 DP 数据求最小递推阶（与闭式无关）；
4) b_i 的有理根（y^3 - y^2 - i 的整数根）。
"""
import sys, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from fractions import Fraction
from core import U_fast_table
from polylib import P_poly, b_poly, pmul, padd, psub, pscale, pshift, trim, pdiv, pgcd


def W_poly(m):
    """W_m = 1 + x^2 sum_{j=1}^m j P_{j-1}；W_{-1} = 1。"""
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
    return W


def berlekamp_massey(seq):
    """有理数域上的 BM：返回连接多项式 C（C[0]=1）与线性复杂度 L。"""
    s = [Fraction(v) for v in seq]
    C = [Fraction(1)]
    B = [Fraction(1)]
    L = 0
    m = 1
    b = Fraction(1)
    for n in range(len(s)):
        d = s[n]
        for i in range(1, L + 1):
            if i < len(C):
                d += C[i] * s[n - i]
        if d == 0:
            m += 1
            continue
        coef = d / b
        T = C[:]
        need = len(B) + m
        if len(C) < need:
            C = C + [Fraction(0)] * (need - len(C))
        for i, bi in enumerate(B):
            C[i + m] -= coef * bi
        if 2 * L <= n:
            L = n + 1 - L
            B = T
            b = d
            m = 1
        else:
            m += 1
    C = trim(C)
    return C, L


if __name__ == '__main__':
    MMAX = 20
    t0 = time.time()
    K = 2 * (3 * MMAX + 1) + 10
    T = U_fast_table(K, MMAX)
    print('DP table K=%d M=%d in %.2fs' % (K, MMAX, time.time() - t0))

    # 4) rational roots
    for i in range(1, 60):
        roots = [y for y in range(1, i + 2) if y ** 3 - y ** 2 == i]
        if roots:
            print('b_%d reducible: y=%s' % (i, roots))

    # 2) reduction via remainders
    for i in range(0, MMAX + 1):
        Wi = W_poly(i)
        q, r = pdiv(Wi, b_poly(i))
        g = pgcd(r, b_poly(i)) if r else 'b_i itself'
        print('i=%2d  W_i mod b_i = %s   gcd = %s' % (i, [str(c) for c in r], g if isinstance(g, str) else [str(c) for c in g]))

    # 1) direct pgcd
    for m in range(0, MMAX + 1):
        t = time.time()
        g = pgcd(W_poly(m), P_poly(m))
        print('m=%2d  deg gcd(W_m,P_m) = %d  (%.2fs)' % (m, len(g) - 1, time.time() - t))

    # 3) BM from DP data
    for m in range(0, MMAX + 1):
        t = time.time()
        L0 = 3 * m + 1
        seq = [T[k][m] for k in range(0, 2 * L0 + 6)]
        C, L = berlekamp_massey(seq)
        Pm = P_poly(m)
        ok = (L == L0) and ([Fraction(c) for c in C] == [Fraction(c) for c in Pm])
        print('m=%2d  BM linear complexity L=%d (3m+1=%d), C==P_m: %s  (%.2fs)' % (m, L, L0, ok, time.time() - t))
    print('total %.1fs' % (time.time() - t0))
