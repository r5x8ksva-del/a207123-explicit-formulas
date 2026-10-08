# -*- coding: utf-8 -*-
"""B5 探索（修正版）：骨架型双和
    X(k,q) = sum_{s<=S, p<=Pmax(s)} A(p,s) * C(q+e, p+f) * C(k + a*s + b*p + c, s + q + d)
是否对 X = N^E、N、N^c 成立（A 与 k、q 无关）。用全部 1<=q<=k<=K 的方程（方程数远多于未知数），
先在素数域上比较秩（相容 <=> rank(M) = rank([M|y])），相容时再用 Fraction 精确求解并核对。
上一版的错误：拟合只用到 k<=13（只确定 s<=4 的未知数），却在 k<=20 上检验，连 N^c 的已知公式都被判为失败。
"""
import os, sys, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from explore_b5_ansatz import build_tables, bin_

PR = (1 << 61) - 1


def rank_mod(rows, ncol):
    M = [r[:] for r in rows]
    rk = 0
    for c in range(ncol):
        piv = None
        for i in range(rk, len(M)):
            if M[i][c] % PR:
                piv = i; break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], PR - 2, PR)
        M[rk] = [(v * inv) % PR for v in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] % PR:
                f = M[i][c]
                M[i] = [(x - f * y) % PR for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk


def test(X, K, S, pfun, a, b, c, d, e, f):
    vars_ = [(p, s) for s in range(S + 1) for p in range(pfun(s) + 1)]
    rows = []
    for k in range(1, K + 1):
        for q in range(1, k + 1):
            r = [bin_(q + e, p + f) * bin_(k + a * s + b * p + c, s + q + d) % PR for (p, s) in vars_]
            r.append(X[k][q] % PR)
            rows.append(r)
    n = len(vars_)
    r1 = rank_mod([rr[:n] for rr in rows], n)
    r2 = rank_mod(rows, n + 1)
    return r1 == r2, r1, n, len(rows)


if __name__ == '__main__':
    K = 21
    N, Nc, NE = build_tables(K, K)
    S = 7
    pf = lambda s: 2 * s + 2
    ok, r1, n, ne = test(Nc, K, S, pf, -2, 1, -1, -1, 0, 0)
    print('sanity N^c (a=-2,b=1,c=-1,d=-1): consistent=%s rank=%d unknowns=%d eqs=%d' % (ok, r1, n, ne), flush=True)
    hits = []
    for name, X in (('NE', NE), ('N', N)):
        for a, b in ((-2, 1), (-2, 0), (-1, 1), (-1, 0), (-3, 1), (-2, 2)):
            for c in range(-5, 3):
                for d in range(-3, 2):
                    for e, f in ((0, 0), (1, 0), (-1, 0), (0, 1), (1, 1), (0, -1)):
                        ok, r1, n, ne = test(X, K, S, pf, a, b, c, d, e, f)
                        if ok:
                            hits.append((name, a, b, c, d, e, f, r1, n))
                            print('CONSISTENT', name, (a, b, c, d, e, f), 'rank', r1, 'of', n, flush=True)
    print('hits:', len(hits))
