# -*- coding: utf-8 -*-
"""探索 6：合法满射词 N(k,q) 的块分解 + 覆盖计数。

T 骨架（arc system）：s 条弧 (v_1,a_1),...,(v_s,a_s)，0<=a_i<v_i，v_1>=...>=v_s（同头的弧有序）。
完整（不以上升结尾）满射词 = T 骨架 + 在 s+q 个缝隙中放 S，未被骨架覆盖的值所在的缝隙必须至少放一个 S。
  R(p,s) = 端点集恰为 {0..p-1} 的 T 骨架数。
  断言：N^c(k,q) = sum_s sum_p C(q,p) R(p,s) C(k-2s+p-1, s+q-1)。
  R 的容斥：R(p,s) = sum_i (-1)^{p-i} C(p,i) Hs(i,s)，Hs(i,s) = h_s(0..i-1)（i>=1）= S(i-1+s,i-1)，Hs(0,s)=[s=0]。
"""
import sys, os, time
from math import comb
from itertools import product
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import core
from formulas import refined_dp, binom, stirling2, hcomp
from blocks import dfs_legal, good3


def arc_systems(p, s):
    """枚举端点 ⊆ {0..p-1} 的全部 T 骨架（弧序列，头非增）。"""
    out = []
    cur = []

    def rec(rem, top):
        if rem == 0:
            out.append(tuple(cur))
            return
        for v in range(top, 0, -1):
            for a in range(v):
                cur.append((v, a))
                rec(rem - 1, v)
                cur.pop()

    rec(s, p - 1)
    return out


def R_brute(p, s):
    return sum(1 for sys_ in arc_systems(p, s)
               if set(x for arc in sys_ for x in arc) == set(range(p)))


def Hs(i, s):
    if i == 0:
        return 1 if s == 0 else 0
    return stirling2(i - 1 + s, i - 1)


def R_ie(p, s):
    return sum((-1) ** (p - i) * comb(p, i) * Hs(i, s) for i in range(p + 1))


if __name__ == '__main__':
    t0 = time.time()
    ok = True
    for p in range(0, 8):
        for s in range(0, 5):
            if R_brute(p, s) != R_ie(p, s):
                ok = False
                print('R mismatch', p, s, R_brute(p, s), R_ie(p, s))
    print('R(p,s) brute (arc systems) == inclusion-exclusion, p<=7 s<=4:', ok)
    print('R table (rows s=0..7, cols p=0..14):')
    for s in range(0, 8):
        print('  s=%d:' % s, [R_ie(p, s) for p in range(0, 15)])

    # N^c, N^E data from direct DP + inclusion-exclusion; also brute force by DFS for small k
    K, QQ = 30, 12
    T = core.U_fast_table(K, QQ)
    A = {}; E = {}
    for m in range(0, QQ + 1):
        tot, asc = refined_dp(K, m)
        E[m] = [sum(asc[k]) for k in range(K + 1)]
        A[m] = [T[k][m] - E[m][k] for k in range(K + 1)]

    def ie(tab, k, q, base):
        return sum((-1) ** (q - i) * comb(q, i) * ((base if k == 0 else 0) if i == 0 else tab[i - 1][k]) for i in range(q + 1))

    Nc = {q: [ie(A, k, q, 1) for k in range(K + 1)] for q in range(1, QQ + 1)}
    NE = {q: [ie(E, k, q, 0) for k in range(K + 1)] for q in range(1, QQ + 1)}
    # brute force surjective words by DFS (k<=8)
    okb = True
    for k in range(1, 9):
        L = dfs_legal(k, k - 1)
        cntc = {}; cnte = {}
        for h in L:
            st = set(h); q = len(st)
            if st != set(range(q)):
                continue
            if k >= 2 and h[-2] < h[-1]:
                cnte[q] = cnte.get(q, 0) + 1
            else:
                cntc[q] = cntc.get(q, 0) + 1
        for q in range(1, min(k, QQ) + 1):
            if cntc.get(q, 0) != Nc[q][k] or cnte.get(q, 0) != NE[q][k]:
                okb = False
    print('N^c, N^E by inclusion-exclusion == DFS brute force (k<=8):', okb)

    def Nc_formula(k, q):
        tot = 0
        for s in range(0, k // 3 + 1):
            for p in range(0, 2 * s + 1):
                r = R_ie(p, s)
                if r:
                    tot += comb(q, p) * r * binom(k - 2 * s + p - 1, s + q - 1)
        return tot

    ok = all(Nc_formula(k, q) == Nc[q][k] for q in range(1, QQ + 1) for k in range(0, K + 1))
    print('N^c(k,q) = sum_{s,p} C(q,p) R(p,s) C(k-2s+p-1, s+q-1) == DP, k<=%d q<=%d:' % (K, QQ), ok)
    print('N^c table rows k=1..10:', [[Nc[q][k] for q in range(1, k + 1)] for k in range(1, 11)])
    print('N^E table rows k=1..10:', [[NE[q][k] for q in range(1, k + 1)] for k in range(1, 11)])
    print('elapsed %.1fs' % (time.time() - t0))
