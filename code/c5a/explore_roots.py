# -*- coding: utf-8 -*-
"""c5a 探索 7：h_k 实根的精确隔离（Sturm + 有理二分），检查相邻 h_k 的根是否交错；记录根的分布。"""
import os, sys, time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_fast_table
from explore_h import h_from_U, ev, sturm_real_roots


def V(seq, x):
    vals = [ev(s, x) for s in seq]
    vals = [v for v in vals if v != 0]
    return sum(1 for u, w in zip(vals, vals[1:]) if (u > 0) != (w > 0))


def isolate(p, lo, hi, width):
    nreal, sqf, seq = sturm_real_roots(p)
    stack = [(Fraction(lo), Fraction(hi))]
    roots = []
    while stack:
        a, b = stack.pop()
        n = V(seq, a) - V(seq, b)
        if n == 0:
            continue
        if n == 1 and b - a < width:
            roots.append((a, b))
            continue
        mid = (a + b) / 2
        if ev(p, mid) == 0:
            mid += (b - a) / 1000
        stack.append((a, mid))
        stack.append((mid, b))
    roots.sort()
    return roots


def main():
    t0 = time.time()
    K = 36
    T = U_fast_table(K, K)
    H = {k: h_from_U(T, k) for k in range(0, K + 1)}
    R = {}
    for k in range(2, K + 1):
        R[k] = [(a + b) / 2 for a, b in isolate(H[k], -10 ** 6, 10 ** 6, Fraction(1, 10 ** 12))]
    out = []
    for k in (6, 9, 12, 18, 24, 30, 36):
        out.append('k=%d roots: %s' % (k, ['%.6g' % float(r) for r in R[k]]))
    # interlacing check between h_k and h_{k+1}
    def interlace(a, b):
        """a, b 排好序；检查是否交错（deg 相等或差 1）。"""
        merged = sorted([(x, 0) for x in a] + [(x, 1) for x in b])
        labs = [l for _, l in merged]
        return all(labs[i] != labs[i + 1] for i in range(len(labs) - 1))
    res1 = [k for k in range(2, K) if not interlace(R[k], R[k + 1])]
    out.append('h_k vs h_{k+1} NOT interlacing at k in: %s' % res1)
    # separately negative / positive parts
    out.append('min root, max root (k=12..36 step 6): %s' % [(k, '%.4g' % float(R[k][0]), '%.4g' % float(R[k][-1])) for k in range(12, K + 1, 6)])
    out.append('elapsed %.1fs' % (time.time() - t0))
    print('\n'.join(out))


if __name__ == '__main__':
    main()
