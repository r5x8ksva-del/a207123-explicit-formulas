# -*- coding: utf-8 -*-
"""B1 探索（续）：p_k := n_k / (1+z)^{a_k}（a_k = floor((k-1)/3)）之间交错关系的方向。

记号：f, g 实根、首项为正。g <= f（g 交错 f，「g 在左」）指
  deg g = deg f = n：b_1 <= a_1 <= b_2 <= ... <= b_n <= a_n；
  deg g = n-1：      a_1 <= b_1 <= a_2 <= ... <= b_{n-1} <= a_n。
p_k = c_k p_{k-1} + D_k p_{k-3}，c_k = 1（k = 1 mod 3）或 1+z（其他），
D_k p = z[(1+z) p' + (a_k + 1) p]。只做观察。
"""
import sys
sys.path.insert(0, __file__.rsplit('code', 1)[0] + 'code')
from tableB.explore.explore_b1_interlace import N_table, strip_minus_one, real_roots  # noqa: E402

TOL = 1e-12


def leq(g, f):
    """g <= f（见文件头）。g, f 为升序根列表。"""
    n = len(f)
    if len(g) == n:
        return all(g[i] <= f[i] + TOL for i in range(n)) and all(f[i] <= g[i + 1] + TOL for i in range(n - 1))
    if len(g) == n - 1:
        return all(f[i] <= g[i] + TOL and g[i] <= f[i + 1] + TOL for i in range(n - 1))
    return False


def padd(a, b):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def pmul_1z(a):
    out = [0] * (len(a) + 1)
    for i, x in enumerate(a):
        out[i] += x
        out[i + 1] += x
    return out


def D(p, a):
    """z[(1+z)p' + (a+1)p]"""
    d = [i * p[i] for i in range(1, len(p))]
    t = padd(pmul_1z(d) if d else [0], [(a + 1) * x for x in p])
    return [0] + t


if __name__ == '__main__':
    K = 45
    N = N_table(K)
    p = {}
    for k in range(1, K + 1):
        c, mult = strip_minus_one([N[k][q] for q in range(1, k + 1)])
        assert mult == (k - 1) // 3, (k, mult)
        p[k] = c
    # 核对 p 的递推
    for k in range(4, K + 1):
        a = (k - 1) // 3
        first = p[k - 1] if k % 3 == 1 else pmul_1z(p[k - 1])
        assert padd(first, D(p[k - 3], a)) == p[k], k
    print('p_k recurrence OK up to', K)
    R = {k: real_roots(p[k]) for k in range(1, K + 1)}
    assert all(R[k] is not None for k in R)
    for k in range(1, 9):
        print(k, p[k], [round(x, 4) for x in R[k]])
    rel = {}
    for k in range(3, K + 1):
        a = (k - 1) // 3
        Dk = D(p[k - 3], a) if k >= 4 else None
        RD = real_roots(Dk) if Dk else None
        first = p[k - 1] if k % 3 == 1 else pmul_1z(p[k - 1])
        Rf = real_roots(first)
        row = {
            'p[k-1]<=p[k]': leq(R[k - 1], R[k]),
            'p[k]<=p[k-1]': leq(R[k], R[k - 1]),
            'p[k-2]<=p[k]': leq(R[k - 2], R[k]) if k >= 3 else None,
            'p[k]<=p[k-2]': leq(R[k], R[k - 2]) if k >= 3 else None,
        }
        if RD is not None:
            row['D<=first'] = leq(RD, Rf)
            row['first<=D'] = leq(Rf, RD)
            row['D<=p[k]'] = leq(RD, R[k])
            row['p[k]<=D'] = leq(R[k], RD)
            row['p[k-1]<=D'] = leq(R[k - 1], RD)
            row['D<=p[k-1]'] = leq(RD, R[k - 1])
        rel[k] = row
    keys = sorted({kk for r in rel.values() for kk in r})
    for kk in keys:
        holds = [k for k in rel if rel[k].get(kk)]
        fails = [k for k in rel if rel[k].get(kk) is False]
        print('%-14s holds:%s' % (kk, holds))
        print('%-14s fails:%s' % ('', fails))
