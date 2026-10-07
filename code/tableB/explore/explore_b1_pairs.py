# -*- coding: utf-8 -*-
"""B1 探索（续三）：对 A=n_k, B=n_{k-1}, C=n_{k-2} 及其像 (1+z)X, TX, PhiX, zX
两两测试 <=（度数相容时），列出对所有 8<=k<=K 都成立的关系。只做观察。"""
import sys
sys.path.insert(0, __file__.rsplit('code', 1)[0] + 'code')
from tableB.explore.explore_b1_interlace import N_table  # noqa: E402
from tableB.explore.explore_b1_dir import leq, pmul_1z  # noqa: E402
from tableB.explore.explore_b1_chain import roots_full, T, Phi  # noqa: E402


def zmul(a):
    return [0] + list(a)


if __name__ == '__main__':
    K = 40
    N = N_table(K)
    n = {k: [N[k][q] for q in range(1, k + 1)] for k in range(1, K + 1)}
    ops = {'': lambda p: p, '(1+z)': pmul_1z, 'T': T, 'Phi': Phi, 'z': zmul}
    names = {'A': 0, 'B': 1, 'C': 2}
    results = {}
    for k in range(8, K + 1):
        polys = {}
        for nm, off in names.items():
            for on, f in ops.items():
                polys[on + nm] = f(n[k - off])
        roots = {key: roots_full(v) for key, v in polys.items()}
        for g in polys:
            for f in polys:
                if g == f:
                    continue
                rg, rf = roots[g], roots[f]
                if rg is None or rf is None:
                    ok = False
                elif len(rg) not in (len(rf), len(rf) - 1):
                    continue
                else:
                    ok = leq(rg, rf)
                results.setdefault((g, f), []).append(ok)
    good = [key for key, v in results.items() if all(v) and len(v) == K - 7]
    print('relations g <= f holding for all k in 8..%d:' % K)
    for g, f in sorted(good):
        print('  %-8s <= %s' % (g, f))
