# -*- coding: utf-8 -*-
"""c3b 探索脚本 2：在 k,m<=40 的精确 U 表与 N 表上搜索线性递推。
E1: U，系数只依赖 k；E2: U，系数依赖 (k,m)；E3a/E3b: N 的同样实验。"""
import sys, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, HERE)
from core import U_fast_table, N_from_U
from relsearch import *

t0 = time.time()
K = M = 40
T = U_fast_table(K, M)
NT = [[N_from_U(T, k, q) for q in range(M + 1)] for k in range(K + 1)]
print('tables built %.1fs; U_40(40) has %d digits' % (time.time() - t0, len(str(T[40][40]))))

p = PRIMES[0]


def run_konly(tab, name, params):
    for (A, B, D) in params:
        unk = unknowns(A, B, monos_konly(D))
        Mx = build_rows_mod(tab, unk, A, K, B, M, p)
        t1 = time.time()
        r, _, _ = rref_mod(Mx, p)
        print('%s k-only  A=%d B=%d deg<=%d: unknowns=%d eqs=%d rank_mod_p=%d -> %s  (%.1fs)'
              % (name, A, B, D, len(unk), Mx.shape[0], r,
                 'NO relation (full rank)' if r == len(unk) else 'kernel dim %d' % (len(unk) - r),
                 time.time() - t1))


def run_total(tab, name, gen, gbox, params, k_off=0):
    out = []
    for (A, B, D) in params:
        unk = unknowns(A, B, monos_total(D))
        k0 = A + k_off
        Mx = build_rows_mod(tab, unk, k0, K, B, M, p)
        t1 = time.time()
        r, _, _ = rref_mod(Mx, p)
        kd = len(unk) - r
        gens = gen_multiples(gen, gbox, A, B, monos_total(D), Dtot=D)
        vecs = [operator_to_vector(g, unk) for g in gens]
        if vecs:
            G = np.array([[c % p for c in v] for v in vecs], dtype=np.int64)
            gr, _, _ = rref_mod(G, p)
        else:
            gr = 0
        ex = all(exact_check(tab, unk, v, k0, K, B, M) for v in vecs)
        print('%s (k,m)-coef A=%d B=%d totdeg<=%d: unknowns=%d eqs=%d rank=%d kernel_dim=%d | '
              'left-multiples of gen: count=%d rank=%d exact=%s  -> %s (%.1fs)'
              % (name, A, B, D, len(unk), Mx.shape[0], r, kd, len(gens), gr, ex,
                 'kernel == span(left multiples)' if (kd == gr and ex) else 'EXTRA relations: %d' % (kd - gr),
                 time.time() - t1))
        out.append((A, B, D, kd, gr))
    return out


print('=== E1: U, coefficients depend on k only ===')
run_konly(T, 'U', [(3, 1, 2), (6, 6, 6), (10, 3, 6), (3, 10, 6), (4, 4, 12), (15, 1, 8), (1, 15, 8), (8, 8, 3)])
print('=== E2: U, coefficients polynomial in (k,m), total degree <= D ===')
run_total(T, 'U', L1, (3, 1), [(3, 1, 1), (3, 1, 2), (3, 1, 3), (4, 1, 2), (4, 2, 2), (5, 2, 2),
                               (6, 2, 3), (5, 3, 3), (8, 2, 2), (3, 4, 4), (6, 4, 2), (4, 3, 4),
                               (2, 6, 4), (6, 0, 4), (3, 3, 0)])
print('=== E3a: N, coefficients depend on k only ===')
run_konly(NT, 'N', [(3, 2, 2), (6, 6, 6), (10, 3, 6), (3, 10, 6), (4, 4, 12), (15, 1, 8), (1, 15, 8), (8, 8, 3)])
print('=== E3b: N, coefficients polynomial in (k,q), total degree <= D ===')
run_total(NT, 'N', LN, (3, 2), [(3, 2, 1), (3, 2, 2), (3, 2, 3), (4, 2, 2), (4, 3, 2), (5, 3, 2),
                                (6, 3, 3), (5, 4, 3), (8, 3, 2), (3, 5, 4), (6, 4, 2), (4, 4, 4),
                                (3, 1, 3), (2, 4, 3), (6, 1, 3)])
print('elapsed %.1fs' % (time.time() - t0))
