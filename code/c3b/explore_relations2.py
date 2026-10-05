# -*- coding: utf-8 -*-
"""c3b 探索脚本 4：更大的参数扫描（日志用）。"""
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
p = PRIMES[1]   # 换一个素数
print('prime', p)

def konly(tab, name, params):
    for (A, B, D) in params:
        unk = unknowns(A, B, monos_konly(D))
        Mx = build_rows_mod(tab, unk, A, K, B, M, p)
        r, _, _ = rref_mod(Mx, p)
        print('%s k-only (A,B,deg)=(%d,%d,%d): %d unknowns, %d eqs, rank %d -> %s'
              % (name, A, B, D, len(unk), Mx.shape[0], r, 'none' if r == len(unk) else 'KERNEL %d' % (len(unk) - r)))

def km(tab, name, gen, gbox, params, pred):
    for (A, B, D) in params:
        unk = unknowns(A, B, monos_total(D))
        Mx = build_rows_mod(tab, unk, A, K, B, M, p)
        r, _, _ = rref_mod(Mx, p)
        gens = gen_multiples(gen, gbox, A, B, monos_total(D), Dtot=D)
        vecs = [operator_to_vector(g, unk) for g in gens]
        gr = rref_mod(np.array([[c % p for c in v] for v in vecs], dtype=np.int64), p)[0] if vecs else 0
        ex = all(exact_check(tab, unk, v, A, K, B, M) for v in vecs)
        print('%s (A,B,D)=(%d,%d,%d): %d unknowns, %d eqs, kernel %d, predicted %d, left multiples %d (rank %d, exact %s)'
              % (name, A, B, D, len(unk), Mx.shape[0], len(unk) - r, pred(A, B, D), len(vecs), gr, ex))

predU = lambda A, B, D: (A - 2) * B * D * (D + 1) // 2 if (A >= 3 and B >= 1 and D >= 1) else 0
predN = lambda A, B, D: (A - 2) * (B - 1) * D * (D + 1) // 2 if (A >= 3 and B >= 2 and D >= 1) else 0

konly(T, 'U', [(20, 1, 6), (1, 20, 6), (5, 5, 9), (2, 2, 30), (12, 12, 1), (0, 25, 10), (25, 0, 10)])
konly(NT, 'N', [(20, 1, 6), (1, 20, 6), (5, 5, 9), (2, 2, 30), (12, 12, 1), (0, 25, 10), (25, 0, 10)])
km(T, 'U', {(0, 0): {(0, 0): 1}, (0, 1): {(0, 0): -1}, (1, 0): {(0, 0): -1}, (3, 0): {(0, 1): -1}}, (3, 1),
   [(7, 3, 3), (5, 5, 3), (3, 1, 8), (9, 2, 2), (4, 6, 2)], predU)
km(NT, 'N', {(0, 0): {(0, 0): 1}, (1, 0): {(0, 0): -1}, (1, 1): {(0, 0): -1},
             (3, 0): {(0, 1): -1, (0, 0): 1}, (3, 1): {(0, 1): -2, (0, 0): 2}, (3, 2): {(0, 1): -1, (0, 0): 1}}, (3, 2),
   [(7, 3, 3), (5, 5, 3), (3, 2, 8), (9, 3, 2), (4, 6, 2)], predN)
print('elapsed %.1fs' % (time.time() - t0))
