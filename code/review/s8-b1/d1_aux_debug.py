# -*- coding: utf-8 -*-
"""调试：aux 节在 k=10 内存暴涨。逐条打印，找出是哪一条、哪一步。"""
import sys
import time
import tracemalloc

from px import (deg, add, mul, mulz, mul1z, T, Phi, pgcd, exact_div, is_real_rooted,
                is_squarefree, sturm_count, cauchy_index, srs)
from truth import N_table_from_U, nrow

k = int(sys.argv[1]) if len(sys.argv) > 1 else 10
N = N_table_from_U(k + 2)
n = {j: nrow(N, j) for j in range(1, k + 2)}
A_, B_, C_ = n[k], n[k - 1], n[k - 2]
TA, TB, TC = T(A_), T(B_), T(C_)
PhiA, PhiB, PhiC = Phi(A_), Phi(B_), Phi(C_)
T2C = T(TC)
nk1 = n[k + 1]
terms = [PhiA, mul([0, 1, 1], A_), mul1z(T2C), mul([0, 1, 1], TC)]
rels = [
    ("A<<(1+z)A", A_, mul1z(A_)), ("A<<PhiC", A_, PhiC), ("(1+z)A<<TA", mul1z(A_), TA),
    ("PhiC<<TA", PhiC, TA), ("A<<TB", A_, TB), ("C<<B", C_, B_), ("B<<TC", B_, TC),
    ("TC<<TB", TC, TB), ("A+TC<<TB", add(A_, TC), TB), ("PhiB<<PhiA", PhiB, PhiA),
    ("TB<<zA", TB, mulz(A_)), ("PhiB<<z(1+z)A", PhiB, terms[1]), ("TB<<T(TC)", TB, T2C),
    ("PhiB<<(1+z)T^2C", PhiB, terms[2]), ("TB<<zTC", TB, mulz(TC)), ("PhiB<<z(1+z)TC", PhiB, terms[3]),
]
tracemalloc.start()
for name, g, f in rels:
    t = time.time()
    print("--", name, "deg g", deg(g), "deg f", deg(f), flush=True)
    d = pgcd(f, g)
    print("   gcd deg", deg(d), d if deg(d) < 8 else "...", flush=True)
    print("   is_real_rooted(d)...", flush=True)
    ok_d = is_real_rooted(d)
    print("   ->", ok_d, "mem %.1f MB" % (tracemalloc.get_traced_memory()[1] / 1e6), flush=True)
    f1 = exact_div(f, d)
    g1 = exact_div(g, d)
    print("   sqfree f1...", flush=True)
    print("   ->", is_squarefree(f1), flush=True)
    print("   sturm f1 ->", sturm_count(f1), "deg", deg(f1), flush=True)
    print("   Ind ->", cauchy_index(g1, f1), "%.2fs mem %.1f MB" % (time.time() - t, tracemalloc.get_traced_memory()[1] / 1e6), flush=True)
