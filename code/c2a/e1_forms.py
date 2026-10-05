# -*- coding: utf-8 -*-
"""探索 1：各显式形式对照 core 高度 DP（U_fast_table）。"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c2a_lib import *  # noqa
from core import U_fast_table, U_height_table

for (K, M) in [(30, 12), (60, 20)]:
    t0 = time.time()
    T = U_fast_table(K, M)
    t1 = time.time()
    H = hgrid(M, K + 2)
    C = ctable(M, K + 3 * M + 4)
    forms = {
        'H': lambda k, m: U_H(k, m, H),
        'F3': lambda k, m: U_F3(k, m, H),
        'Theta': lambda k, m: U_Theta(k, m, C),
        'ThetaH': lambda k, m: U_ThetaH(k, m, C),
        'F4': lambda k, m: U_F4(k, m, C),
    }
    R = U_rec_table(K, M)
    print('K=%d M=%d  DP time %.2fs' % (K, M, t1 - t0))
    print('  Lemma1 rec table == DP:', R == T)
    for name, f in forms.items():
        t2 = time.time()
        bad = [(k, m) for k in range(K + 1) for m in range(M + 1) if f(k, m) != T[k][m]]
        print('  %-7s mismatches=%d  (%.2fs)' % (name, len(bad), time.time() - t2), bad[:5])
    Nt = N_triangle(K)
    bad = [(k, m) for k in range(K + 1) for m in range(M + 1)
           if sum(Nt[k][q] * binom(m + 1, q) for q in range(0, k + 1)) != T[k][m]]
    print('  N-triangle sum mismatches:', len(bad), bad[:5])
# 参考实现交叉：U_height_table（逐字照抄的参考实现）对 k<=30, m<=12
T1 = U_height_table(30, 12)
T2 = U_fast_table(30, 12)
print('reference U_list table == fast DP (k<=30,m<=12):', T1 == T2)
