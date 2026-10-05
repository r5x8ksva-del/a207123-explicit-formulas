# -*- coding: utf-8 -*-
"""探索 1：DP 锚点 + PDE 残差 + 形式 Laplace 表示的直接展开 vs DP。"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c3a_lib import *

t0 = time.time()
# 锚点：dp_stats 的总数 vs core 的 U_fast_table / U_multichain；细分 vs DFS
T = U_fast_table(40, 20)
ok = True
for m in range(0, 9):
    tot, na, asc = dp_stats(m, 40)
    if tot != [T[k][m] for k in range(41)]:
        ok = False; print('dp_stats tot mismatch m=', m)
for k in range(0, 8):
    for m in range(0, 5):
        tb, nb, ab = brute_stats(m, k)
        tot, na, asc = dp_stats(m, k)
        if (tb, nb, ab) != (tot[k], na[k], asc[k]):
            ok = False; print('brute mismatch', k, m)
        if k <= 7 and m <= 4 and U_multichain(k, m) != tot[k]:
            ok = False; print('multichain mismatch', k, m)
print('anchors:', ok, '%.1fs' % (time.time() - t0))

bad = pde_residual_F(T, 40, 20)
print('PDE residual on DP (k<=40,m<=20):', 'none' if not bad else bad[:5])

for (K, M) in [(24, 12), (30, 16), (36, 20)]:
    t1 = time.time()
    L = laplace_F(K, M)
    good_ = all(L[k][m] == T[k][m] for k in range(K + 1) for m in range(M + 1))
    print('Laplace vs DP K=%d M=%d:' % (K, M), good_, '%.1fs' % (time.time() - t1))
    if not good_:
        for k in range(K + 1):
            for m in range(M + 1):
                if L[k][m] != T[k][m]:
                    print('  first mismatch', k, m, L[k][m], T[k][m]); break
            else:
                continue
            break
