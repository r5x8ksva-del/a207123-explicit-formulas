# -*- coding: utf-8 -*-
"""x2-dfinite: compare the c3b data tables (core.U_fast_table(40,40), core.N_from_U) with this reviewer's
independently built tables (x2_kernel_check.py rebuilds them from the definition without importing core).
Read-only use of core; nothing is modified."""
import os, sys, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, CODE)
from core import U_fast_table, N_from_U
# load own table builder without running the heavy parts: re-implement the tiny DP here (same as x2_kernel_check.U_col_fast)
def U_col_fast(m, K):
    n = m + 1
    out = [1, n, n * n][:K + 1]
    cnt = [[1] * n for _ in range(n)]
    for _k in range(3, K + 1):
        new = [[0] * n for _ in range(n)]
        for c in range(n):
            suf = [0] * (n + 1); s = 0
            for b in range(n - 1, -1, -1):
                s += cnt[b][c]; suf[b] = s
            for d in range(n):
                new[c][d] = suf[0] if d == c else suf[max(c, d)]
        cnt = new
        out.append(sum(sum(r) for r in cnt))
    return out
mine = [[U_col_fast(m, 40)[k] for m in range(41)] for k in range(41)]
T = U_fast_table(40, 40)
okU = (mine == T)
NT = [[N_from_U(T, k, q) for q in range(41)] for k in range(41)]
from math import comb
def N_ie(k, q):
    return sum((-1) ** (q - i) * comb(q, i) * ((1 if k == 0 else 0) if i == 0 else mine[k][i - 1]) for i in range(q + 1))
okN = all(NT[k][q] == N_ie(k, q) for k in range(41) for q in range(41))
print('PASS' if (okU and okN) else 'FAIL', 'X2-CORE c3b tables core.U_fast_table(40,40) and core.N_from_U == reviewer tables (0<=k,q<=40)')
