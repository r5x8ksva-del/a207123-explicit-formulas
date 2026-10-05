# -*- coding: utf-8 -*-
"""探索 8：(1) r-Stirling 跨层恒等式 h_s(j..m) = sum_t C(m-j+s, m-j+t) S(m-j+t, m-j) j^{s-t}；
(2) Θ 型 / F4 的抵消规模（最大单项位数 vs 结果位数）；(3) H 型的项数统计。"""
import os, sys
from math import comb, factorial
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c2a_lib import *  # noqa
from core import h_complete, stirling2_table

S = stirling2_table(80)
ok = True
for m in range(0, 21):
    for j in range(0, m + 1):
        M = m - j
        for s in range(0, 25):
            rhs = sum(comb(M + s, M + t) * S[M + t][M] * j ** (s - t) for t in range(0, s + 1))
            ok = ok and rhs == h_complete(s, j, m)
print('cross identity h_s(j..m) = sum_t C(m-j+s,m-j+t) S(m-j+t,m-j) j^(s-t)  (m<=20, s<=24):', ok)

for (k, m) in [(30, 12), (60, 20), (100, 100), (200, 30)]:
    C = ctable(m, k + 3 * m + 4)
    mx = 0
    # Theta 型：每个 Theta_t 内的单项 C(t,r) c_{m-r}(n)
    for t in range(m + 1):
        n = k + 1 + 3 * m if t == m else k + 3 * t
        for r in range(t + 1):
            mx = max(mx, comb(t, r) * cval(C, m - r, n))
    mxF4 = 0
    for i in range(m + 1):
        ff = 1
        mxF4 = max(mxF4, comb(m, i) * cval(C, i, k + 3 * m))
        for j in range(1, i + 1):
            ff *= (i - j + 1)
            mxF4 = max(mxF4, comb(m, i) * j * ff * cval(C, i, k + 3 * m - 3 * j - 2))
    U = U_Theta(k, m, C)
    print('k=%d m=%d: digits(U)=%d, max term digits Theta=%d, F4=%d (before dividing by t!/m!)' % (
        k, m, len(str(U)), len(str(mx)), len(str(mxF4))))
    nH = (k // 3 + 1) + sum((k - 2) // 3 + 1 for j in range(1, m + 1)) if k >= 2 else k // 3 + 1
    nTheta = sum(t + 1 for t in range(m + 1))
    print('    number of terms: H form %d (r-Stirling x binomial products); Theta form %d c-values (each c_i(n) is a sum of ~n/3 terms)' % (nH, nTheta))
