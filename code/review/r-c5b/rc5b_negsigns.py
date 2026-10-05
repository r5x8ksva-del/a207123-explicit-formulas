# -*- coding: utf-8 -*-
"""r-c5b 探索：U_k(-j) 在 j > floor((k+2)/3) 时的符号模式（帮助判断 c5b-32 能否简单证明）。
U_k(-j) 由引理 1 的多项式恒等向下递推得到（引理 1 已独立核对其证明）。"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rc5b_verify as V  # noqa: E402  (只用其中的 negvals)

K = 60
Vv = V.negvals(K, K + 3)
rows = []
for k in range(1, 31):
    r = (k + 2) // 3
    s = ''.join('0' if Vv[-j][k] == 0 else ('+' if Vv[-j][k] > 0 else '-') for j in range(1, 31))
    rows.append('k=%2d r=%2d  %s' % (k, r, s))
print('\n'.join(rows))
# 猜测：j>r 时 sign = (-1)^(k - j)？逐项检验
cand = {}
for name, f in [('(-1)^k', lambda k, j: (-1) ** k), ('(-1)^(k+j)', lambda k, j: (-1) ** (k + j)),
                ('(-1)^(k+j+1)', lambda k, j: (-1) ** (k + j + 1))]:
    bad = 0
    for k in range(1, K + 1):
        r = (k + 2) // 3
        for j in range(r + 1, K + 3):
            v = Vv[-j][k]
            if v == 0 or (v > 0) != (f(k, j) > 0):
                bad += 1
    cand[name] = bad
print('sign-pattern mismatches (k<=60, r<j<=62):', cand)
