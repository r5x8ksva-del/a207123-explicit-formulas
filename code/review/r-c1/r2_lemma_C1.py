# -*- coding: utf-8 -*-
"""r-c1 独立复核 2：引理 1 与 (C1)（L1、C1-sum、C1-poly）。

真值：自写高度 DP（rc1lib.U_column，已在 r1_defs.py 中与原题矩阵计数、多重链、core 参考实现交叉核对）。
  L1a  引理 1（含边界约定）：k<=132,m<=30；k<=60,m<=66；以及 m in {99,100,149,150} 的整列 k<=25（大 m 抽查）
  C1a  (C1) 求和式：同上范围
  C1b  (C1) 精确多项式：对每个 0<=k<=60，用 m=0..k 共 k+1 个点做 Newton 插值得到 u_k（Fraction 单项式系数），
       然后检查 (i) u_k(m)==U_k(m) 对全部 m<=66（至少 6 个额外点）；(ii) deg=k，首项 2/k!（k>=2）、1（k=0,1）；
       (iii) u_k(-1)=0（k>=1）；(iv) 多项式恒等式 u_k(x)-u_k(x-1) == u_{k-1}(x)+x*u_{k-3}(x)（1<=k<=60，u_{-1}=1,u_{-2}=0）
"""
import os
import sys
import time
from fractions import Fraction
from math import factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rc1lib import U_table, U_column, Ub, Reporter, trim, add, sub, mul, ev, poly_shift_arg  # noqa: E402

rep = Reporter('r-c1-lemma-C1')
T0 = time.time()
TM = U_table(60, 66)
TL = U_table(132, 30)
print('INFO tables built [%.1fs]' % (time.time() - T0), flush=True)


def lemma_bad(T, K, M):
    return [(k, m) for k in range(1, K + 1) for m in range(0, M + 1)
            if T[k][m] != Ub(T, k, m - 1) + Ub(T, k - 1, m) + m * Ub(T, k - 3, m)]


def sum_bad(T, K, M):
    return [(k, m) for k in range(1, K + 1) for m in range(0, M + 1)
            if T[k][m] != sum(Ub(T, k - 1, j) + j * Ub(T, k - 3, j) for j in range(m + 1))]


t = time.time()
b1 = lemma_bad(TL, 132, 30)
b2 = lemma_bad(TM, 60, 66)
cols = {m: U_column(m, 25) for m in (99, 100, 149, 150)}
b3 = []
for m in (100, 150):
    for k in range(1, 26):
        lhs = cols[m][k]
        rhs = cols[m - 1][k] + cols[m][k - 1] + m * (cols[m][k - 3] if k >= 3 else (1 if k == 2 else 0))
        if lhs != rhs:
            b3.append((k, m))
rep('L1a', not (b1 or b2 or b3), '引理1（含边界约定 U_{-1}≡1,U_{-2}≡0,U_k(-1)=0）对自写 DP：k<=132,m<=30；k<=60,m<=66；m=100,150 时 k<=25 [%.1fs] %s'
    % (time.time() - t, (b1 + b2 + b3)[:3]))

t = time.time()
s1 = sum_bad(TL, 132, 30)
s2 = sum_bad(TM, 60, 66)
rep('C1a', not (s1 or s2), '(C1) U_k(m)=sum_{j<=m}[U_{k-1}(j)+j U_{k-3}(j)]：k<=132,m<=30；k<=60,m<=66 [%.1fs] %s'
    % (time.time() - t, (s1 + s2)[:3]))

# ---------------- C1b 精确多项式 ----------------
t = time.time()
NMAXS = 61
# 带符号第一类 Stirling：x(x-1)...(x-j+1) = sum_i s1[j][i] x^i
s1t = [[0] * (NMAXS + 1) for _ in range(NMAXS + 1)]
s1t[0][0] = 1
for j in range(1, NMAXS + 1):
    for i in range(1, j + 1):
        s1t[j][i] = s1t[j - 1][i - 1] - (j - 1) * s1t[j - 1][i]


def interp(k):
    """过 m=0..k 的插值多项式（Fraction 单项式系数）。"""
    vals = [TM[k][m] for m in range(k + 1)]
    d = []
    cur = vals[:]
    for j in range(k + 1):
        d.append(cur[0])
        cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
    poly = [Fraction(0)] * (k + 1)
    for j in range(k + 1):
        if d[j]:
            c = Fraction(d[j], factorial(j))
            for i in range(j + 1):
                poly[i] += c * s1t[j][i]
    return trim(poly)


U_POLY = {-2: [], -1: [Fraction(1)]}
bad = []
for k in range(0, 61):
    u = interp(k)
    U_POLY[k] = u
    if len(u) - 1 != k:
        bad.append(('deg', k))
        continue
    lc_exp = Fraction(2, factorial(k)) if k >= 2 else Fraction(1)
    if u[-1] != lc_exp:
        bad.append(('lc', k))
    if k >= 1 and ev(u, -1) != 0:
        bad.append(('u(-1)', k))
    if any(ev(u, m) != TM[k][m] for m in range(67)):
        bad.append(('values', k))
for k in range(1, 61):
    lhs = sub(U_POLY[k], poly_shift_arg(U_POLY[k], -1))
    rhs = add(U_POLY[k - 1], mul([0, 1], U_POLY[k - 3]))
    if lhs != rhs:
        bad.append(('identity', k))
rep('C1b', not bad, '(C1) 精确插值：u_k 过 m=0..k，k<=60：在全部 m<=66 与 DP 一致（>=6 个额外点）、deg=k、首项 2/k!（k>=2；k=0,1 为 1）、'
    'u_k(-1)=0（k>=1）、多项式恒等式 u_k(x)-u_k(x-1)=u_{k-1}(x)+x u_{k-3}(x)（1<=k<=60） [%.1fs] %s' % (time.time() - t, bad[:3]))

print('TIME r2 total %.1fs' % (time.time() - T0), flush=True)
sys.exit(0 if rep.summary() else 1)
