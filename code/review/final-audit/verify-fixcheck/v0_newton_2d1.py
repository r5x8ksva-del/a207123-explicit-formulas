# -*- coding: utf-8 -*-
"""verify-fixcheck #0：独立复核「基点 2d+1 的 Newton 系数」的符号。

与 fixcheck 的做法不同（它用三角递推算 N）：这里
  (a) 用 y=1 的 T2.2 递推 U_k(m)=U_k(m-1)+U_{k-1}(m)+m U_{k-3}(m)+m[k=2]（U_k(-1)=[k=0]）
      建 U 表，先与 core.U_fast_table（定义 DP）对照；
  (b) 用容斥 N(k,q)=sum_i (-1)^{q-i} C(q,i) U_k(i-1) 得 D(k,d)=N(k,k-d)；
  (c) p_d(2d+1) 不用缺陷公式，而用 k>=2d+2 处 2d+1 个值做多项式外推，再与
      D(2d+1,d)-(-1)^{d+1}(d+1)! 对照；并在 k=2d+2..4d+3 上检验 Delta^{2d+1}=0。
输出：每个 d 的非正 Newton 系数下标（基点 2d+1），以及基点 2d+2 的正性。
"""
import sys
import time
from math import comb, factorial

sys.path.insert(0, r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\code')
import core  # noqa: E402

T0 = time.time()
DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 101
KMAX = 4 * DMAX + 3
MMAX = KMAX - DMAX  # q<=k-d 的最大值；需要 U_k(m) 到 m=q-1

# (a) U 表：U[k][m+1] 存 U_k(m)，m=-1..MMAX
U = [[0] * (MMAX + 2) for _ in range(KMAX + 1)]
for k in range(KMAX + 1):
    U[k][0] = 1 if k == 0 else 0           # U_k(-1)
    row = U[k]
    for m in range(0, MMAX + 1):
        v = row[m]                            # U_k(m-1)
        if k >= 1:
            v += U[k - 1][m + 1]
        if k >= 3:
            v += m * U[k - 3][m + 1]
        if k == 2:
            v += m
        row[m + 1] = v
T = core.U_fast_table(40, 15)
ok_a = all(T[k][m] == U[k][m + 1] for k in range(41) for m in range(16))
print('U-table (T2.2 at y=1 recurrence) == core.U_fast_table (k<=40, m<=15):', ok_a)
print('U-table built k<=%d, m<=%d  [%.1fs]' % (KMAX, MMAX, time.time() - T0))


def N(k, q):
    s = 0
    for i in range(q + 1):
        s += (-1) ** (q - i) * comb(q, i) * U[k][i]   # U[k][i] = U_k(i-1)
    return s


# 小 k 处对照 DFS 定义
okN = True
for k in range(0, 9):
    br = core.N_brute(k)
    for q in range(0, k + 1):
        if N(k, q) != br.get(q, 0):
            okN = False
print('N by inclusion-exclusion == core.N_brute DFS (k<=8):', okN)

first_bad = None
bad = {}
poly_ok = True
extrap_ok = True
base2_ok = True
for d in range(1, DMAX + 1):
    # v[j] = D(2d+1+j, d), j=0..2d+2
    v = [N(2 * d + 1 + j, d + 1 + j) for j in range(2 * d + 3)]
    # Delta^{2d+1} on k=2d+2..4d+3 (j=1..2d+2) must vanish
    n = 2 * d + 1
    s = sum((-1) ** (n - t) * comb(n, t) * v[1 + t] for t in range(n + 1))
    if s != 0:
        poly_ok = False
    # extrapolate p_d(2d+1) from j=1..2d+1 (degree 2d => Delta^{2d+1} p(2d+1)=0)
    pe = -sum((-1) ** (n - t) * comb(n, t) * v[t] for t in range(1, n + 1)) * (-1) ** n
    pdef = v[0] - (-1) ** (d + 1) * factorial(d + 1)
    if pe != pdef:
        extrap_ok = False
    p = [pe] + v[1:2 * d + 1]              # p_d(2d+1+j), j=0..2d
    # Newton coefficients at base 2d+1 via forward differences
    row = p[:]
    coef = []
    for i in range(2 * d + 1):
        coef.append(row[0])
        row = [row[t + 1] - row[t] for t in range(len(row) - 1)]
    nonpos = [i for i, c in enumerate(coef) if c <= 0]
    if nonpos:
        bad[d] = (nonpos, [coef[i] for i in nonpos])
        if first_bad is None:
            first_bad = d
    # base 2d+2 Newton coefficients must be positive (T4.2(3))
    row = v[1:2 * d + 2]
    c2 = []
    for i in range(2 * d + 1):
        c2.append(row[0])
        row = [row[t + 1] - row[t] for t in range(len(row) - 1)]
    if any(c <= 0 for c in c2):
        base2_ok = False
    if d == 2:
        print('d=2 base 2d+2 Newton coeffs:', c2, ' base 2d+1:', coef)

print('Delta^{2d+1} D(k,d) == 0 on k=2d+2..4d+3 for all 1<=d<=%d:' % DMAX, poly_ok)
print('extrapolated p_d(2d+1) == D(2d+1,d)-(-1)^{d+1}(d+1)! for all d<=%d:' % DMAX, extrap_ok)
print('base 2d+2 Newton coeffs all positive for d<=%d:' % DMAX, base2_ok)
print('first d with a nonpositive Newton coeff at base 2d+1:', first_bad)
for d in sorted(bad):
    idx, vals = bad[d]
    print('  d=%3d (%s) nonpositive indices %s  values %s' % (
        d, 'even' if d % 2 == 0 else 'odd', idx, ['%.3e' % float(x) for x in vals]))
even_bad = [d for d in bad if d % 2 == 0]
odd_bad = [d for d in bad if d % 2 == 1]
odd_idx0 = [d for d in bad if 0 in bad[d][0]]
print('even d with some nonpositive coeff:', even_bad)
print('odd d with some nonpositive coeff :', odd_bad)
print('d whose 0-th coeff is nonpositive  :', odd_idx0)
print('odd d in [69,%d] all have 0-th coeff negative:' % DMAX,
      all(d in bad and 0 in bad[d][0] for d in range(69, DMAX + 1, 2)))
print('elapsed %.1fs' % (time.time() - T0))
