# -*- coding: utf-8 -*-
"""s12-b5 复核 r7：§5「骨架型双和搜索」的独立重跑与范围分析；定理 5(b) 规范化的补充观察。

骨架族：X(k,q)=sum_{s<=7, p<=2s+2} A(p,s)·C(q+e,p+f)·C(k+a s+b p+c, s+q+d)，1<=q<=k<=21 的 231 个方程。
  r7-sanity    N^c 的 R 式参数 (a,b,c,d,e,f)=(-2,1,-1,-1,0,0)：相容，系数矩阵秩 79/80（两个 31 位素数下相同）
  r7-search    自写（numpy 向量化、模两个 31 位素数）重跑全部 6×8×5×6=1440 组参数 × {N^E, N}：相容的个数（作者：0）；
               并统计「系数矩阵列满秩」的比例——只有列满秩时「模 p 不相容」才严格推出「在 Q 上不相容」
  r7-trunc     对每组参数求在 1<=q<=k<=21 内可能出现非零项的最大 s；>7 的参数组说明截断 s<=7 会漏掉真公式需要的项
  r7-syn       人造反例：形状 (-1,1,0,0,0,0) 下取 s<=12 的随机系数造一个「真」骨架型双和，s<=7 的检验判为不相容，
               s<=12 的检验判为相容——即该搜索的否定结论不覆盖 s 的范围随 k 增长超过 k/3 的形状
  r7-free      定理 5(b) 规范化的补充：不带 3(q-1) 平移时最高一项是 x^{-3i}W~_i（i=q-1）在 K_i 中的坐标；
               打印前几项、是否都是整数，并在 order<=2、degree<=4 内找多项式系数递推（只作观察）
"""
import os
import sys
import time
import random
from fractions import Fraction as Fr
from math import comb, factorial

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s12b5_common import report, summary, C, ie_tables, Cubic, Wtil_poly, consistent_exact  # noqa: E402

t0 = time.time()
K = 21
IN, INc, INE = ie_tables(K, K)
P1, P2 = 2147483647, 2147483629
SHAPES = ((-2, 1), (-2, 0), (-1, 1), (-1, 0), (-3, 1), (-2, 2))
EFS = ((0, 0), (1, 0), (-1, 0), (0, 1), (1, 1), (0, -1))
PTS = [(k, q) for k in range(1, K + 1) for q in range(1, k + 1)]


def vars_for(S):
    return [(p, s) for s in range(S + 1) for p in range(2 * s + 3)]


def matrix(a, b, c, d, e, f, S):
    vs = vars_for(S)
    return [[C(q + e, p + f) * C(k + a * s + b * p + c, s + q + d) for (p, s) in vs] for (k, q) in PTS], len(vs)


def rank_mod(Mint, P):
    A = np.array([[v % P for v in row] for row in Mint], dtype=np.int64)
    m, n = A.shape
    r = 0
    for c in range(n):
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0:
            continue
        piv = r + nz[0]
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        col = A[:, c].copy()
        col[r] = 0
        idx = np.nonzero(col)[0]
        if idx.size:
            A[idx] = (A[idx] - (col[idx, None] * A[r][None, :]) % P) % P
        r += 1
        if r == m:
            break
    return r


def test(M, n, y, P):
    rk = rank_mod(M, P)
    rk2 = rank_mod([row + [yy] for row, yy in zip(M, y)], P)
    return rk == rk2, rk


yNc = [INc[k][q] for (k, q) in PTS]
yNE = [INE[k][q] for (k, q) in PTS]
yN = [IN[k][q] for (k, q) in PTS]

M, n = matrix(-2, 1, -1, -1, 0, 0, 7)
r1 = test(M, n, yNc, P1)
r2 = test(M, n, yNc, P2)
report(r1 == r2 == (True, 79) and n == 80, 'r7-sanity', 'N^c 的 R 式参数：相容=%s，秩 %d/%d（两个素数下 %s、%s）' % (r1[0], r1[1], n, r1, r2))

# ---------------------------------------------------------------- 全量重跑
hits = []
fullrank = 0
nsets = 0
rk_hist = {}
for (a, b) in SHAPES:
    for c in range(-5, 3):
        for d in range(-3, 2):
            for (e, f) in EFS:
                M, n = matrix(a, b, c, d, e, f, 7)
                nsets += 1
                rkM = None
                for name, y in (('NE', yNE), ('N', yN)):
                    ok1, rk = test(M, n, y, P1)
                    ok2, rkb = test(M, n, y, P2)
                    rkM = rk
                    if ok1 or ok2:
                        hits.append((name, a, b, c, d, e, f, ok1, ok2))
                if rkM == n:
                    fullrank += 1
                rk_hist[n - rkM] = rk_hist.get(n - rkM, 0) + 1
report(not hits, 'r7-search', '%d 组参数 × {N^E, N}（共 %d 个检验）在两个素数下都不相容，命中 %s；系数矩阵列满秩的参数组 %d/%d，'
       '亏秩分布 {亏秩: 组数}=%s（%.0fs）' % (nsets, 2 * nsets, hits[:5], fullrank, nsets, dict(sorted(rk_hist.items())),
                                         time.time() - t0))

# ---------------------------------------------------------------- 截断范围
def term_possible(a, b, c, d, e, f, s, k, q):
    """是否存在 0<=p<=2s+2 使 C(q+e,p+f)·C(k+as+bp+c, s+q+d) != 0（b>=0）。"""
    plo, phi = max(0, -f), min(2 * s + 2, q + e - f)
    if plo > phi:
        return False
    R = s + q + d
    if R < 0:
        return False
    base = k + a * s + c
    # 需要 base + b p >= R（且 >=0，由 R>=0 推出）
    if b == 0:
        return base >= R
    return base + b * phi >= R


def max_s(a, b, c, d, e, f, smax=60):
    best = -1
    for s in range(smax + 1):
        if any(term_possible(a, b, c, d, e, f, s, k, q) for (k, q) in PTS):
            best = s
    return best


# 自检：O(1) 判定与逐项判定在一组参数上一致
def _slow(a, b, c, d, e, f, s, k, q):
    return any(C(q + e, p + f) and C(k + a * s + b * p + c, s + q + d) for p in range(2 * s + 3))


assert all(term_possible(a, b, c, d, e, f, s, k, q) == bool(_slow(a, b, c, d, e, f, s, k, q))
           for (a, b) in SHAPES for (c, d, e, f) in ((-5, -3, 1, 0), (2, 1, 0, -1), (0, 0, -1, 0), (-1, -1, 1, 1))
           for s in range(0, 12) for (k, q) in PTS[::7])


over = {}
for (a, b) in SHAPES:
    cnt = 0
    mx = 0
    for c in range(-5, 3):
        for d in range(-3, 2):
            for (e, f) in EFS:
                ms = max_s(a, b, c, d, e, f, 40)
                mx = max(mx, ms)
                if ms > 7:
                    cnt += 1
    over[(a, b)] = (cnt, mx)
report(True, 'r7-trunc', '（信息）每种 (a,b) 中「k<=21 内仍有非零项的最大 s」>7 的参数组数（共 240 组）与最大 s：%s' % over)

# ---------------------------------------------------------------- 人造反例
random.seed(7)
sh = (-1, 1, 0, 0, 0, 0)
A12 = {(p, s): random.randint(-5, 5) for (p, s) in vars_for(12)}
ysyn = []
for (k, q) in PTS:
    a, b, c, d, e, f = sh
    ysyn.append(sum(v * C(q + e, p + f) * C(k + a * s + b * p + c, s + q + d) for (p, s), v in A12.items()))
M7, n7 = matrix(*sh, 7)
M12, n12 = matrix(*sh, 12)
t7 = test(M7, n7, ysyn, P1)
t12 = test(M12, n12, ysyn, P1)
report((not t7[0]) and t12[0], 'r7-syn', '人造的 s<=12 骨架型双和（形状 (-1,1,0,0,0,0)）：s<=7 检验相容=%s，s<=12 检验相容=%s'
       % (t7[0], t12[0]))

# ---------------------------------------------------------------- 规范化补充
seqs = {0: [], 1: [], 2: []}
allint = True
for i in range(1, 31):
    Kc = Cubic([1, -1, 0, -i])
    co = Kc.mul(Kc.xpow(-3 * i), Kc.red([Fr(c) for c in Wtil_poly(i)]))
    for r in range(3):
        seqs[r].append(co[r])
        if co[r].denominator != 1:
            allint = False


def find_prec(seq, order, deg):
    """找 sum_{t=0}^{order} P_t(n) seq[n+t] = 0（P_t 次数<=deg）的非零解；返回是否存在（在全部可用 n 上）。"""
    unk = (order + 1) * (deg + 1)
    rows = []
    for nn in range(1, len(seq) - order + 1):     # n 从 1 开始（seq[0] 对应 i=1）
        row = []
        for t in range(order + 1):
            for j in range(deg + 1):
                row.append(Fr(nn) ** j * seq[nn - 1 + t])
        rows.append(row)
    if len(rows) <= unk + 3:
        return None
    # 齐次方程组的秩 < 未知数 ⇔ 有非零解
    okc, rk, _ = consistent_exact(rows, [0] * len(rows))
    return rk < unk


found = {}
for r in range(3):
    found[r] = [(o, dg) for o in (1, 2) for dg in range(0, 5) if find_prec(seqs[r], o, dg)]
report(True, 'r7-free', '（信息）不带 3(q-1) 时最高一项坐标（i=1..30）全为整数=%s；前 6 项 r=0: %s；r=1: %s；r=2: %s；'
       '在 order<=2、deg<=4 内找到的递推 %s' % (allint, [str(v) for v in seqs[0][:6]], [str(v) for v in seqs[1][:6]],
                                         [str(v) for v in seqs[2][:6]], found))

print('time %.1fs' % (time.time() - t0))
sys.exit(1 if summary('r7') else 0)
