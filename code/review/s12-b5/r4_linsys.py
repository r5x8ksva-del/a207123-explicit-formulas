# -*- coding: utf-8 -*-
"""s12-b5 复核 r4：截断线性方程组（Fraction 精确消元，判据是精确的「不相容」，不是模素数）。

(2,1) 形状：X(k,q)=sum_s A(s) C(k+c-2s, s+d) 对 k0<=k<=K 成立（未知数 A(s)，-d<=s<=floor((K+c-d)/3)，即全部可能出现的项）。
窗口：c∈[-8,8]，d∈[-5,5]，k0∈{1,4,10}，K=50（g=-2d-c-3 覆盖 [-21,15]）。
  r4-N21        N_q（q=2..5）：全部 561×4 个方程组不相容（定理 4 的有限窗口佐证）
  r4-Nc21       N^c_q（q=3..5）：全部不相容（命题 6(i)）
  r4-NE21       N^E_q（q=3..5）：全部不相容（命题 6(iii)）
  r4-pos        正对照：N_1 恰在 k0+c+2d>=0 的 (c,d,k0) 上相容（组合约定 C(负,0)=0）；N^c_2 恰在 g=-6、N^E_2 恰在 g=-1 的 (c,d) 上相容（与纤维 u=1 的留数元
                -ξ^{-6}、ξ^{5}·ξ^{-6} 推出的唯一 g 一致）；人造的真 (2,1) 和在其 (c0,d0) 上相容
  r4-5a         定理 5(a) 的窗口佐证：N_q（q=2,3,4）=sum_i γ(i) c_i(k+δ(i))，δ(i)∈[-3,8]，k∈[5,50] 全部不相容
  r4-w1         补充（不是作者的断言）：每个 i 只用一个 w_i 原子 N_q=sum_i γ(i) w_i(k+δ(i))，q=2 相容（δ(1)=3），q=3,4 在窗口内是否相容
"""
import os
import sys
import time
import random
from fractions import Fraction as Fr
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s12b5_common import report, summary, C, ie_tables, CI, w_atom  # noqa: E402

t0 = time.time()
KI = 60
IN, INc, INE = ie_tables(KI, 6)
K = 50


def elim_multi(rows, rhss):
    """rows: m×n，rhss: m×R。返回每个右端是否相容的列表（精确）。"""
    m = len(rows)
    n = len(rows[0]) if m else 0
    R = len(rhss[0])
    A = [[Fr(v) for v in rows[i]] + [Fr(v) for v in rhss[i]] for i in range(m)]
    r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [v / pv for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        r += 1
        if r == m:
            break
    return [all(A[i][n + j] == 0 for i in range(r, m)) for j in range(R)]


random.seed(20261008)
SYN_C, SYN_D = 1, -2
SYN_A = {s: random.randint(-9, 9) for s in range(-SYN_D, 25)}


def syn(k):
    return sum(a * C(k + SYN_C - 2 * s, s + SYN_D) for s, a in SYN_A.items())


TARGETS = []
for q in range(2, 6):
    TARGETS.append(('N', q, [IN[k][q] for k in range(KI + 1)]))
for q in range(3, 6):
    TARGETS.append(('Nc', q, [INc[k][q] for k in range(KI + 1)]))
for q in range(3, 6):
    TARGETS.append(('NE', q, [INE[k][q] for k in range(KI + 1)]))
TARGETS.append(('N', 1, [IN[k][1] for k in range(KI + 1)]))
TARGETS.append(('Nc', 2, [INc[k][2] for k in range(KI + 1)]))
TARGETS.append(('NE', 2, [INE[k][2] for k in range(KI + 1)]))
TARGETS.append(('syn', 0, [syn(k) for k in range(KI + 1)]))

cons = {(t[0], t[1]): [] for t in TARGETS}
nsys = 0
for c in range(-8, 9):
    for d in range(-5, 6):
        for k0 in (1, 4, 10):
            s_lo, s_hi = -d, (K + c - d) // 3
            svals = list(range(s_lo, s_hi + 1))
            ks = list(range(k0, K + 1))
            if svals:
                rows = [[C(k + c - 2 * s, s + d) for s in svals] for k in ks]
            else:
                rows = [[0] for k in ks]
            rhss = [[t[2][k] for t in TARGETS] for k in ks]
            res = elim_multi(rows, rhss)
            nsys += 1
            for t, okc in zip(TARGETS, res):
                if okc:
                    cons[(t[0], t[1])].append((c, d, k0))

print('  %d 组 (c,d,k0)，%.1fs' % (nsys, time.time() - t0), flush=True)
bad ={key: v for key, v in cons.items() if key[0] in ('N',) and key[1] >= 2 and v}
report(not bad, 'r4-N21', 'N_q（q=2..5）的 (2,1) 截断方程组在 %d 组 (c,d,k0) 上全部不相容（精确）' % nsys)
bad = {key: v for key, v in cons.items() if key[0] == 'Nc' and key[1] >= 3 and v}
report(not bad, 'r4-Nc21', 'N^c_q（q=3..5）全部不相容')
bad = {key: v for key, v in cons.items() if key[0] == 'NE' and key[1] >= 3 and v}
report(not bad, 'r4-NE21', 'N^E_q（q=3..5）全部不相容')

g_of = lambda cd: -2 * cd[1] - cd[0] - 3
# 常数列：s=-d 那一项 C(k+c+2d,0) 只在 k+c+2d>=0 时为 1（组合约定下 C(负数,0)=0），其余项的起始次数更高，
# 所以相容 ⇔ k0+c+2d>=0（与复核者 s10-b3 对 notes/06 对照组的更正同一现象）。
exp_n1 = [(c, d, k0) for c in range(-8, 9) for d in range(-5, 6) for k0 in (1, 4, 10) if k0 + c + 2 * d >= 0]
ok1 = sorted(cons[('N', 1)]) == sorted(exp_n1)
gs_c2 = sorted(set(g_of(t) for t in cons[('Nc', 2)]))
gs_e2 = sorted(set(g_of(t) for t in cons[('NE', 2)]))
exp_c2 = [(c, d, k0) for c in range(-8, 9) for d in range(-5, 6) for k0 in (1, 4, 10) if -2 * d - c - 3 == -6]
exp_e2 = [(c, d, k0) for c in range(-8, 9) for d in range(-5, 6) for k0 in (1, 4, 10) if -2 * d - c - 3 == -1]
ok2 = sorted(cons[('Nc', 2)]) == sorted(exp_c2)
ok3 = sorted(cons[('NE', 2)]) == sorted(exp_e2)
ok4 = all(t in cons[('syn', 0)] for t in [(SYN_C, SYN_D, k0) for k0 in (1, 4, 10)])
report(ok1 and ok2 and ok3 and ok4, 'r4-pos',
       '正对照：N_1 恰在 k0+c+2d>=0 的 %d/%d 组上相容；N^c_2 相容的 g=%s（%d 组，恰为窗口内 g=-6 的全部）；'
       'N^E_2 相容的 g=%s（%d 组，恰为 g=-1 的全部）；人造和在 (c0,d0)=(%d,%d) 相容'
       % (len(cons[('N', 1)]), nsys, gs_c2, len(cons[('Nc', 2)]), gs_e2, len(cons[('NE', 2)]), SYN_C, SYN_D))

# ---------------------------------------------------------------- 定理 5(a) 窗口
ci = CI(200)
KS = list(range(5, 51))
bad = 0
nsys5 = 0
for q in (2, 3, 4):
    rhs = [[IN[k][q]] for k in KS]
    for deltas in product(range(-3, 9), repeat=q - 1):
        rows = [[1] + [ci(i + 1, k + deltas[i]) for i in range(q - 1)] for k in KS]
        nsys5 += 1
        if elim_multi(rows, rhs)[0]:
            bad += 1
            print('  5a consistent', q, deltas)
report(bad == 0, 'r4-5a', '定理 5(a) 窗口：N_q（q=2,3,4）= γ0+sum_i γ(i)c_i(k+δ(i))，δ(i)∈[-3,8]，%d 个方程组全部不相容' % nsys5)

# ---------------------------------------------------------------- 补充：每个 i 一个 w_i 原子
found = {}
nsysw = 0
for q in (2, 3, 4):
    rhs = [[IN[k][q]] for k in KS]
    found[q] = []
    for deltas in product(range(-3, 9), repeat=q - 1):
        rows = [[1] + [w_atom(ci, i + 1, k + deltas[i]) for i in range(q - 1)] for k in KS]
        nsysw += 1
        if elim_multi(rows, rhs)[0]:
            found[q].append(deltas)
ok = found[2] == [(3,)]
report(ok, 'r4-w1', '补充：N_q=γ0+sum_i γ(i) w_i(k+δ(i))（δ(i)∈[-3,8]，%d 个方程组）相容的 δ：q=2 %s；q=3 %s；q=4 %s'
       % (nsysw, found[2], found[3][:6], found[4][:6]))

print('time %.1fs' % (time.time() - t0))
sys.exit(1 if summary('r4') else 0)
