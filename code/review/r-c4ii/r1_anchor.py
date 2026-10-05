# -*- coding: utf-8 -*-
"""r1：把 Num_q 锚定到原始定义（自写高度 DP + 容斥），并核对 C4-17/18/19/20 与表 7。
运行：py -3.14 r1_anchor.py
"""
import sys
import time
from math import comb
from rlib import *

sys.path.insert(0, CODE)
import core  # noqa: E402  只用于交叉对照

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
t0 = time.time()
L = Log('r1_anchor')

# ---- 0. 自写 DP 与朴素 DP、core 的三种实现、词暴力 互相对照
ok = True
for m in range(0, 8):
    a = U_column_mine(m, 14)
    b = U_column_naive(m, 14)
    c = core.U_fast_column(m, 14)
    d = core.U_list(m, 14)
    if not (a == b == c == d):
        ok = False
for k in range(1, 6):
    for m in range(0, 4):
        if U_column_mine(m, k)[k] != core.U_multichain(k, m):
            ok = False
L.check('r1-dp-cross', ok, '自写高度DP == 朴素逐a检查DP == core.U_fast_column == core.U_list (m<=7,k<=14)，且 == core.U_multichain (k<=5,m<=3)')

ok = True
for k in range(1, 8):
    br = words_brute(k, k)
    Ucols = [U_column_mine(m, k) for m in range(0, k)]
    N = N_table_from_U(Ucols, k, k)
    for q in range(0, k + 1):
        if N[k][q] != br.get(q, 0):
            ok = False
    nb = core.N_brute(k)
    for q in range(0, k + 1):
        if nb.get(q, 0) != br.get(q, 0):
            ok = False
L.check('r1-N-brute', ok, '容斥 N(k,q) == 自写按定义暴力枚举 {1..k}^k 的合法满射词 == core.N_brute，k<=7')

# ---- 1. 大表
K = 150
QM = 47                      # q<=47：deg Num_q = 3q-2 <= 139 < K
Ucols = [U_column_mine(m, K) for m in range(0, QM)]
L.out('# U 表完成 (k<=%d, m<=%d)  %.1fs' % (K, QM - 1, time.time() - t0))
N = N_table_from_U(Ucols, K, QM)
F = {q: [N[k][q] for k in range(K + 1)] for q in range(0, QM + 1)}
F[-1] = [0] * (K + 1)

# ---- 2. C4-17：b_{q-1}F_q = (x+2(q-1)x^3)F_{q-1} + (q-1)x^3 F_{q-2} + [q=2]x^2
ok = True
for q in range(1, QM + 1):
    lhs = mul_trunc(bpoly(q - 1), F[q], K + 1)
    r1 = mul_trunc([0, 1, 0, 2 * (q - 1)], F[q - 1], K + 1)
    r2 = mul_trunc([0, 0, 0, q - 1], F[q - 2], K + 1)
    rhs = [r1[i] + r2[i] + (1 if (q == 2 and i == 2) else 0) for i in range(K + 1)]
    if lhs != rhs:
        ok = False
        L.out('  C4-17 fail q=%d' % q)
L.check('r1-C4-17', ok, 'F_q 一阶递推（含 [q=2]x^2）对原始定义 DP 成立：1<=q<=%d，模 x^%d' % (QM, K + 1))

# ---- 3. C4-18/19：P_{q-1}F_q 是多项式且 == 三项递推；次数/首项/最低项
NumR = num_by_recurrence(QM)
ok = True
NumDP = {}
for q in range(1, QM + 1):
    pr = mul_trunc(Ppoly(q - 1), F[q], K + 1)
    dg = 3 * q - 2
    if any(pr[i] != 0 for i in range(dg + 1, K + 1)):
        ok = False
        L.out('  not polynomial q=%d' % q)
    NumDP[q] = tr(pr[:dg + 1])
    if NumDP[q] != NumR[q]:
        ok = False
        L.out('  recurrence mismatch q=%d' % q)
L.check('r1-C4-18', ok, 'P_{q-1}F_q（F 来自原始定义 DP，模 x^%d）在 x^{3q-1}..x^%d 全为 0，且 == 自写三项递推的 Num_q，1<=q<=%d' % (K + 1, K, QM))

ok = True
from math import factorial
for q in range(1, QM + 1):
    p = NumDP[q]
    if len(p) - 1 != 3 * q - 2 or p[-1] != factorial(q - 1):
        ok = False
    low = min(i for i, c in enumerate(p) if c)
    if q == 1:
        ok = ok and low == 1 and p[1] == 1
    else:
        ok = ok and low == q and p[q] == 2
L.check('r1-C4-19', ok, 'DP 锚定的 Num_q：deg=3q-2、首项 (q-1)!、最低项 2x^q (q>=2; q=1 为 x)，q<=%d' % QM)

# ---- 4. 表 7（c4.md §4.2）逐字核对
T7 = {
    1: {1: 1},
    2: {2: 2, 4: 1},
    3: {3: 2, 4: 2, 5: 7, 7: 2},
    4: {4: 2, 5: 8, 6: 13, 7: 15, 8: 29, 10: 6},
    5: {5: 2, 6: 16, 7: 29, 8: 99, 9: 81, 10: 104, 11: 146, 13: 24},
    6: {6: 2, 7: 26, 8: 79, 9: 284, 10: 341, 11: 1004, 12: 551, 13: 770, 14: 874, 16: 120},
    7: {7: 2, 8: 38, 9: 187, 10: 674, 11: 1649, 12: 3824, 13: 3911, 14: 10100, 15: 4180, 16: 6264, 17: 6084, 19: 720},
}
ok = True
for q, d in T7.items():
    p = [0] * (max(d) + 1)
    for e, c in d.items():
        p[e] = c
    if tr(p) != NumDP[q]:
        ok = False
        L.out('  table7 mismatch q=%d: %s' % (q, NumDP[q]))
L.check('r1-table7', ok, 'c4.md 表 7 (q<=7) == DP 锚定的 Num_q')

# ---- 5. W_m（C4-2 推论）与容斥式 C4-20
ok = True
for m in range(0, QM):
    G = Ucols[m]
    pr = mul_trunc(Ppoly(m), G, K + 1)
    if tr(pr) != W_poly(m):
        ok = False
        L.out('  W mismatch m=%d' % m)
L.check('r1-Wm', ok, 'P_m * sum_k U_k(m) x^k == W_m = 1 + x^2 sum_{j<=m} j P_{j-1}，m<=%d，模 x^%d（DP）' % (QM - 1, K + 1))

ok = True
Wc = {-1: [1]}
for m in range(0, QM):
    Wc[m] = W_poly(m)
for q in range(1, 41):
    tot = []
    for i in range(0, q + 1):
        prod = [1]
        for v in range(i, q):
            prod = mul(prod, bpoly(v))
        tot = add(tot, scl(mul(Wc[i - 1], prod), (-1) ** (q - i) * comb(q, i)))
    if tot != NumDP[q]:
        ok = False
        L.out('  IE mismatch q=%d' % q)
L.check('r1-C4-20', ok, '容斥式 Num_q = sum_i (-1)^{q-i}C(q,i)W_{i-1} prod_{v=i}^{q-1} b_v == DP 锚定的 Num_q，q<=40')

# 保存 DP 锚定的 Num 供后续脚本使用
import json
with open(os.path.join(HERE, 'numdp.json'), 'w') as f:
    json.dump({str(q): NumDP[q] for q in NumDP}, f)
L.out('# 已保存 numdp.json（q<=%d）' % QM)
L.close(t0)
