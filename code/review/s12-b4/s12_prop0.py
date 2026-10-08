# -*- coding: utf-8 -*-
"""复核 s12-b4：notes/12 命题 0 (a)(b)(c)(d)。
U 的真值来自 code/core.py；其余全部自写（见 s12_common.py）。"""
import random
import time
import cmath
from fractions import Fraction as Fr
from math import factorial

import numpy as np

from s12_common import (Checker, C, ff, U_core, P_poly, W_poly, Wt_poly, b_poly,
                        series_div, pmul, pderiv, pgcd, peval, system_status, exact_solve)

ck = Checker('s12_prop0')
t0 = time.time()
K, M = 40, 8
U = U_core(60, M)
Ucol = lambda m: [U[k][m] for k in range(61)]


def shape_system(f, alpha, beta, c, d, k0, K, s_lo, s_hi):
    """f(k)=Σ_{s_lo<=s<=s_hi} A(s) C(k+c-αs, βs+d)，k0<=k<=K。返回 (A,b,svals)。"""
    svals = list(range(s_lo, s_hi + 1))
    A = [[C(k + c - alpha * s, beta * s + d) for s in svals] for k in range(k0, K + 1)]
    b = [f[k] for k in range(k0, K + 1)]
    return A, b, svals


# ------------------------------------------------ (a) 三角形状：c=d=0、s_0=0 时一切 k>=0 可解且唯一
random.seed(20261008)
rnd = [random.randint(-50, 50) for _ in range(61)]
for (alpha, beta) in [(1, 0), (0, 1), (-1, 2), (-2, 3), (-3, 4), (-5, 6)]:
    for name, f in [('U1', Ucol(1)), ('U2', Ucol(2)), ('U3', Ucol(3)), ('rand', rnd)]:
        Kt = 30
        A, b, sv = shape_system(f, alpha, beta, 0, 0, 0, Kt, 0, Kt)
        # 下三角、对角线为 1（第 s 项在 k=s 首次出现，系数 C(βs,βs)=1）
        tri = all(A[k][k] == 1 for k in range(Kt + 1)) and \
            all(A[k][s] == 0 for k in range(Kt + 1) for s in range(Kt + 1) if k < s)
        ok, rank, sol = exact_solve(A, b)
        ck.check(f'P0a-tri ({alpha},{beta}) {name}', tri and ok and rank == Kt + 1,
                 f'c=d=0,s0=0,k<=30: unit-lower-triangular={tri}, solvable={ok}, rank={rank}')

# (a) 字面陈述「对一切 k>=0，c、d 任取，A 唯一」的反例
f = Ucol(1)
cases = [
    ((0, 1), -1, 0, 'k=0 时一切项 C(-1,s)=0，而 U_0(1)=1'),
    ((1, 0), 0, -1, 'd<0 时一切项为 0'),
    ((-1, 2), 0, 2, 'k=0 时一切项 C(s,2s+2)=0'),
    ((-2, 3), 0, 3, 'k=0 时一切项 C(2s,3s+3)=0'),
]
for (alpha, beta), c, d, why in cases:
    # 允许的 s：βs+d>=0；在 k<=K 内出现的 s：es+d-c<=K（e=α+β=1）
    s_lo = -(d // beta) if beta > 0 else -30
    if beta > 0 and (beta * s_lo + d) < 0:
        s_lo += 1
    s_hi = 30 - d + c
    A, b, sv = shape_system(f, alpha, beta, c, d, 0, 30, s_lo, s_hi)
    st = system_status(A, b)
    ck.check(f'P0a-literal-counterexample ({alpha},{beta}) c={c} d={d}', st.startswith('inconsistent'),
             f'k>=0 的方程组 {st}（{why}）——命题 0(a)「c、d 任取」字面不成立')
    # 修正后的说法：β>=1 时 c、d 任取但 k_0 取大些就可解
    if beta >= 1:
        k0 = max(0, d - c + 1, 1)
        A2, b2, _ = shape_system(f, alpha, beta, c, d, k0, 30, s_lo, s_hi)
        ok2, _, _ = exact_solve(A2, b2)
        ck.check(f'P0a-corrected ({alpha},{beta}) c={c} d={d} k0={k0}', ok2,
                 '修正说法：同一 (c,d) 在 k>=k_0 上可解')

# (a) 笔记修订版（01:00 UTC）的条件：「可用的最低项的 x-赋值不超过 0」⇔ β(c-d)+d>=0（β>=1）、d>=0（β=0）。
#     对 f(0)≠0、k_0=0，这个条件应当恰好刻画可解性（必要性：k=0 的方程需要某个 s 满足 βs+d>=0 且 s<=c-d）。
f2 = Ucol(2)
mism, mism_strict, cnt = [], 0, 0
for (alpha, beta) in [(1, 0), (0, 1), (-1, 2), (-2, 3), (-3, 4)]:
    for c in range(-3, 4):
        for d in range(-3, 4):
            Kt = 30
            s_lo = -(d // beta) if beta >= 1 else c - d - 5     # β=0 时 s 无下界限制，取一个够宽的窗口
            s_hi = Kt - d + c
            A, b, sv = shape_system(f2, alpha, beta, c, d, 0, Kt, s_lo, s_hi)
            if not sv:
                A = [[] for _ in b]
            solv = system_status(A, b) == 'consistent'
            pred = (beta * (c - d) + d >= 0) if beta >= 1 else (d >= 0)
            pred_strict = (beta * (c - d) + d > 0) if beta >= 1 else (d > 0)
            cnt += 1
            if solv != pred:
                mism.append((alpha, beta, c, d))
            if solv != pred_strict:
                mism_strict += 1
ck.check('P0a-new-condition', not mism,
         f'修订版命题 0(a) 的条件：{cnt} 组 (形状,c,d)（f=U_k(2)，k>=0）可解 ⇔ β(c-d)+d>=0（β=0 时 d>=0），无一例外'
         + (f'；不符 {mism[:5]}' if mism else ''))
ck.check('P0a-new-condition-reverse', mism_strict > 0, f'把条件改成严格不等号后有 {mism_strict} 组不符（核对确实敏感）')

# (a) 「A 唯一」也要 s_0 固定：(1,0)、c=3、d=0、s_0=0 时 k>=0 的方程组有 3 维核
A, b, sv = shape_system(Ucol(2), 1, 0, 3, 0, 0, 30, 0, 33)
ok, rank, _ = exact_solve(A, b)
ck.check('P0a-nonunique (1,0) c=3 d=0', ok and len(sv) - rank == 3,
         f'可解={ok}，未知数 {len(sv)}，秩 {rank}，核维数 {len(sv) - rank}（A(0..3) 只受其和约束）')

# ------------------------------------------------ (b) [x^k] x^r u^s = C(k-r-2s-1, s-1)
N = 45
okb = True
for r in range(3):
    for s in range(1, 15):
        num = [0] * (r + 3 * s) + [1]                      # x^{r+3s}
        den = [1]
        for _ in range(s):
            den = pmul(den, [1, -1])                      # (1-x)^s
        ser = series_div(num, den, N)
        for k in range(N + 1):
            if ser[k] != C(k - r - 2 * s - 1, s - 1):
                okb = False
ck.check('P0b-coef', okb, '[x^k]x^r u^s = C(k-r-2s-1,s-1)，r=0,1,2，1<=s<=14，k<=45')


def three_family(fvals, N):
    """把 F=Σ f(k)x^k 写成 Σ_r x^r a_r(u)（截断到 x^N），返回 A[r][s]（s>=0）。"""
    rem = [Fr(x) for x in fvals[:N + 1]]
    A = [[Fr(0)] * (N // 3 + 2) for _ in range(3)]
    for k in range(N + 1):
        cc = rem[k]
        if cc == 0:
            continue
        r, s = k % 3, k // 3
        A[r][s] = cc
        num = [0] * k + [1]
        den = [1]
        for _ in range(s):
            den = pmul(den, [1, -1])
        ser = series_div(num, den, N)
        for j in range(N + 1):
            rem[j] -= cc * ser[j]
    return A


for name, fv in [('U3', Ucol(3)), ('U8', Ucol(8)), ('rand', rnd)]:
    A3 = three_family(fv, N)
    good = True
    for k in range(N + 1):
        val = sum(A3[r][s] * C(k - r - 2 * s - 1, s - 1) for r in range(3) for s in range(1, N // 3 + 2))
        val += sum(A3[r][0] for r in range(3) if k == r)        # s=0 项：有限支撑修正
        if val != fv[k]:
            good = False
    ck.check(f'P0b-3family {name}', good, f'三族 u 型和 + 有限修正逐项等于 f(k)，k<=45')

# ------------------------------------------------ (c) U_k(m)=Σ_i (-1)^{m-i}/(i!(m-i)!) w_i(k+3m)
okc = True
for m in range(0, M + 1):
    ws = [series_div(Wt_poly(i), b_poly(i), 30 + 3 * m) for i in range(m + 1)]
    for k in range(0, 31):
        val = sum(Fr((-1) ** (m - i), factorial(i) * factorial(m - i)) * ws[i][k + 3 * m] for i in range(m + 1))
        if val != U[k][m]:
            okc = False
ck.check('P0c-F4', okc, 'U_k(m)=Σ_i(-1)^{m-i}w_i(k+3m)/(i!(m-i)!)，w_i=[x^n]W̃_i/b_i，m<=8，k<=30（精确）')

# ------------------------------------------------ (d) Binet 型：P_m 无重根、gcd(W_m,P_m)=1、数值谱分解
oksf = True
for m in range(0, 9):
    P = P_poly(m)
    g1 = pgcd(P, pderiv(P))
    g2 = pgcd(W_poly(m), P)
    if len(g1) != 1 or len(g2) != 1:
        oksf = False
ck.check('P0d-squarefree-coprime', oksf, 'gcd(P_m,P_m\')=1 且 gcd(W_m,P_m)=1，m<=8（Q 上精确 Euclid）')

worst = 0.0
for m in range(1, 6):
    P = P_poly(m)
    W = W_poly(m)
    dP = pderiv(P)
    # P_m 的根 = {1} ∪ 各 b_v（v=1..m，三次）的根；逐个三次式求根再用 Newton 磨光，避免高次多项式求根的误差
    roots = [1.0 + 0j]
    for v in range(1, m + 1):
        for z in np.roots([-v, 0, -1, 1]):
            z = complex(z)
            for _ in range(8):
                z -= (1 - z - v * z ** 3) / (-1 - 3 * v * z * z)
            roots.append(z)
    kap = []
    for xr in roots:
        rho = 1 / xr
        R = complex(peval([complex(c) for c in W], xr)) / complex(peval([complex(c) for c in dP], xr))
        kap.append((-rho * R, rho))
    for k in range(0, 41):
        val = sum(kp * rho ** k for kp, rho in kap)
        rel = abs(val - U[k][m]) / U[k][m]
        worst = max(worst, rel)
ck.check('P0d-binet', worst < 1e-8, f'U_k(m)=Σ_ρ κ_ρ ρ^k（κ_ρ=-ρW_m(1/ρ)/P_m\'(1/ρ)），1<=m<=5，k<=40，最大相对误差 {worst:.2e}（双精度，数值佐证）')

print(f'time {time.time() - t0:.1f}s')
import sys
sys.exit(0 if ck.summary() else 1)
