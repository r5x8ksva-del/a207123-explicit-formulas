# -*- coding: utf-8 -*-
"""杂项：T4.2(2) 的 h* 负系数（小 d 抽查）、T5.2 的 B_d 恒等式、T5.2 C(m+1,·) 基展开的适用范围（final-audit math-c4c5）。"""
import time
from fractions import Fraction
from math import comb, factorial

from alib import say, check, N_tri, interp_newton, peval, ptrim, padd, pmul, pscale, write_log
from core import U_fast_table

t0 = time.time()
F = Fraction
NT = N_tri(120)


def D(k, d):
    q = k - d
    return NT[k][q] if 0 <= q <= k else 0


PD = {}
for d in range(0, 9):
    xs = list(range(2 * d + 2, 4 * d + 3))
    PD[d] = interp_newton(xs, [D(k, d) for k in xs])

# ---- T4.2(2)：p_d(K) = Σ_j h_j C(K+c-j,2d)，h_j = Σ_{i<=j}(-1)^i C(2d+1,i) p_d(s+j-i)，s=2d-c；总有 h_j<0
bad = []
for d in range(1, 6):
    p = PD[d]
    for c in range(-400, 401):
        s = 2 * d - c
        h = [sum((-1) ** i * comb(2 * d + 1, i) * peval(p, s + j - i) for i in range(j + 1)) for j in range(2 * d + 1)]
        # 展开核对（多项式二项式）在若干 K 上
        for K in (-7, 0, 3, 11, 25):
            val = 0
            for j in range(2 * d + 1):
                n_ = K + c - j
                bb = F(1)
                for r in range(2 * d):
                    bb *= (n_ - r)
                bb /= factorial(2 * d)
                val += h[j] * bb
            if val != peval(p, K):
                bad.append(('expand', d, c, K))
                break
        if min(h) >= 0:
            bad.append(('allnonneg', d, c))
check('T4.2.2-hstar', not bad, '1<=d<=5、整数 c∈[-400,400]：p_d 在基 C(K+c-j,2d)（j=0..2d）下的系数总有负的（并核对展开式本身）; bad=%s' % bad[:3])

# ---- T5.2：B_d(k)=(k-d)![m^{k-d}]U_k = Σ_e (-1)^{d-e} N(k,k-e) ẽ_{d-e}(k-e)
T = U_fast_table(32, 34)
UP = {k: interp_newton(list(range(k + 2)), [T[k][m] for m in range(k + 2)]) for k in range(0, 31)}


def esym(j, vals):
    e = [F(1)] + [F(0)] * j
    for v in vals:
        for t in range(j, 0, -1):
            e[t] += v * e[t - 1]
    return e[j]


def etilde(j, n):
    ff = 1
    for r in range(j):
        ff *= (n - r)
    if ff == 0:
        return None
    return esym(j, list(range(-1, n - 1))) / ff


bad = []
for d in range(0, 6):
    for k in range(max(d, 1), 31):
        lhs = factorial(k - d) * (UP[k][k - d] if k - d < len(UP[k]) else 0)
        rhs = 0
        okk = True
        for e in range(d + 1):
            n = k - e
            if n < 0:
                continue
            et = etilde(d - e, n)
            if et is None:
                # n^{下降 j}=0：此时 N(k,k-e) 也应为 0 或该项按多项式延拓；跳过并标记
                if NT[k][k - e] if 0 <= k - e <= k else 0:
                    okk = False
                continue
            rhs += (-1) ** (d - e) * (NT[k][k - e] if 0 <= k - e <= k else 0) * et
        if okk and lhs != rhs:
            bad.append((d, k))
check('T5.2-Bd', not bad, 'B_d(k)=(k-d)![m^{k-d}]U_k = Σ_e(-1)^{d-e}N(k,k-e)ẽ_{d-e}(k-e)（d<=5, d<=k<=30）; bad=%s' % bad[:4])

# ---- T5.2 末句：C(m+1,·) 基下 U_k=2C(m+1,k)+(k^2-k-4)C(m+1,k-1)+p_2(k)C(m+1,k-2)+… 的适用范围
p2 = PD[2]
info = []
for k in range(2, 9):
    c_k1 = NT[k][k - 1]
    c_k2 = NT[k][k - 2] if k >= 2 else 0
    info.append((k, c_k1, k * k - k - 4, c_k2, peval(p2, k)))
say('INFO k, N(k,k-1), k^2-k-4, N(k,k-2), p_2(k):', info)
ok = all(NT[k][k - 1] == k * k - k - 4 for k in range(4, 60)) and all(NT[k][k - 2] == peval(p2, k) for k in range(6, 60))
fails = [k for k in range(2, 6) if NT[k][k - 2] != peval(p2, k)] + [k for k in range(2, 4) if NT[k][k - 1] != k * k - k - 4]
check('T5.2-basis-range', ok and fails, '「U_k=2C(m+1,k)+(k^2-k-4)C(m+1,k-1)+p_2(k)C(m+1,k-2)+…」只在 k>=6 成立（k>=4 时前两项成立）；k<=5 处不成立的点：%s' % sorted(set(fails)))

# μ_k 的范围：(2/k!)(m+μ_k)^k 的 m^{k-1} 系数 = [m^{k-1}]U_k 当且仅当 k>=4（k=3 时不成立）
okmu = all(F(2, factorial(k)) * k * F(k * k - 2 * k - 1, 2) == UP[k][k - 1] for k in range(4, 31))
k3 = F(2, factorial(3)) * 3 * F(9 - 6 - 1, 2) == UP[3][2]
check('T5.2-mu-range', okmu and not k3, 'μ_k=(k^2-2k-1)/2 使 (2/k!)(m+μ_k)^k 与 U_k 前两项一致：k>=4 成立，k=3 不成立')

say('elapsed %.1fs' % (time.time() - t0))
write_log('final_audit_math-c4c5_s6.log')
