# -*- coding: utf-8 -*-
"""r5：反转分子 e.g.f.（C4-29）的独立复核。
(a) 一阶 ODE：(1-z)^2 A' = (y^2 + e z) A + 1 + (y^2-1) z，e=y^3-y^2（复核者推出；核对模块用的二阶 ODE 是它的导数）。
(b) 闭式按「代值 + 次数界」核对：对每个 q<=Z，[z^q] 两边都是 y 的 <=3q-1 次多项式，
    在 3Z 个不同的 y 值上相等即推出多项式恒等。实现与核对模块完全不同（单变量级数、按 y 代值）。
"""
import sys
import time
from fractions import Fraction
from math import comb, factorial
from rlib import *

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
t0 = time.time()
L = Log('r5_egf')
QM = 200
Num = num_by_recurrence(QM)
R = {q: list(reversed(Num[q])) for q in range(1, QM + 1)}     # R_q(y)=y^{3q-2}Num_q(1/y)，升幂
R[0] = []
ee = [0, 0, -1, 1]                                            # e = y^3 - y^2

# ---- (a) 一阶 ODE 的系数形式：R_{n+1} - (2n+y^2)R_n - n(e-(n-1))R_{n-1} = [n=0] + (y^2-1)[n=1]
ok = True
for n in range(0, QM):
    lhs = sub(sub(R[n + 1], mul([2 * n, 0, 1], R[n])), scl(mul(add(ee, [-(n - 1)]), R[n - 1] if n >= 1 else []), n))
    want = [1] if n == 0 else ([-1, 0, 1] if n == 1 else [])
    if tr(lhs) != tr(want):
        ok = False
        L.out('  first-order ODE fails n=%d' % n)
L.check('r5-ode1', ok, '一阶 ODE (1-z)^2A\' = (y^2+(y^3-y^2)z)A + 1 + (y^2-1)z 对 A=sum R_q z^q/q! 逐项成立到 z^%d（R_q 来自 DP 锚定的递推）' % (QM - 1))

# 二阶 ODE（c4.md 的形式）作为一阶 ODE 的导数，也逐项核对：
# (1-z)^2A'' = (y^2-1) + (2(1-z)+y^2(1-z)+y^3 z)A' + eA
ok = True
for n in range(0, QM - 1):
    # [z^n/n!] 系数：A''->R_{n+2}，z A''->n R_{n+1}，z^2 A''->n(n-1)R_n；A'->R_{n+1}，zA'->nR_n；A->R_n
    lhs = add(sub(R[n + 2], scl(R[n + 1], 2 * n)), scl(R[n], n * (n - 1)))
    rhs = add(add(mul([2, 0, 1], R[n + 1]), scl(mul([-2, 0, -1, 1], R[n]), n)), mul(ee, R[n]))
    if n == 0:
        rhs = add(rhs, [-1, 0, 1])
    if tr(lhs) != tr(rhs):
        ok = False
        L.out('  second-order ODE fails n=%d' % n)
L.check('r5-ode2', ok, 'c4.md 的二阶 ODE 逐项成立到 z^%d' % (QM - 2))

# ---- (b) 闭式：按 y 代值
Z = 24


def closed_form_series(y, Z):
    y = Fraction(y)
    e = y ** 3 - y ** 2
    # Lam = (y-1)ln(1-z) + y z/(1-z)
    Lam = [Fraction(0)] + [-(y - 1) / n + y for n in range(1, Z + 1)]
    G = [y * y * c for c in Lam]
    Phi = [Fraction(0)] * (Z + 1)
    Phi[0] = Fraction(1)
    for n in range(1, Z + 1):
        Phi[n] = sum(k * G[k] * Phi[n - k] for k in range(1, n + 1)) / n
    # g_m = [w^m](1+w)^e e^{-y^3 w}，二项式系数用广义 C(e,i)
    Ce = [Fraction(1)]
    for i in range(1, Z + 1):
        Ce.append(Ce[-1] * (e - (i - 1)) / i)
    Ex = [(-y ** 3) ** k / factorial(k) for k in range(Z + 1)]
    g = [sum(Ce[i] * Ex[m - i] for i in range(m + 1)) for m in range(Z + 1)]
    # I = sum_m g_m/(m+1) w^{m+1}，[z^n] w^{k} = C(n-1,k-1)
    I = [Fraction(0)] + [sum(g[m] / (m + 1) * comb(n - 1, m) for m in range(0, n)) for n in range(1, Z + 1)]
    PhiI = [sum(Phi[a] * I[n - a] for a in range(n + 1)) for n in range(Z + 1)]
    A = [(y + 1) * (Phi[n] - (1 if n == 0 else 0)) / (y * y) - y * PhiI[n] for n in range(Z + 1)]
    return A


ys = list(range(1, 2 * Z + 1)) + [-k for k in range(1, Z // 2 + 1)] + [Fraction(1, k) for k in range(2, Z // 2 + 2)]
assert len(set(ys)) >= 3 * Z
ok = True
for y in ys:
    A = closed_form_series(y, Z)
    if A[0] != 0:
        ok = False
    for q in range(1, Z + 1):
        if A[q] != ev([Fraction(c) for c in R[q]], Fraction(y)) / factorial(q):
            ok = False
            L.out('  closed form mismatch y=%s q=%d' % (y, q))
            break
L.check('r5-closed', ok, '闭式 (y+1)(Phi-1)/y^2 - y Phi I 在 %d 个不同 y 值上逐项等于 sum R_q(y) z^q/q!（q<=%d）；[z^q] 两边 y-次数 <=3q-1<%d ⇒ 作为 Q[y][[z]] 恒等到 z^%d' % (len(set(ys)), Z, len(set(ys)), Z))

# ---- (c) 闭式直接满足一阶 ODE（逐个 y、级数层面）
ok = True
for y in (2, 3, Fraction(-5, 3), Fraction(7, 2)):
    A = closed_form_series(y, Z)
    yF = Fraction(y)
    e = yF ** 3 - yF ** 2
    Ap = [(n + 1) * A[n + 1] for n in range(Z)]
    for n in range(Z - 2):
        lhs = Ap[n] - 2 * (Ap[n - 1] if n >= 1 else 0) + (Ap[n - 2] if n >= 2 else 0)
        rhs = yF * yF * A[n] + e * (A[n - 1] if n >= 1 else 0) + (1 if n == 0 else 0) + ((yF * yF - 1) if n == 1 else 0)
        if lhs != rhs:
            ok = False
L.check('r5-closed-ode1', ok, '闭式（代 y=2,3,-5/3,7/2）直接满足一阶 ODE，逐项到 z^%d' % (Z - 3))

# ---- (d) 特例 y=1：A = e^{z/(1-z)} - 1，即 R_q(1)=A000262(q)
A1 = closed_form_series(1, Z)
a = [1, 1]
for n in range(2, Z + 1):
    a.append((2 * n - 1) * a[n - 1] - (n - 1) * (n - 2) * a[n - 2])
L.check('r5-y1', all(A1[q] * factorial(q) == a[q] for q in range(1, Z + 1)), 'y=1：闭式系数 * q! == A000262(q)，q<=%d' % Z)
L.close(t0)
