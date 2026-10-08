# -*- coding: utf-8 -*-
"""s12-b5 复核 r2：引理 4.1（纤维 u=1/w 上的留数）。

分子 Num 由自写 DP 的计数得到：Num := P_{q-1}(x)·sum_{k<=3q-2} X(k,q)x^k 截断到 3q-2 次，并核对乘积在 3q-1..60 次的系数为 0
（X = N、N^c、N^E；q<=10；计数来自 r1 已核对的容斥表，k<=60）。
  r2-num      上述截断乘积的高次系数全为 0（即 F = Num/P_{q-1} 至少到 x^60 成立），且 deg Num_q=3q-2、首项 (q-1)!、最低项 2x^q
  r2-contour  数值围道积分（梯形公式，512 点）算出 F 在 b_w 每个根处的留数，乘 u'(η) 后与
              (-1)^(q-w)/(w^2 w!)·W(η)·Λ_{q,w}(η) 比较（W = W~_w、1、W~_w-1 分别对应 N、N^c、N^E），2<=q<=10，1<=w<=q-1，相对误差 <1e-9
  r2-exact    在 Q[x]/(b_w) 中精确：u'(x)·Num(x)/P'_{q-1}(x)（P' 是整个乘积的导数，不用引理 5 的化简）= 上式（w=1..7 含可约的 b_4）
  r2-uprime   u'/b_w' = -1/(w^2 x^3) 在 Q[x]/(b_w) 中成立（1<=w<=12）
  r2-psi      w=1：Ψ_q(ξ)>0，且 u'(ξ)Res_ξ F_q=(-1)^(q-1) ξ(1+ξ) Ψ_q（数值，2<=q<=10）
  r2-rev-*    反向：符号改成 (-1)^(q-w+1)、或 Λ 中 (M-w)! 改成 (M-w+1)!，围道积分结果应不符
"""
import os
import sys
import time
import cmath
from fractions import Fraction as Fr
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s12b5_common import (report, summary, ie_tables, pmul, ptrim, pderiv, peval, P_poly, Wtil_poly,  # noqa: E402
                          Cubic, roots_cubic_b, contour_residue)

t0 = time.time()
KI, QM = 60, 10
IN, INc, INE = ie_tables(KI, QM)
TABS = {'N': IN, 'Nc': INc, 'NE': INE}


def numerator(tab, q):
    P = P_poly(q - 1)
    F = [tab[k][q] for k in range(KI + 1)]
    prod = pmul(P, F)
    prod = prod + [0] * (KI + 1 - len(prod))
    deg = 3 * q - 2
    num = ptrim(prod[:deg + 1])
    tail_zero = all(prod[d] == 0 for d in range(deg + 1, KI + 1))
    return num, tail_zero


NUM = {}
ok = True
for kind, tab in TABS.items():
    for q in range(2, QM + 1):
        num, tz = numerator(tab, q)
        NUM[(kind, q)] = num
        if not tz:
            ok = False
            print('  tail nonzero', kind, q)
ok_shape = True
for q in range(2, QM + 1):
    num = NUM[('N', q)]
    if not (len(num) - 1 == 3 * q - 2 and num[-1] == factorial(q - 1) and num[q] == 2 and all(c == 0 for c in num[:q])):
        ok_shape = False
report(ok and ok_shape, 'r2-num', 'P_{q-1}·F 的 3q-1..60 次系数全为 0（N、N^c、N^E，2<=q<=10）；Num_q 次数 3q-2、首项 (q-1)!、最低项 2x^q')


def Lam(q, w, eta, fact_shift=0):
    return sum(comb(q, M + 1) * eta ** (-3 * (M + 1)) / factorial(M - w + fact_shift) for M in range(w, q))


def Wfun(kind, w, eta):
    Wt = peval(Wtil_poly(w), eta)
    return {'N': Wt, 'Nc': 1, 'NE': Wt - 1}[kind]


def uprime(x):
    return x * x * (3 - 2 * x) / (1 - x) ** 2


def closed(kind, q, w, eta, sgn_shift=0, fact_shift=0):
    return (-1) ** (q - w + sgn_shift) / (w * w * factorial(w)) * Wfun(kind, w, eta) * Lam(q, w, eta, fact_shift)


ALLROOTS = {v: roots_cubic_b(v) for v in range(0, QM + 1)}
ALLROOTS[0] = [1.0 + 0j]


def prod_b(m, z):
    r = 1
    for v in range(m + 1):
        r *= (1 - z - v * z ** 3)
    return r


def residues(kind, q, w):
    num = NUM[(kind, q)]
    P = P_poly(q - 1)
    others = [r for v in range(0, q) for r in ALLROOTS[v]]
    out = []
    for eta in ALLROOTS[w]:
        dmin = min(abs(eta - r) for r in others if abs(eta - r) > 1e-12)
        rad = 0.3 * dmin
        # 分母按乘积 ∏ b_v(z) 求值（展开后的 Horner 在根附近有严重抵消，只有约 1e-8 的相对精度）
        f = (lambda z, num=num, q=q: peval(num, z) / prod_b(q - 1, z))
        out.append((eta, contour_residue(f, eta, rad, 512)))
    return out


worst = 0.0
cnt = 0
RES = {}
for kind in ('N', 'Nc', 'NE'):
    for q in range(2, QM + 1):
        for w in range(1, q):
            for eta, res in residues(kind, q, w):
                RES[(kind, q, w, eta)] = res
                lhs = uprime(eta) * res
                rhs = closed(kind, q, w, eta)
                err = abs(lhs - rhs) / max(abs(rhs), 1e-300)
                if err > worst:
                    worst_case = (kind, q, w, eta)
                worst = max(worst, err)
                cnt += 1
print('  worst case', worst_case)
report(worst < 1e-9, 'r2-contour', '围道积分留数 × u\'(η) 与引理 4.1 的闭式一致：%d 个 (类型,q,w,根)，最大相对误差 %.2e' % (cnt, worst))

# 反向：符号、阶乘
def worst_with(**kw):
    wst = 0.0
    for (kind, q, w, eta), res in RES.items():
        lhs = uprime(eta) * res
        rhs = closed(kind, q, w, eta, **kw)
        wst = max(wst, abs(lhs - rhs) / max(abs(rhs), 1e-300))
    return wst


e1 = worst_with(sgn_shift=1)
e2 = worst_with(fact_shift=1)
report(e1 > 0.5, 'r2-rev-sign', '反向：符号改为 (-1)^(q-w+1) 后最大相对误差 %.2f（应很大）' % e1)
report(e2 > 0.01, 'r2-rev-fact', '反向：Λ 中 (M-w)! 改为 (M-w+1)! 后最大相对误差 %.2f（应很大）' % e2)


# ---------------------------------------------------------------- 精确：Q[x]/(b_w)
def kpoly(K, p):
    return K.red([Fr(c) for c in p])


ok = True
cnt = 0
for w in range(1, 8):
    K = Cubic([1, -1, 0, -w])
    x = [Fr(0), Fr(1), Fr(0)]
    xinv = K.inv(x)
    one_minus_x = [Fr(1), Fr(-1), Fr(0)]
    up = K.mul(K.mul(kpoly(K, [0, 0, 1]), kpoly(K, [3, -2])), K.inv(K.mul(one_minus_x, one_minus_x)))
    for q in range(w + 1, QM + 1):
        Pd = kpoly(K, pderiv(P_poly(q - 1)))
        Pdinv = K.inv(Pd)
        lamb = [Fr(0)] * 3
        for M in range(w, q):
            term = K.xpow(-3 * (M + 1))
            lamb = [a + Fr(comb(q, M + 1), factorial(M - w)) * b for a, b in zip(lamb, term)]
        Wt = kpoly(K, Wtil_poly(w))
        for kind in ('N', 'Nc', 'NE'):
            lhs = K.mul(K.mul(up, kpoly(K, NUM[(kind, q)])), Pdinv)
            Wk = {'N': Wt, 'Nc': [Fr(1), Fr(0), Fr(0)], 'NE': [Wt[0] - 1, Wt[1], Wt[2]]}[kind]
            const = Fr((-1) ** (q - w), w * w * factorial(w))
            rhs = [const * c for c in K.mul(Wk, lamb)]
            cnt += 1
            if lhs != rhs:
                ok = False
                print('  exact mismatch', kind, q, w)
report(ok, 'r2-exact', 'Q[x]/(b_w) 中 u\'·Num/P\'_{q-1} = (-1)^(q-w)/(w^2 w!)·W·Λ_{q,w}（%d 例，1<=w<=7 含 b_4 可约，w<q<=10）' % cnt)

ok = True
for w in range(1, 13):
    K = Cubic([1, -1, 0, -w])
    one_minus_x = [Fr(1), Fr(-1), Fr(0)]
    up = K.mul(K.mul(kpoly(K, [0, 0, 1]), kpoly(K, [3, -2])), K.inv(K.mul(one_minus_x, one_minus_x)))
    bd = kpoly(K, [-1, 0, -3 * w])
    lhs = K.mul(up, K.inv(bd))
    rhs = [Fr(-1, w * w) * c for c in K.xpow(-3)]
    if lhs != rhs:
        ok = False
report(ok, 'r2-uprime', "u'/b_w' = -1/(w^2 x^3) 在 Q[x]/(b_w) 中成立（1<=w<=12）")

# w=1 的特例与 Ψ_q>0
xi = [r for r in ALLROOTS[1] if abs(r.imag) < 1e-12][0].real
ok = True
for q in range(2, QM + 1):
    psi = sum(comb(q, n) * xi ** (-3 * n) / factorial(n - 2) for n in range(2, q + 1))
    if not psi > 0:
        ok = False
    res = RES[('N', q, 1, [r for r in ALLROOTS[1] if abs(r.imag) < 1e-12][0])]
    lhs = uprime(xi) * res
    rhs = (-1) ** (q - 1) * xi * (1 + xi) * psi
    if abs(lhs - rhs) > 1e-9 * abs(rhs):
        ok = False
report(ok, 'r2-psi', 'ξ≈%.6f：Ψ_q>0 且 u\'(ξ)Res_ξ F_q=(-1)^(q-1)ξ(1+ξ)Ψ_q（2<=q<=10，数值）' % xi)

print('time %.1fs' % (time.time() - t0))
sys.exit(1 if summary('r2') else 0)
