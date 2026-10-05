# -*- coding: utf-8 -*-
"""s7：把几条「猜想/已验证」推到更大的 d，尝试打破它们。
N 表用已证明（且 s1/s2 中对独立高度 DP 核对到 k<=150）的三角递推生成到 k<=2*DM+2；
p_d 用定理 2 的构造：p_d(k) = D(2d+2,d) + Σ_{j=2d+3}^k R_d(j)（在 2d+1 个点上累加后插值，再验证差分恒等式）。
检查（d<=DM）：C4-7（门槛下全例外）、C4-9（p_d(2d+1+m) 单项式系数全正）、C4-11（基点 2d+1 Newton 系数全正）、
C4-10（基点 2d+2 Newton 系数全正，数值）、缺陷闭式、次首项。
用法：py -3.14 s7_extend.py [DM]
"""
import sys, os, time
from fractions import Fraction
from math import factorial
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rlib import ptrim, padd, psub, pmul, pscale, peval, pshift, interp, newton_coeffs, dfact

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
DM = int(sys.argv[1]) if len(sys.argv) > 1 else 60
t0 = time.time()
KK = 2 * DM + 3
N = [[0] * (KK + 4) for _ in range(KK + 1)]
N[0][0] = 1
N[1][1] = 1
N[2][1], N[2][2] = 1, 2


def g(k, q):
    if k < 0 or q < 0 or q > k:
        return 0
    return N[k][q]


for k in range(3, KK + 1):
    for q in range(1, k + 1):
        N[k][q] = g(k - 1, q - 1) + g(k - 1, q) + (q - 1) * (g(k - 3, q - 2) + 2 * g(k - 3, q - 1) + g(k - 3, q))


def D(k, d):
    return g(k, k - d)


PD = {-3: [], -2: [], -1: []}
ok7, ok9, ok10, ok11, okE, ok8, okid = True, True, True, True, True, True, True
bad = []
for d in range(0, DM + 1):
    inner = padd(padd(pshift(PD[d - 1], -3), pscale(pshift(PD[d - 2], -3), 2)), pshift(PD[d - 3], -3))
    R = padd(pshift(PD[d - 1], -1), pmul([Fraction(-(d + 1)), Fraction(1)], inner))
    base = 2 * d + 2
    xs, ys = [base], [Fraction(D(base, d))]
    for t in range(1, 2 * d + 1):
        xs.append(base + t)
        ys.append(ys[-1] + peval(R, base + t))
    p = interp(xs, ys)
    if psub(p, pshift(p, -1)) != R:
        okid = False
    PD[d] = p
    if len(p) - 1 != 2 * d or p[-1] != Fraction(2, 2 ** d * factorial(d)):
        okid = False
    if d >= 1 and p[-2] != -(4 * d * d - 3 * d) * p[-1]:
        ok8 = False
    if D(2 * d + 1, d) - peval(p, 2 * d + 1) != (-1) ** (d + 1) * factorial(d + 1) or \
            D(2 * d, d) - peval(p, 2 * d) != Fraction((-1) ** (d + 1) * factorial(d + 2), 2):
        okE = False
    for k in range(d + 1, 2 * d + 2):
        if peval(p, k) == D(k, d):
            ok7 = False
            bad.append(('C4-7', d, k))
    ps = pshift(p, 2 * d + 1)
    if not all(c > 0 for c in ps):
        ok9 = False
        bad.append(('C4-9', d, [i for i, c in enumerate(ps) if c <= 0]))
    n2 = newton_coeffs(p, 2 * d + 2, 2 * d)
    if not all(c.denominator == 1 and c > 0 for c in n2) or n2[-1] != 2 * dfact(2 * d - 1):
        ok10 = False
    n1 = newton_coeffs(p, 2 * d + 1, 2 * d)
    if not all(c.denominator == 1 and c > 0 for c in n1):
        ok11 = False
        bad.append(('C4-11', d))
print(('OK  ' if okid else 'BAD ') + '定理 2 构造：差分恒等式、次数 2d、首项 2/(2^d d!)，d<=%d' % DM)
print(('OK  ' if okE else 'BAD ') + '缺陷闭式（2d+1 与 2d 处），d<=%d' % DM)
print(('OK  ' if ok8 else 'BAD ') + 'C4-8 次首项，d<=%d' % DM)
print(('OK  ' if ok7 else 'BAD ') + 'C4-7 门槛下 d+1<=k<=2d+1 全例外，d<=%d' % DM)
print(('OK  ' if ok9 else 'BAD ') + 'C4-9 p_d(2d+1+m) 单项式系数全正，d<=%d' % DM)
print(('OK  ' if ok10 else 'BAD ') + 'C4-10 基点 2d+2 Newton 系数全为正整数、末项 2(2d-1)!!，d<=%d' % DM)
print(('OK  ' if ok11 else 'BAD ') + 'C4-11 基点 2d+1 Newton 系数全为正整数，d<=%d' % DM)
print('   counterexamples:', bad[:10])
# 最小比值：D(2d+1,d)/(d+1)!（奇数 d）
rat = [(d, D(2 * d + 1, d) // factorial(d + 1)) for d in range(1, DM + 1, 2)]
print('   floor(D(2d+1,d)/(d+1)!) (odd d) first/last:', rat[:4], [(d, len(str(r))) for d, r in rat[-2:]], '(last: number of digits)')
print('SUMMARY s7 ok=%d bad=%d runtime=%.1fs' % (sum([okid, okE, ok8, ok7, ok9, ok10, ok11]),
                                                7 - sum([okid, okE, ok8, ok7, ok9, ok10, ok11]), time.time() - t0))
