# -*- coding: utf-8 -*-
"""s11：解释 C4-9 为何对大 d 必然失败（补充性质，数据拟合 + 留出验证）。
r_j(d) := [m^{2d-j}] p_d(2d+1+m) / [m^{2d}] p_d(2d+1+m)。已证明 r_1(d)=5d（命题 2.6 的等价形式）。
对 j=2,3,4：用 d=j..j+2j+... 的值拟合关于 d 的多项式（次数 2j），在其余 d<=DM 上留出验证；
若验证通过，则报告该多项式与其首项符号：首项为负 ⇒ 对充分大的 d 该系数为负 ⇒ C4-9 对一切充分大的 d 失败。
p_d 用定理 2 的构造（三角递推基点 + 差分恒等式）。
"""
import sys, os, time
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rlib import padd, psub, pmul, pscale, peval, pshift, interp

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
DM = int(sys.argv[1]) if len(sys.argv) > 1 else 50
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
PD = {-3: [], -2: [], -1: []}
for d in range(0, DM + 1):
    inner = padd(padd(pshift(PD[d - 1], -3), pscale(pshift(PD[d - 2], -3), 2)), pshift(PD[d - 3], -3))
    R = padd(pshift(PD[d - 1], -1), pmul([Fraction(-(d + 1)), Fraction(1)], inner))
    base = 2 * d + 2
    xs, ys = [base], [Fraction(g(base, base - d))]
    for t in range(1, 2 * d + 1):
        xs.append(base + t)
        ys.append(ys[-1] + peval(R, base + t))
    PD[d] = interp(xs, ys)
SH = {d: pshift(PD[d], 2 * d + 1) for d in range(0, DM + 1)}


def r(j, d):
    ps = SH[d]
    return ps[2 * d - j] / ps[2 * d]


for j in (1, 2, 3, 4):
    deg = 2 * j
    d0 = j  # 需要 2d-j>=0
    fit_d = list(range(max(d0, 1), max(d0, 1) + deg + 1))
    poly = interp(fit_d, [r(j, d) for d in fit_d])
    hold = [d for d in range(max(d0, 1), DM + 1) if d not in fit_d]
    okh = all(peval(poly, d) == r(j, d) for d in hold)
    # 找最后一个非负的整数 d（若首项为负）
    sign_change = [d for d in range(max(d0, 1), 400) if peval(poly, d) <= 0]
    print('j=%d: r_j(d) = poly of degree %d (fit on d=%s..%s, held-out d<=%d agree: %s)' % (
        j, len(poly) - 1, fit_d[0], fit_d[-1], DM, okh))
    print('     coefficients (ascending in d): %s' % [str(c) for c in poly])
    print('     leading coefficient sign: %s ; first d>=%d with r_j(d)<=0: %s' % (
        '+' if poly[-1] > 0 else '-', max(d0, 1), sign_change[:3]))
print('runtime %.1fs' % (time.time() - t0))
