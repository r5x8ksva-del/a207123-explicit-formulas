# -*- coding: utf-8 -*-
"""s8：C4-9 反例的诊断与独立确认。
(1) 用三角递推 + 定理 2 构造得到 p_d（d<=DM），打印 d=44..DM 时 p_d(2d+1+m) 的非正单项式系数（精确 Fraction）。
(2) 若存在 N_K{K}.pkl（由 s1_build_N.py K 生成，K>=4d+2+margin），则对出现反例的 d 用「原始定义的高度 DP + 容斥」
    数据直接插值得到 p_d，独立重算这些系数。
(3) 打印 r_d := D(2d+1,d)/(d+1)!（奇数 d）的整数部分，观察 C4-11 归约条件的趋势。
用法：py -3.14 s8_c49_counterexample.py [DM] [K]
"""
import sys, os, time, pickle
from fractions import Fraction
from math import factorial
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rlib import padd, psub, pmul, pscale, peval, pshift, interp

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
DM = int(sys.argv[1]) if len(sys.argv) > 1 else 56
KP = int(sys.argv[2]) if len(sys.argv) > 2 else 0
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
for d in range(0, DM + 1):
    inner = padd(padd(pshift(PD[d - 1], -3), pscale(pshift(PD[d - 2], -3), 2)), pshift(PD[d - 3], -3))
    R = padd(pshift(PD[d - 1], -1), pmul([Fraction(-(d + 1)), Fraction(1)], inner))
    base = 2 * d + 2
    xs, ys = [base], [Fraction(D(base, d))]
    for t in range(1, 2 * d + 1):
        xs.append(base + t)
        ys.append(ys[-1] + peval(R, base + t))
    p = interp(xs, ys)
    assert psub(p, pshift(p, -1)) == R
    PD[d] = p

first_bad = None
for d in range(40, DM + 1):
    ps = pshift(PD[d], 2 * d + 1)
    lead = ps[-1]
    badidx = [i for i, c in enumerate(ps) if c <= 0]
    if badidx and first_bad is None:
        first_bad = d
    if badidx or d in (45, 46):
        show = []
        for i in sorted(set(badidx + [2 * d - 3, 2 * d - 2, 2 * d - 4])):
            c = ps[i]
            show.append('m^%d: %s (= %s x lead)' % (i, c, c / lead))
        print('d=%d: nonpositive m-coefficients at %s' % (d, badidx))
        for s in show:
            print('     ' + s)
print('first d with a nonpositive coefficient (from d>=40):', first_bad)
# 全范围扫描 d<40 是否有反例（与 s2/s7 一致应为无）
early = [d for d in range(0, 40) if not all(c > 0 for c in pshift(PD[d], 2 * d + 1))]
print('d<40 with nonpositive coefficient:', early)

# (2) 用原始定义数据独立重算
if KP:
    path = os.path.join(HERE, 'N_K%d.pkl' % KP)
    with open(path, 'rb') as fh:
        NI = pickle.load(fh)['N']

    def DI(k, d):
        q = k - d
        if k < 0 or q < 0 or q > k:
            return 0
        return NI[k][q]
    dmax_i = (KP - 2 - 4) // 4
    for d in range(44, min(DM, dmax_i) + 1):
        xs = list(range(2 * d + 2, 4 * d + 3))
        pi = interp(xs, [DI(k, d) for k in xs])
        extra = all(peval(pi, k) == DI(k, d) for k in range(4 * d + 3, KP + 1))
        same = (pi == PD[d])
        ps = pshift(pi, 2 * d + 1)
        badidx = [i for i, c in enumerate(ps) if c <= 0]
        print('independent (height-DP + incl-excl, K=%d) d=%d: extra points agree=%s, equals recurrence p_d=%s, nonpositive m-coeffs=%s'
              % (KP, d, extra, same, badidx))

# (3) C4-11 归约条件的趋势
rows = []
for d in range(1, DM + 1, 2):
    rows.append((d, D(2 * d + 1, d) // factorial(d + 1)))
print('floor(D(2d+1,d)/(d+1)!) for odd d:', rows)
print('runtime %.1fs' % (time.time() - t0))
