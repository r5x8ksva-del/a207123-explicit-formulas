# -*- coding: utf-8 -*-
"""s9：检验 C4-11（基点 2d+1 的 Newton 系数全为正整数）在大 d 处是否成立。
由已证明的定理 2：Δ^0 p_d(2d+1) = p_d(2d+1) = D(2d+1,d) - (-1)^{d+1}(d+1)!；奇数 d 时 = D(2d+1,d) - (d+1)!。
(a) 用三角递推（已证明，且对独立高度 DP 核对到 k<=150/200）求出全部奇数 d<=DM 中 D(2d+1,d) <= (d+1)! 的 d。
(b) 对第一个这样的 d*，用「原始定义」独立重算 D(2d*+1,d*)：自写高度 DP 求 U_{2d*+1}(m)（m<=d*）再容斥。
(c) 对 d*，用定理 2 的构造求出 p_{d*}（需要全部 p_d, d<=d*），直接计算基点 2d*+1 的全部 Newton 系数，报告负的那些；
    同时核对 p_{d*}(2d*+1) == D(2d*+1,d*) - (d*+1)!，以及 p_{d*} 在 2d*+2..2d*+6 处等于 D（门槛之上）。
用法：py -3.14 s9_c411_counterexample.py [DM]
"""
import sys, os, time
from fractions import Fraction
from math import factorial, comb
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rlib import padd, psub, pmul, pscale, peval, pshift, interp, newton_coeffs, U_column

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
DM = int(sys.argv[1]) if len(sys.argv) > 1 else 101
t0 = time.time()
KK = 2 * DM + 8
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


fails = [d for d in range(1, DM + 1, 2) if D(2 * d + 1, d) <= factorial(d + 1)]
print('(a) odd d<=%d with D(2d+1,d) <= (d+1)!: %s' % (DM, fails[:20]))
if not fails:
    print('no counterexample up to DM')
    sys.exit(0)
ds = fails[0]
print('    d*=%d: D(2d*+1,d*) = %d' % (ds, D(2 * ds + 1, ds)))
print('           (d*+1)!    = %d' % factorial(ds + 1))
print('    neighbouring odd d: ', [(d, D(2 * d + 1, d) - factorial(d + 1) > 0) for d in range(ds - 4, ds + 5, 2)])

# (b) 原始定义独立重算
k = 2 * ds + 1
q = ds + 1
Ucol = [U_column(m, k)[k] for m in range(0, q)]          # U_k(m), m=0..q-1
Nk = sum((-1) ** (q - i) * comb(q, i) * (Ucol[i - 1] if i >= 1 else 0) for i in range(0, q + 1))
print('(b) height-DP + incl-excl: N(%d,%d) = %d ; equals recurrence value: %s' % (k, q, Nk, Nk == D(k, ds)))
# 再对相邻的 d*-2（应仍为正）做同样的独立重算
k2, q2 = 2 * (ds - 2) + 1, ds - 1
U2 = [U_column(m, k2)[k2] for m in range(0, q2)]
N2 = sum((-1) ** (q2 - i) * comb(q2, i) * (U2[i - 1] if i >= 1 else 0) for i in range(0, q2 + 1))
print('    check d*-2=%d: N(%d,%d) == recurrence: %s ; > (d*-1)!: %s' % (ds - 2, k2, q2, N2 == D(k2, ds - 2), N2 > factorial(ds - 1)))

# (c) p_{d*} 的构造与基点 2d*+1 的 Newton 系数
PD = {-3: [], -2: [], -1: []}
for d in range(0, ds + 1):
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
p = PD[ds]
print('(c) p_{d*} built (deg %d); p(k)==D(k,d*) for k=2d*+2..2d*+8: %s' % (
    len(p) - 1, all(peval(p, kk) == D(kk, ds) for kk in range(2 * ds + 2, 2 * ds + 9))))
v = peval(p, 2 * ds + 1)
print('    p_{d*}(2d*+1) = %s ; equals D(2d*+1,d*) - (d*+1)!: %s ; negative: %s' % (
    v, v == D(2 * ds + 1, ds) - factorial(ds + 1), v < 0))
n1 = newton_coeffs(p, 2 * ds + 1, 2 * ds)
neg = [i for i, c in enumerate(n1) if c <= 0]
print('    Newton coefficients at base 2d*+1 that are <= 0: indices %s' % neg)
n2 = newton_coeffs(p, 2 * ds + 2, 2 * ds)
print('    (control) Newton coefficients at base 2d*+2 all positive: %s' % all(c > 0 for c in n2))
print('runtime %.1fs' % (time.time() - t0))
