# -*- coding: utf-8 -*-
"""审计 a3-requirements（补充）：独立复算 T4.1 / T4.2(3) 中未进 verify_all 的范围断言。

- 「以 m=k-2d-1 表示时 d<=46 系数全正」「d=47 的 m^91 系数为首项的 -122153 倍」「d>=57 低次项也出现负号」
- 「奇数 d<=67 时 p_d(2d+1)>0，d=69 时 <0」
N 用三角递推（T1.4，已证明）算到 k=210，并在 k<=60 与原始定义 DP 的容斥值逐项对照。
"""
import os
import sys
from fractions import Fraction
from math import factorial

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))
import core  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

KMAX = 240
N = [[0] * (KMAX + 2) for _ in range(KMAX + 1)]
N[0][0] = 1
N[1][1] = 1
N[2][1], N[2][2] = 1, 2


def g(k, q):
    if k < 0 or q < 0 or q > KMAX + 1:
        return 0
    return N[k][q]


for k in range(3, KMAX + 1):
    for r in range(0, k):
        N[k][r + 1] = g(k - 1, r) + g(k - 1, r + 1) + r * (g(k - 3, r - 1) + 2 * g(k - 3, r) + g(k - 3, r + 1))

T = core.U_fast_table(60, 60)
ok_anchor = all(N[k][q] == core.N_from_U(T, k, q) for k in range(0, 61) for q in range(0, k + 1))
print('%s anchor 三角递推 N == 原始定义 DP 容斥 N（0<=q<=k<=60）' % ('PASS' if ok_anchor else 'FAIL'))


def D(k, d):
    q = k - d
    return N[k][q] if 0 <= q <= KMAX and 0 <= k <= KMAX else 0


def shifted_monomial_coeffs(d):
    """p_d(2d+1+m) 关于 m 的单项式系数（由 m=1..2d+1 处的值插值，即 k=2d+2..4d+2）。"""
    deg = 2 * d
    vals = [Fraction(D(2 * d + 1 + m, d)) for m in range(1, deg + 2)]
    # Newton 前向差分，基 C(m-1, i)
    diffs, cur = [], vals[:]
    while cur:
        diffs.append(cur[0])
        cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
    # sum_i diffs[i] * C(m-1, i) 转单项式
    poly = [Fraction(0)] * (deg + 1)
    basis = [Fraction(1)]                      # C(m-1, 0)
    for i in range(deg + 1):
        for j, c in enumerate(basis):
            poly[j] += diffs[i] * c
        # basis_{i+1} = basis_i * (m-1-i)/(i+1)
        nb = [Fraction(0)] * (len(basis) + 1)
        for j, c in enumerate(basis):
            nb[j + 1] += c / (i + 1)
            nb[j] += c * (-(1 + i)) / (i + 1)
        basis = nb
    # 额外点核对插值正确（k=4d+3..4d+6 仍在多项式区）
    for m in range(deg + 2, deg + 6):
        v = sum(c * m ** j for j, c in enumerate(poly))
        if v != D(2 * d + 1 + m, d):
            raise AssertionError('interpolation check failed d=%d' % d)
    return poly


neg = {}
lead_ratio_47 = None
for d in range(1, 58):
    if 4 * d + 6 + 1 > KMAX:
        break
    poly = shifted_monomial_coeffs(d)
    bad = [j for j, c in enumerate(poly) if c <= 0]
    if bad:
        neg[d] = bad
    if d == 47:
        lead_ratio_47 = poly[91] / poly[94]
first = min(neg) if neg else None
print('%s shiftpos d<=46 全正（第一个出现非正系数的 d=%s）；d=47 非正位置 %s，[m^91]/[m^94] = %s；d=57 非正位置 %s'
      % ('PASS' if first == 47 and lead_ratio_47 == -122153 else 'FAIL', first, neg.get(47), lead_ratio_47, neg.get(57)))
low57 = [j for j in neg.get(57, []) if j < 20]
print('%s d=57 低次项（j<20）出现非正：%s；d=48..56 的非正位置：%s'
      % ('PASS' if low57 else 'FAIL', low57, {d: neg[d] for d in range(48, 57) if d in neg}))

# Newton 基点 2d+1 的第 0 个系数 p_d(2d+1) = D(2d+1,d) - (-1)^{d+1}(d+1)!
res = {}
for d in range(1, 102, 2):
    if 2 * d + 1 > KMAX:
        break
    res[d] = D(2 * d + 1, d) - (-1) ** (d + 1) * factorial(d + 1) > 0
pos_upto = max(d for d in res if all(res[e] for e in res if e <= d))
fails = [d for d in res if not res[d]]
print('%s newton-2d1 奇数 d<=67 均为正：%s；d=69 为负：%s；失败的奇数 d（<=101）：%s'
      % ('PASS' if pos_upto == 67 and not res[69] else 'FAIL', pos_upto == 67, not res[69], fails))
