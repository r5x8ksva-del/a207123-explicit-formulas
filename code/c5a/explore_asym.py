# -*- coding: utf-8 -*-
"""c5a 探索 1：固定 m、k->oo 的渐近。
- rho_m：y^3 = y^2 + m 的实根（Decimal, 90 位）
- c_m 闭式：c_m = gt_m(rho)/(3 rho^2 - 2 rho)，gt_m(y) = y^(3m+2)/m! + sum_{i<m} (m-i) y^(3i)/i!
- 与高度 DP（core.U_fast_column，精确整数）对照：e_k = U_k/(c rho^k) - 1，局部衰减率 e_{k+1}/e_k
- 两项渐近：U_k(m) - c_m rho_m^k ~ -c_{m-1} rho_{m-1}^{k+3}
"""
import os, sys, time
from decimal import Decimal, getcontext
from fractions import Fraction
from math import factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_fast_column

getcontext().prec = 90


def rho(m):
    if m == 0:
        return Decimal(1)
    y = Decimal(m) ** (Decimal(1) / Decimal(3)) + Decimal('0.5')
    for _ in range(200):
        f = y * y * y - y * y - m
        fp = 3 * y * y - 2 * y
        y2 = y - f / fp
        if abs(y2 - y) < Decimal(10) ** (-85):
            y = y2
            break
        y = y2
    return y


def c_closed(m, r=None):
    if m == 0:
        return Decimal(1)
    if r is None:
        r = rho(m)
    s = r ** (3 * m + 2) / factorial(m)
    for i in range(m):
        s += (m - i) * r ** (3 * i) / factorial(i)
    return s / (3 * r * r - 2 * r)


def main():
    t0 = time.time()
    K = 60
    out = []
    rhos = [rho(m) for m in range(0, 20)]
    cs = [c_closed(m, rhos[m]) for m in range(0, 20)]
    for m in range(0, 10):
        out.append('m=%d rho=%s  c=%s' % (m, str(rhos[m])[:40], str(cs[m])[:40]))
    out.append('')
    for m in range(1, 9):
        U = U_fast_column(m, 400)
        r, c = rhos[m], cs[m]
        theta = rhos[m - 1] / r
        kappa = cs[m - 1] * rhos[m - 1] ** 3 / c
        e = [Decimal(U[k]) / (c * r ** k) - 1 for k in range(401)]
        out.append('--- m=%d  rho=%.12f  c_m=%.12f  theta=rho_{m-1}/rho_m=%.12f  kappa=c_{m-1}rho_{m-1}^3/c_m=%.6f' % (
            m, r, c, theta, kappa))
        for k in (10, 20, 30, 40, 50, 59, 60, 100, 200, 300, 399):
            rate = e[k + 1] / e[k] if k < 400 else None
            two = (Decimal(U[k]) - c * r ** k) / (-cs[m - 1] * rhos[m - 1] ** (k + 3))
            out.append('  k=%3d  e_k=% .6e  e_{k+1}/e_k=%.9f  (theory %.9f)  two-term ratio=%.9f' % (
                k, e[k], rate, theta, two))
    # 提示词「m=2,3 在 k=40 时相差 <0.4%」
    out.append('')
    for m in (1, 2, 3):
        U = U_fast_column(m, 41)
        r = rhos[m]
        ratio = Decimal(U[41]) / Decimal(U[40])
        root = Decimal(U[40]) ** (Decimal(1) / Decimal(40))
        out.append('m=%d: U41/U40=%.9f rel.err=%.3e ; U40^(1/40)=%.6f rel.err=%.3e ; U40/(c rho^40)-1=%.3e' % (
            m, ratio, ratio / r - 1, root, root / r - 1, Decimal(U[40]) / (cs[m] * r ** 40) - 1))
    # m=4 精确
    c4 = Fraction(2 ** 14, 24) + sum(Fraction((4 - i) * 8 ** i, factorial(i)) for i in range(4))
    c4 /= (3 * 4 - 2 * 2)
    out.append('c_4 exact = %s' % c4)
    c18 = Fraction(3 ** 56, factorial(18)) + sum(Fraction((18 - i) * 27 ** i, factorial(i)) for i in range(18))
    c18 /= (27 - 6)
    out.append('c_18 exact = %s  ~ %.15e' % (c18, c18.numerator / c18.denominator))
    out.append('elapsed %.1fs' % (time.time() - t0))
    print('\n'.join(out))


if __name__ == '__main__':
    main()
