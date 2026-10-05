# -*- coding: utf-8 -*-
"""verify-requirements / finding #3：独立重算 T5.1(5) 的数值（不导入 core / 报告的核对模块）。

U_k(m) 用原始任务说明第 1 节的参考实现 U_list（照抄）；rho_m 用 decimal 牛顿法求 y^3=y^2+m 的实根；
c_m 用 T5.1(3) 的第二个闭式 c_m = rho(rho^{3m+1}/m! - sum_{i<m} rho^{3i}/i!)/(3rho-2)；
theta_m = rho_{m-1}/rho_m，kappa_m = c_{m-1} rho_{m-1}^3 / c_m。
目的：确认 (5) 里的百分比只来自 decimal 数值计算（即这条是数值结论），并核对数字本身。
"""
import sys
from collections import defaultdict
from decimal import Decimal, getcontext
from math import factorial

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
getcontext().prec = 90


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def U_list(m, K):                  # 原始任务说明第 1 节的参考实现
    out = [1, m + 1]
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    out.append(sum(cnt.values()))
    for k in range(3, K + 1):
        new = defaultdict(int)
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] += v
        cnt = new
        out.append(sum(cnt.values()))
    return out


def rho(m):
    if m == 0:
        return Decimal(1)
    y = Decimal(2)
    for _ in range(200):
        f = y ** 3 - y ** 2 - m
        y = y - f / (3 * y ** 2 - 2 * y)
    return y


def cm(m):
    r = rho(m)
    if m == 0:
        return Decimal(1)
    s = sum(r ** (3 * i) / factorial(i) for i in range(m))
    return r * (r ** (3 * m + 1) / factorial(m) - s) / (3 * r - 2)


print('== finding #3: T5.1(5) numbers recomputed independently (decimal prec 90)')
for m in (1, 2, 3):
    U = [U_list(m, k)[k] for k in (40, 41)] if False else None
    col = [U_list(m, 41)[k] for k in range(42)]
    r, c = rho(m), cm(m)
    theta = rho(m - 1) / r
    kappa = cm(m - 1) * rho(m - 1) ** 3 / c
    ratio_err = Decimal(col[41]) / Decimal(col[40]) / r - 1
    pred = kappa * (1 - theta) * theta ** 40
    root_err = Decimal(col[40]) ** (Decimal(1) / 40) / r - 1
    lvl_err = Decimal(col[40]) / (c * r ** 40) - 1
    print('m=%d rho=%.10f c_m=%.10f | U41/U40 rel.err=%.4e (%.4f%%), theory kappa(1-theta)theta^40=%.4e, '
          'agreement %.2f%% | U40^(1/40) rel.err=%.4e (%.2f%%) | U40/(c rho^40)-1=%.4e (%.2f%%)'
          % (m, r, c, ratio_err, ratio_err * 100, pred, abs(ratio_err / pred - 1) * 100,
             root_err, root_err * 100, lvl_err, lvl_err * 100))
print('c_1 check vs (10+15rho+17rho^2)/31:', cm(1) - (10 + 15 * rho(1) + 17 * rho(1) ** 2) / 31)
