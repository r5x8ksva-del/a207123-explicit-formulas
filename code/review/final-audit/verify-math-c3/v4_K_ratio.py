# -*- coding: utf-8 -*-
"""verify-math-c3 / v4：数值核对 K/Γ(−λ) = 1 + λ x^5 J(x)（r-c3a 命题 R1）落在 (1,2) 内、上界
(1−x)/(1+x²)²（λ≥1）或 (1−x)x²（λ<1）成立、x→0+ 时趋于 2；并复现 r-c3a 给出的 6 个数值。
J(x) = ∫_0^∞ w e^{−w} (1+x³w)^{λ−1} dw，用复合 Simpson（numpy，float64）计算——只是数值旁证。"""
import numpy as np

def J(x):
    lam = (1 - x) / x ** 3
    # 被积函数的指数部分：-w + (lam-1) log1p(x^3 w)；峰在 w ~ 1/(x+x^3) 附近（lam 大时）
    scale = 1.0 / (x + x ** 3) if lam >= 1 else 1.0
    W = 80.0 * max(scale, 1.0)
    n = 400001
    w = np.linspace(0.0, W, n)
    f = w * np.exp(-w + (lam - 1.0) * np.log1p(x ** 3 * w))
    h = W / (n - 1)
    return h / 3.0 * (f[0] + f[-1] + 4.0 * f[1:-1:2].sum() + 2.0 * f[2:-1:2].sum())

ref = {0.6: 1.195007, 0.4: 1.335900, 0.3: 1.428866, 0.21: 1.535091, 0.1: 1.717420, 0.05: 1.835941}
xs = [0.95, 0.9, 0.8, 0.7, 0.69, 0.6, 0.5, 0.4, 0.3, 0.21, 0.1, 0.05, 0.02, 0.01, 0.005]
allok = True
for x in xs:
    lam = (1 - x) / x ** 3
    r = 1.0 + lam * x ** 5 * J(x)
    ub = 1.0 + ((1 - x) / (1 + x * x) ** 2 if lam >= 1 else (1 - x) * x * x)
    ok = 1.0 < r < ub < 2.0
    allok &= ok
    extra = ''
    if x in ref:
        extra = '  r-c3a value %.6f  diff %.1e' % (ref[x], abs(r - ref[x]))
    print('x=%-6g lambda=%-12.5g K/Gamma=%.6f  upper=%.6f  1<r<upper<2: %s%s' % (x, lam, r, ub, ok, extra))
print('all inside (1, upper) with upper<2:', allok)
