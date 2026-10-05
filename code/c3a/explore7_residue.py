# -*- coding: utf-8 -*-
"""探索 7：F_an(x,t)=sum_m t^m G_m(x) 在 x_i（1-x-i x^3 的正根）处的留数结构（数值核对）：
   Res_{x_i} G_m = Res_{x_i} G_i * (-x_i^{-3})^{m-i}/(m-i)!   (m >= i)
   => Res_{x_i} F_an(x,t) = Res_{x_i}G_i * t^i e^{-t/x_i^3}；并与 c_i（U_k(i) ~ c_i rho_i^k）比较：Res_{x_i}G_i = -c_i x_i。"""
from decimal import Decimal as D, getcontext
getcontext().prec = 80

def root(i):
    x = D('0.5')
    for _ in range(200):
        f = 1 - x - i * x ** 3
        fp = -1 - 3 * i * x ** 2
        x = x - f / fp
    return x

def G_list(x, M):
    G = D(1); out = []
    for m in range(M + 1):
        G = (G + m * x * x) / (1 - x - m * x ** 3)
        out.append(G)
    return out

for i in (1, 2, 3, 4):
    xi = root(i)
    d = D(10) ** -40
    Gp = G_list(xi + d, i + 6)
    Gm = G_list(xi - d, i + 6)
    res = [(Gp[m] * d - Gm[m] * d) / 2 for m in range(i + 7)]   # [(x-x_i)G_m] 在 x_i±d 的平均 = Res + O(d^2)
    Ri = res[i]
    worst = max(abs(res[m] - Ri * (-1 / xi ** 3) ** (m - i) / __import__('math').factorial(m - i)) / abs(res[m]) for m in range(i, i + 7))
    # c_i via U_k(i) ratio: U_k(i) ~ c_i rho^k ; compute from DP
    import sys, os
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from core import U_fast_column
    U = U_fast_column(i, 400)
    rho = 1 / xi
    ci_est = D(U[400]) / rho ** 400
    print('i=%d x_i=%.20f  Res G_i=%.20E  -c_i x_i(est from U_400)=%.20E  worst rel dev of residue law m=i..i+6: %.2E'
          % (i, xi, Ri, -ci_est * xi, worst))
