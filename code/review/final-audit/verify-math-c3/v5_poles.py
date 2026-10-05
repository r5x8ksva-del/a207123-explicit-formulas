# -*- coding: utf-8 -*-
"""verify-math-c3 / v5：在 λ 为整数的点（x_4=1/2 即 λ=4；x_18=1/3 即 λ=18）精确核对 G_m（m≥i）有非零留数，
所以 𝒮(x,t)=Σ t^m G_m(x) 在这些 x 处没有定义（T3.4 的前提需要 λ∉Z）。
G_m = W_m/P_m（T1.3(1)），b_i 在 x_i 处是单根；Res_{x_i} G_m = W_m(x_i) / (b_i'(x_i) ∏_{j≤m, j≠i} b_j(x_i))。
另用 x_i ± ε 的数值求值确认 (x−x_i)G_m(x) → 该留数（G_m 由递推直接计算，不经过闭式）。"""
from fractions import Fraction as Fr

def b(j, x):
    return 1 - x - j * x ** 3

def W(m, x):
    s = Fr(0)
    P = Fr(1)            # P_{j-1}
    for j in range(1, m + 1):
        P *= b(j - 1, x)
        s += j * P
    return 1 + x * x * s

def G_rec(m, x):
    g = Fr(1)
    for v in range(m + 1):
        g = (g + v * x * x) / b(v, x)
    return g

for (i, xi) in [(4, Fr(1, 2)), (18, Fr(1, 3))]:
    assert b(i, xi) == 0
    lam = (1 - xi) / xi ** 3
    db = -1 - 3 * i * xi ** 2
    res = {}
    for m in range(i, i + 6):
        prod = Fr(1)
        for j in range(m + 1):
            if j != i:
                prod *= b(j, xi)
        res[m] = W(m, xi) / (db * prod)
    law = all(res[m] == res[i] * (-1 / xi ** 3) ** (m - i) / __import__('math').factorial(m - i) for m in res)
    eps = Fr(1, 10 ** 12)
    num_ok = True
    for m in (i, i + 3):
        approx = eps * G_rec(m, xi + eps)
        num_ok &= abs(float(approx / res[m]) - 1) < 1e-6
    print('i=%d x_i=%s lambda=%s : Res G_m (m=i..i+5) nonzero: %s ; residue law Res G_m = Res G_i (-x_i^-3)^(m-i)/(m-i)!: %s ;'
          ' eps*G_m(x_i+eps) ~ Res: %s ; Res G_i = %s'
          % (i, xi, lam, all(r != 0 for r in res.values()), law, num_ok, res[i]))
