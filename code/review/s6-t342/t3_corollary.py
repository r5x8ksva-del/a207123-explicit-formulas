# -*- coding: utf-8 -*-
"""s6-t342 / t3：推论的数值扫描。R(x) := K/Γ(−λ) = 1 + λx^5 J(x) = 1 + (1−x)·x^2 J(x)。

  (a) 1 < R(x) < 2 − x：证明里的上界来自 J < 1/x^2（(1+x^3w)^{λ−1} < e^{(1−x)w}）。
  (b) λ ≥ 1（即 x^3 ≤ 1−x，x ≤ 0.6823）时的双边界（证明见报告 §3.4）：
        L(x) = 1 + (1−x)[1/(1+x^2)^2 − 3x/(1+x^2)^4]  ≤  R(x)  ≤  U(x) = 1 + (1−x)/(1+x^2)^2。
  (c) x→0+：R → 2；并看 (2−R)/x 的趋势（双边界给出 2−R ∈ [x+O(x^2), 4x+O(x^2)]）。
R 对一切 x∈(0,1) 都有定义（λ 是整数时 K 是极点，但比值的闭式仍有意义），扫描里不排除 x=1/n。
"""
import sys, os, time, math
sys.stdout.reconfigure(line_buffering=True)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import Decimal as D, getcontext
from fractions import Fraction as Fr
import hp

getcontext().prec = 60      # x 很小时 ln(1+x^3 w) 的自变量很小，多留位数
FAIL = 0
T0 = time.time()


def R_of(x):
    lam = (1 - x) / x ** 3
    x3 = hp.dec(x ** 3)
    lm1 = hp.dec(lam - 1)
    f = lambda w: [w * (-w + lm1 * (1 + x3 * w).ln()).exp()]
    (J,), (eJ,), info = hp.de_exp_quad_vec(f, 1, 35, scale=1 / hp.dec(x))
    return 1 + hp.dec(lam * x ** 5) * J, J, eJ / J, lam


xs = [Fr(k, 10000) for k in (5, 10, 20, 50)] + [Fr(k, 1000) for k in (13, 27)] + [Fr(k, 100) for k in range(1, 100)]
print("%-8s %-14s %-22s %-10s %-10s %-10s %-10s %s" % ("x", "lambda", "R=K/Gamma(-lam)", "2-x", "L(x)", "U(x)", "(2-R)/x", "checks"))
worst_gap_low = None
for x in xs:
    R, J, relerr, lam = R_of(x)
    xd = hp.dec(x)
    ok_a = (R > 1) and (R < 2 - xd) and (J < 1 / (xd * xd))
    s = 1 + xd * xd
    L = 1 + (1 - xd) * (1 / s ** 2 - 3 * xd / s ** 4)
    U = 1 + (1 - xd) / s ** 2
    if lam >= 1:
        ok_b = (L <= R <= U)
    else:
        ok_b = True
    ok = ok_a and ok_b and relerr < D(10) ** -30
    if not ok:
        FAIL += 1
    print("%-8s %-14.6g %-22s %-10.6f %-10s %-10s %-10.6f %s%s" % (
        float(x), float(lam), hp.sci(R, 16), float(2 - x),
        ("%.6f" % float(L)) if lam >= 1 else "-", ("%.6f" % float(U)) if lam >= 1 else "-",
        float((2 - R) / xd), "PASS" if ok else "FAIL", "" if lam.denominator != 1 else "  (lambda integer: K is a pole, ratio formula still defined)"))
print("SUMMARY t3: points=%d FAIL=%d elapsed %.1fs" % (len(xs), FAIL, time.time() - T0))
sys.exit(1 if FAIL else 0)
