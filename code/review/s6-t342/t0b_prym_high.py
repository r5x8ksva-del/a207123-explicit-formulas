# -*- coding: utf-8 -*-
"""s6-t342 / t0b：Prym 分解在 λ=6800/27（即 x=3/20）上的高精度检验（约 557 位）。

    Γ(−λ) = Σ_{n≥0} (−1)^n/(n!(n−λ)) + ∫_1^∞ τ^{−λ−1} e^{−τ} dτ        (λ>0 非整数)

这是 K(x) 定义里 e^{−τ} 那一半（K 的另一半带因子 x^5）。两块各约 1.5e−3，
结果约 1e−496，要抵消约 494 位。这一项先单独检验积分程序和 Γ 程序在最严重的抵消下是否可靠。
"""
import sys, os, time
sys.stdout.reconfigure(line_buffering=True)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import Decimal as D, getcontext
from fractions import Fraction as Fr
import hp

T0 = time.time()
lam = Fr(6800, 27)
getcontext().prec = 60
g_low = hp.gamma_neg_frac(lam)
cancel = max(0, -int(hp.log10_abs(g_low)))
P = cancel + 60
print("lam = 6800/27 = %.12f ; Gamma(-lam) ~ %s ; cancellation ~ %d digits ; working digits %d"
      % (float(lam), hp.sci(g_low, 10), cancel, P))
getcontext().prec = P + 20
S = Fr(0)
n = 0
fact = 1
while True:
    if n > 0:
        fact *= n
    S += Fr((-1) ** n, fact) / (n - lam)
    if n > lam + 2 and hp.dec(Fr(2, fact * (n + 1))) < D(10) ** -(P + 10):
        break
    n += 1
print("series: %d terms (exact rational), tail < 1e-%d ; value %s  (%.1fs)" % (n + 1, P + 10, hp.sci(hp.dec(S), 20), time.time() - T0))
lamd = hp.dec(lam)
f = lambda v: [(-(lamd + 1) * (1 + v).ln() - 1 - v).exp()]      # τ = 1+v
t = time.time()
qs, es, info = hp.de_exp_quad_vec(f, 1, P + 5, scale=1 / (lamd + 2))
q, e = qs[0], es[0]
print("integral: %s  est.err %s  %s  (%.1fs)" % (hp.sci(q, 20), hp.sci(e, 3), info, time.time() - t))
tot = hp.dec(S) + q
getcontext().prec = 80
g = hp.gamma_neg_frac(lam)
g2 = hp.gamma_neg_frac_rec(lam)
r = abs(tot - g) / abs(g)
print("Prym sum      = %s" % hp.sci(tot, 40))
print("Gamma(-lam)   = %s  (reflection)" % hp.sci(g, 40))
print("Gamma(-lam)   = %s  (recursion)" % hp.sci(g2, 40))
print("relative deviation = %s" % hp.sci(r, 3))
ok = r < D(10) ** -55
print(("PASS" if ok else "FAIL") + " Prym decomposition at lam=6800/27   elapsed %.1fs" % (time.time() - T0))
sys.exit(0 if ok else 1)
