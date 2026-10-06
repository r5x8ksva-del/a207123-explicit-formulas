# -*- coding: utf-8 -*-
"""s6-t342 / t0：高精度工具自检 + 计时。
  (1) exp/ln 在 100/300/600 位时的耗时；
  (2) π：Machin 与 Gauss–Legendre AGM 两种算法在 650 位上互相比对；
  (3) Γ：整数阶乘、Γ(1/2)^2=π、倍元公式、Γ(−λ) 的两种算法；
  (4) 积分：已知积分（Γ(5/2)、π²/6、π、e²−1）；
  (5) Prym 分解 Γ(−λ)=Σ(−1)^n/(n!(n−λ))+∫_1^∞τ^{−λ−1}e^{−τ}dτ 在 λ=6800/27（x=3/20 的 λ）和
      λ=100/729（x=9/10）上的高精度检验——这正是 K 的定义里 e^{−τ} 那一半，抵消最严重的情形；
  (6) φ_n 的两种精确算法（三项递推 vs 直接卷积）逐项比对。
"""
import sys, time, math
from decimal import Decimal as D, getcontext, localcontext
from fractions import Fraction as Fr
import os
sys.stdout.reconfigure(line_buffering=True)      # 被看门狗结束时也保留已输出的行
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hp


def lam_of(x):
    return (1 - x) / x ** 3


LAM_021 = lam_of(Fr(21, 100))       # = 790000/9261 ≈ 85.30

FAIL = 0


def check(name, ok, detail=""):
    global FAIL
    print(("PASS " if ok else "FAIL ") + name + ("  | " + detail if detail else ""))
    if not ok:
        FAIL += 1


def rel(a, b):
    return abs(a - b) / abs(b)


T0 = time.time()
# (1) 计时 -------------------------------------------------------------
for P in (100, 300, 600):
    getcontext().prec = P
    z = D(1) / D(7)
    t = time.time()
    for i in range(200):
        _ = (z + i).exp()
    te = (time.time() - t) / 200
    t = time.time()
    for i in range(200):
        _ = (z + i + 1).ln()
    tl = (time.time() - t) / 200
    print("timing prec=%d: exp %.3f ms, ln %.3f ms" % (P, te * 1e3, tl * 1e3))

# (2) π ---------------------------------------------------------------
getcontext().prec = 650
p1 = hp.pi_dec()
with localcontext() as ctx:
    ctx.prec = 680
    a, b, tt, pp = D(1), D(1) / D(2).sqrt(), D(1) / 4, D(1)
    for _ in range(12):
        an = (a + b) / 2
        b = (a * b).sqrt()
        tt -= pp * (a - an) ** 2
        a = an
        pp *= 2
    p2 = (a + b) ** 2 / (4 * tt)
check("pi Machin vs AGM (650 digits)", abs(p1 - p2) < D(10) ** -645, hp.sci(abs(p1 - p2), 3))
check("pi leading digits", str(p1).startswith("3.14159265358979323846264338327950288419716939937510"))

# (3) Γ ---------------------------------------------------------------
getcontext().prec = 80
ok = True
worst = D(0)
for n in range(1, 41):
    g = hp.gamma_pos(n)
    r = rel(g, D(math.factorial(n - 1)))
    worst = max(worst, r)
check("Gamma(n)=(n-1)!, n=1..40", worst < D(10) ** -75, "max rel " + hp.sci(worst, 3))
g = hp.gamma_pos(Fr(1, 2))
check("Gamma(1/2)^2 = pi", rel(g * g, hp.pi_dec()) < D(10) ** -75, hp.sci(rel(g * g, hp.pi_dec()), 3))
for z in (Fr(7, 3), Fr(100, 729), Fr(6800, 27), Fr(1, 1000)):
    zz = hp.dec(z)
    lhs = hp.gamma_pos(z) * hp.gamma_pos(z + Fr(1, 2))
    rhs = (D(2) ** (1 - 2 * zz)) * hp.pi_dec().sqrt() * hp.gamma_pos(2 * z)
    check("duplication formula z=%s" % z, rel(lhs, rhs) < D(10) ** -74, hp.sci(rel(lhs, rhs), 3))
for lam in (Fr(100, 729), Fr(25, 64), Fr(7, 3) + Fr(1, 3) / 7, Fr(700, 27), Fr(6800, 27), LAM_021):
    g1 = hp.gamma_neg_frac(lam)
    g2 = hp.gamma_neg_frac_rec(lam)
    check("Gamma(-lam) reflection vs recursion, lam=%.6f" % float(lam), rel(g1, g2) < D(10) ** -74,
          "Gamma(-lam)=%s rel %s" % (hp.sci(g1, 15), hp.sci(rel(g1, g2), 3)))

# (4) 已知积分 ----------------------------------------------------------
for P in (100, 600):
    getcontext().prec = P + 20
    t = time.time()
    q, e, info = hp.de_exp_quad(lambda v: v * v.sqrt() * (-v).exp(), P)
    exact = D(3) / 4 * hp.pi_dec().sqrt()
    check("de_exp_quad Gamma(5/2) @%d" % P, rel(q, exact) < D(10) ** -(P - 2),
          "rel %s est %s %s %.1fs" % (hp.sci(rel(q, exact), 3), hp.sci(e, 3), info, time.time() - t))
getcontext().prec = 120
q, e, info = hp.de_exp_quad(lambda v: v / (v.exp() - 1) if v > D(10) ** -100 else D(1) - v / 2, 100)
exact = hp.pi_dec() ** 2 / 6
check("de_exp_quad pi^2/6 @100", rel(q, exact) < D(10) ** -98, "rel %s %s" % (hp.sci(rel(q, exact), 3), info))
q, e, info = hp.ts_quad(lambda u: 4 / (1 + u * u), D(0), D(1), 100)
check("ts_quad pi @100", rel(q, hp.pi_dec()) < D(10) ** -98, "rel %s %s" % (hp.sci(rel(q, hp.pi_dec()), 3), info))
q, e, info = hp.ts_quad_composite(lambda u: u.exp(), D(0), D(2), 100, piece=D('0.5'))
exact = D(2).exp() - 1
check("ts_quad_composite e^2-1 @100", rel(q, exact) < D(10) ** -98, "rel %s %s" % (hp.sci(rel(q, exact), 3), info))


# (5) Prym 分解 ---------------------------------------------------------
def prym_check(lam, extra_digits=60):
    """返回 (Prym 和, Γ(−λ), 相对偏差, 用的精度)。"""
    lam = Fr(lam)
    getcontext().prec = 60
    g_low = hp.gamma_neg_frac(lam)
    cancel = max(0, -int(hp.log10_abs(g_low)))       # 两块各约 O(1)，结果约 |Γ(−λ)|
    P = cancel + extra_digits
    getcontext().prec = P + 20
    # 级数：精确有理部分和 + 尾项界
    S = Fr(0)
    n = 0
    fact = 1
    while True:
        if n > 0:
            fact *= n
        S += Fr((-1) ** n, fact) / (n - lam)
        # 尾项 ≤ Σ_{m>n} 1/(m!·|m−λ|) ≤ 2/((n+1)!·dist)
        if n > lam + 2 and hp.dec(Fr(2, fact * (n + 1))) < D(10) ** -(P + 10):
            break
        n += 1
    lamd = hp.dec(lam)
    f = lambda v: (-(lamd + 1) * (1 + v).ln() - 1 - v).exp()
    q, e, info = hp.de_exp_quad(f, P + 5)
    tot = hp.dec(S) + q
    getcontext().prec = 70
    g = hp.gamma_neg_frac(lam)
    return tot, g, rel(tot, g), P, n, e, info


PRYM_LAMS = [Fr(100, 729), LAM_021]          # x=3/20（λ=6800/27，约 557 位）放在 t0b_prym_high.py 单独跑
for lam in PRYM_LAMS:
    t = time.time()
    tot, g, r, P, n, e, info = prym_check(lam)
    check("Prym decomposition lam=%.6f (prec %d, %d series terms)" % (float(lam), P, n),
          r < D(10) ** -55, "Gamma(-lam)=%s rel dev %s quad-est %s %s %.1fs" %
          (hp.sci(g, 12), hp.sci(r, 3), hp.sci(e, 3), info, time.time() - t))


# (6) φ_n 两种精确算法 ----------------------------------------------------
def phi_coeffs_rec(x, N):
    x3 = x ** 3
    x6 = x3 * x3
    c = [Fr(0)] * (N + 1)
    phi = [Fr(0)] * (N + 1)
    fact = 1
    for n in range(N + 1):
        if n > 0:
            fact *= n
        d = Fr((-1) ** (n - 1), math.factorial(n - 1)) if n >= 1 else Fr(0)
        c[n] = d - (2 * x3 * c[n - 1] if n >= 1 else 0) - (x6 * c[n - 2] if n >= 2 else 0)
        phi[n] = Fr((-1) ** n, fact) - x ** 5 * c[n]
    return phi


def phi_coeffs_conv(x, N):
    out = []
    for n in range(N + 1):
        s = Fr(0)
        for j in range(n):            # τ·e^{−τ}·(1+x³τ)^{−2}：j 来自 e^{−τ}，k=n−1−j 来自 (1+x³τ)^{−2}
            k = n - 1 - j
            s += Fr((-1) ** j, math.factorial(j)) * (k + 1) * (-x ** 3) ** k
        out.append(Fr((-1) ** n, math.factorial(n)) - x ** 5 * s)
    return out


for x in (Fr(3, 20), Fr(9, 10), Fr(11, 20)):
    a = phi_coeffs_rec(x, 40)
    b = phi_coeffs_conv(x, 40)
    check("phi_n recurrence == convolution, x=%s, n<=40" % x, a == b)
check("phi_0=1, phi_1=-1-x^5 (x=3/20)", phi_coeffs_rec(Fr(3, 20), 2)[:2] == [1, -1 - Fr(3, 20) ** 5])

print("TOTAL FAIL = %d   elapsed %.1fs" % (FAIL, time.time() - T0))
sys.exit(1 if FAIL else 0)
