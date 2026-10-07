# -*- coding: utf-8 -*-
"""s10-b3 检查 3：纤维上的代数论断（K=Q(xi) 中的精确运算 + 有理区间 + 浮点示意）。

F1 xi 的基本事实：X^3+X-1 无有理根；判别式 -31；N(xi)=1、Tr(xi)=0、N(1+xi)=3；
   W_m(xi)=xi+xi^2 且 P_m(xi)=0（1<=m<=20）。
F2 范数引理：xi^N 不是有理数（1<=|N|<=300）。反向：(xi^3+xi)^N=1 必须被判为有理数。
F3 纤维判据（核心）：对 α,β>=0、2<=α+β<=12 的全部 88 个形状，构造纤维多项式
      α>=1：F=x^{α+β}-xi^{α-2β}(1-x)^β；α=0：F=x^β-xi^{-2β}(1-x)^β（§4 的 y=x/(1-x) 纤维）。
   在 K[x] 中精确计算：F 的不同根个数 = deg F - deg gcd(F,F')；
   与 b_w（1<=w<=8）的公共根个数 = sum_w deg gcd(F,b_w)（b_w 两两互素且无重根）。
   预期：除 (2,1) 外，公共根个数 < 不同根个数（纤维上有点不是 P_8 的根，从而不是任一 P_m(m<=8) 的根）；
   (2,1) 恰好全部纤维点都是 b_1 的根（内置正对照）；另外每个形状都有 deg gcd(F,b_1)>=1（xi 在纤维上）。
F4 情形 (I) 的乘积关系（浮点示意）：α,β>=1、e≠0 时 prod (1-η)/η^3 = (-1)^{α+β+1} xi^{-3e}。
F5 情形 (IV)：a(β)=(1-xi)^β-(-xi)^β 在 K 中只在 β=1 时是有理数（β<=40）；
   有理区间：2 xi^3 < 0.64，xi^{-3}(xi^{-3}-1)^2 > 3.8^2；
   浮点：prod_ζ(xi^2+ζ)=xi^{2β}-(-1)^β、u(x_ζ)=ζ^3/(xi^2(xi^2+ζ)^2)、|a(xi_2)|>3.8>0.64>|a(xi)|（β 奇数 3..41）。
F6 反向检查：把 v_0 的指数故意改成 α-β（忘了 1-xi=xi^3 的化简），(2,1) 的正对照与「xi 在纤维上」必须报 FAIL。
"""
import sys
import cmath
from fractions import Fraction
from s10b3_common import (K, KZERO, KONE, XI, kadd, ksub, kmul, kneg, kscale, kpow, kinv, knorm, ktrace,
                          k_is_rational, keval_intpoly, kp_from_int, kp_trim, kp_add, kp_sub, kp_mul,
                          kp_scale, kp_gcd, kp_deriv, kp_pow, kp_deg, P_poly, W_poly, xi_interval, b_poly)

results = []


def report(tag, ok, info=""):
    results.append((tag, ok))
    print(("PASS " if ok else "FAIL ") + tag + ("  " + info if info else ""))


# ---------------------------------------------------------------- F1
ok = True
f = lambda t: t ** 3 + t - 1
ok &= f(1) != 0 and f(-1) != 0
disc = -4 * 1 ** 3 - 27 * (-1) ** 2
ok &= disc == -31
ok &= knorm(XI) == 1 and ktrace(XI) == 0 and knorm(kadd(KONE, XI)) == 3
for m in range(1, 21):
    if keval_intpoly(W_poly(m), XI) != K(0, 1, 1):
        ok = False
    if keval_intpoly(P_poly(m), XI) != KZERO:
        ok = False
report("F1 basic facts on xi (min poly, disc -31, N=1, N(1+xi)=3, W_m(xi)=xi+xi^2, P_m(xi)=0 for m<=20)", ok)

# ---------------------------------------------------------------- F2
ok = True
p = KONE
for N in range(1, 301):
    p = kmul(p, XI)
    if k_is_rational(p) or k_is_rational(kinv(p)):
        ok = False
# 反向：(xi^3+xi)=1，幂必为有理数
z = kadd(kpow(XI, 3), XI)
rev_ok = all(k_is_rational(kpow(z, N)) for N in range(-5, 6))
report("F2 xi^N not rational for 1<=|N|<=300 (reverse: (xi^3+xi)^N detected rational: %s)" % rev_ok, ok and rev_ok)


# ---------------------------------------------------------------- F3
import os
CORRUPT = os.environ.get("S10B3_CORRUPT", "")  # 反向检查用：=exp 时把 v_0 的指数改成 α-β（故意改坏）


def fiber_poly(alpha, beta, exp_override=None):
    """α>=1：x^{α+β}-xi^{e}(1-x)^β，e=α-2β；α=0：x^β-xi^{-2β}(1-x)^β。"""
    onemx = kp_from_int([1, -1])
    if CORRUPT == "exp" and exp_override is None:
        exp_override = alpha - beta
    if alpha >= 1:
        e = alpha - 2 * beta if exp_override is None else exp_override
        c = kpow(XI, e)
        Fp = [KZERO] * (alpha + beta) + [KONE]
        return kp_sub(Fp, kp_scale(kp_pow(onemx, beta), c)), e
    else:
        e = -2 * beta if exp_override is None else exp_override
        c = kpow(XI, e)
        Fp = [KZERO] * beta + [KONE]
        return kp_sub(Fp, kp_scale(kp_pow(onemx, beta), c)), e


def fiber_test(alpha, beta, W=8, exp_override=None):
    Fp, e = fiber_poly(alpha, beta, exp_override)
    deg = kp_deg(Fp)
    g = kp_gcd(Fp, kp_deriv(Fp))
    ndistinct = deg - kp_deg(g)
    common = []
    for w in range(1, W + 1):
        common.append(kp_deg(kp_gcd(Fp, kp_from_int(b_poly(w)))))
    return deg, ndistinct, common


shapes = [(a, n - a) for n in range(2, 13) for a in range(0, n + 1)]
ok_all = True
ok_xi = True
not_excluded = []
lines = []
sqfree_flags = []
for (al, be) in shapes:
    deg, nd, common = fiber_test(al, be)
    sqfree_flags.append(deg == nd)
    tot = sum(common)
    excluded = tot < nd
    if common[0] < 1:
        ok_xi = False
    if not excluded:
        not_excluded.append((al, be))
    lines.append("  (%d,%d): deg F=%d distinct=%d common-with-b_w(w=1..8)=%s %s" % (
        al, be, deg, nd, common, "excluded" if excluded else "NOT excluded"))
for ln in lines:
    print(ln)
ok_f3 = (not_excluded == [(2, 1)]) and ok_xi
report("F3 fibre criterion exact in K[x]: only (2,1) not excluded among %d shapes; xi on every fibre" % len(shapes), ok_f3,
       "not_excluded=%s" % not_excluded)

# 同时记录：所有 F 都无重根（与我的手算一致：重根只能在 x=(α+β)/α，此处 v 取有理值）
report("F3b every fibre polynomial is squarefree (all %d shapes)" % len(shapes), all(sqfree_flags))

# ---------------------------------------------------------------- F4（浮点示意）
try:
    import numpy as np
    have_np = True
except Exception:
    have_np = False

xi_f = None
lo, hi = xi_interval(200)
xi_f = float((lo + hi) / 2)
ok = True
worst = 0.0
if have_np:
    for (al, be) in shapes:
        if al >= 1 and be >= 1 and al != 2 * be:
            e = al - 2 * be
            n = al + be
            # F 的系数（高到低）
            coeffs = [0.0] * (n + 1)
            coeffs[0] = 1.0
            # -(xi^e)(1-x)^β
            from math import comb
            for j in range(be + 1):
                # (1-x)^β 的 x^j 系数 (-1)^j C(β,j)，放在高到低的位置 n-j
                coeffs[n - j] -= (xi_f ** e) * ((-1) ** j) * comb(be, j)
            roots = np.roots(coeffs)
            prod = 1.0 + 0j
            for r in roots:
                prod *= (1 - r) / r ** 3
            target = (-1) ** (n + 1) * xi_f ** (-3 * e)
            rel = abs(prod - target) / abs(target)
            worst = max(worst, rel)
            if rel > 1e-6:
                ok = False
                print("  product mismatch (%d,%d): %s vs %s" % (al, be, prod, target))
    report("F4 case (I) product identity prod w_i = (-1)^{a+b+1} xi^{-3e} (float, worst rel err %.1e)" % worst, ok)
else:
    report("F4 skipped (no numpy)", True)

# ---------------------------------------------------------------- F5
ok = True
for beta in range(1, 41):
    a = ksub(kpow(ksub(KONE, XI), beta), kpow(kneg(XI), beta))
    if k_is_rational(a) != (beta == 1):
        ok = False
    if beta == 1 and a != KONE:
        ok = False
# 有理区间
ok_int = (2 * hi ** 3 < Fraction(64, 100))
inv3 = 1 / hi ** 3  # xi^{-3} >= hi^{-3}
ok_int &= inv3 * (inv3 - 1) ** 2 > Fraction(38, 10) ** 2
# 浮点：乘积公式、u(x_ζ)、模的比较
xi2 = None
roots = np.roots([1, 0, 1, -1]) if have_np else []
for r in roots:
    if abs(r.imag) > 1e-9:
        xi2 = complex(r)
        break
okf = True
for beta in range(2, 42):
    zs = [cmath.exp(2j * cmath.pi * t / beta) for t in range(beta)]
    prod = 1
    for zt in zs:
        prod *= (xi_f ** 2 + zt)
    if abs(prod - (xi_f ** (2 * beta) - (-1) ** beta)) > 1e-9 * max(1, abs(prod)):
        okf = False
    for zt in zs:
        x = zt / (xi_f ** 2 + zt)
        u = x ** 3 / (1 - x)
        if abs(u - zt ** 3 / (xi_f ** 2 * (xi_f ** 2 + zt) ** 2)) > 1e-9 * max(1, abs(u)):
            okf = False
    if beta % 2 == 1 and xi2 is not None:
        a1 = (1 - xi_f) ** beta - (-xi_f) ** beta
        a2 = (1 - xi2) ** beta - (-xi2) ** beta
        if not (abs(a1) < 0.64 < 3.8 < abs(a2)):
            okf = False
report("F5 case (IV): a rational only for beta=1 (exact, beta<=40); interval bounds %s; float identities %s" % (ok_int, okf),
       ok and ok_int and okf)

# ---------------------------------------------------------------- F6 反向检查
deg, nd, common = fiber_test(2, 1, exp_override=2 - 1)  # 错把 e 写成 α-β
rev1 = (sum(common) < nd)  # 改坏后 (2,1) 被误判为 excluded => 正对照失败
bad_xi = []
for (al, be) in [(1, 2), (3, 1), (2, 3), (4, 0), (0, 3)]:
    dg, n2, cm = fiber_test(al, be, exp_override=(al - be) if al >= 1 else -be)
    if cm[0] < 1:
        bad_xi.append((al, be))
rev2 = len(bad_xi) > 0
print("  reverse: corrupted exponent -> (2,1) control flips to 'excluded': %s; 'xi on fibre' fails for %s" % (rev1, bad_xi))
report("F6 reverse check: corrupting v_0 is detected (control (2,1) and xi-on-fibre both FAIL)", rev1 and rev2)

nf = sum(1 for _, o in results if not o)
print("SUMMARY fiber: %d PASS, %d FAIL" % (len(results) - nf, nf))
sys.exit(1 if nf else 0)
