# -*- coding: utf-8 -*-
"""审计 a1-formulas：T3.4 的数值断言（数值；不是证明）。

  * S(x,t)=Σ_m t^m G_m(x) 的精确有理部分和（G_m 用 (G_{m-1}+m x^2)/b_m 精确递推）；
  * I(x,t) 用 exp-sinh 求积（Decimal 高精度），检查 (21/100,-1/20) 处 I-S；
  * W(1/e)、f_k(-1/2) 的增长。
"""
import time
from fractions import Fraction
from decimal import Decimal, getcontext, localcontext
from common import *  # noqa

t0 = time.time()

def S_partial(x, t, M):
    G = Fraction(1)                    # G_{-1}
    tot = Fraction(0)
    tp = Fraction(1)
    terms = []
    for m in range(0, M + 1):
        G = (G + m * x * x) / (1 - x - m * x ** 3)
        term = tp * G
        tot += term
        terms.append(term)
        tp *= t
    return tot, terms

def dec(fr, prec=60):
    with localcontext() as c:
        c.prec = prec
        return Decimal(fr.numerator) / Decimal(fr.denominator)

# (3) 反例 (x,t)=(3/5,-1/2)
x, t = Fraction(3, 5), Fraction(-1, 2)
S400, terms = S_partial(x, t, 400)
last = max(abs(dec(terms[m], 30)) for m in range(390, 401))
v = dec(S400, 40)
report(abs(v - Decimal('-1057.810873')) < Decimal('5e-7'), 'T3.4.3-S', 'S(3/5,-1/2) 的 m<=400 精确部分和 = %s（报告 ≤-1057.810873+3.5e-118）；m=390..400 的最大项 %.2e' % (str(v)[:20], last))

# (5) (21/100,-1/2)：|S|>1e44
x2, t2 = Fraction(21, 100), Fraction(-1, 2)
S2, terms2 = S_partial(x2, t2, 600)
v2 = dec(S2, 30)
imax = max(range(601), key=lambda m: abs(terms2[m]))
report(abs(v2) > Decimal('1e44'), 'T3.4.5-S-big', 'S(21/100,-1/2) 部分和(m<=600) = %.6e，最大项在 m=%d（%.3e）' % (v2, imax, dec(terms2[imax], 20)))

# W(1/e)
getcontext().prec = 50
w = Decimal('0.3')
e = Decimal(1).exp()
for _ in range(60):
    w = w - (w * w.exp() - 1 / e) / (w.exp() * (1 + w))
report(abs(w - Decimal('0.2785')) < Decimal('0.00005'), 'T3.4.5-W', 'W(1/e)=%s（报告 ≈0.2785）' % str(w)[:12])

# f_k(-1/2)=h_k(-1/2)/(3/2)^{k+1}
KH = 150
TL = lemma1_table(KH, KH + 1)
def h_at(k, tt):
    tot = Fraction(0)
    for i in range(0, k + 1):
        c = sum((-1) ** (i - j) * comb(k + 1, i - j) * TL[k][j] for j in range(0, i + 1))
        tot += c * tt ** i
    return tot
vals = {}
for k in (75, 150):
    fk = h_at(k, Fraction(-1, 2)) / Fraction(3, 2) ** (k + 1)
    with localcontext() as c:
        c.prec = 40
        a = abs(dec(fk, 400))
        vals[k] = float(a.ln() / k) if a != 0 else None
import math
r75, r150 = math.exp(vals[75]), math.exp(vals[150])
report(abs(r75 - 1.669) < 0.0006 and abs(r150 - 2.036) < 0.0006 and abs(r150 / r75 - 1.22) < 0.006,
       'T3.4.5-gevrey', '|f_k(-1/2)|^{1/k}：k=75 → %.4f，k=150 → %.4f，比值 %.3f（报告 1.669、2.036、1.22）' % (r75, r150, r150 / r75))

# (5) 数值例：(21/100,-1/20) 处 I-S
PREC = 130
getcontext().prec = PREC
x3, t3 = Fraction(21, 100), Fraction(-1, 20)
S3, _ = S_partial(x3, t3, 260)
Sdec = dec(S3, PREC)
X = Decimal(21) / 100
Tt = Decimal(-1) / 20
X3 = X ** 3
# π
def pi_dec():
    with localcontext() as c:
        c.prec = PREC + 10
        def arctan_inv(n):
            n = Decimal(n)
            x_ = 1 / n
            s = x_
            k = 1
            term = x_
            while True:
                term *= -1 / (n * n)
                k += 2
                d = term / k
                if abs(d) < Decimal(10) ** (-(PREC + 8)):
                    break
                s += d
            return s
        return 16 * arctan_inv(5) - 4 * arctan_inv(239)
PI = pi_dec()
scale = (1 - X - Tt) / X3          # 近 0 处衰减率 ≈ 90.7
def integrand(sig):
    es = sig.exp()
    expo = (Tt * (es - 1) - (1 - X) * sig) / X3
    if expo < Decimal(-200000):
        return Decimal(0)
    wv = Tt * es
    return expo.exp() * (1 + X * X * wv / (1 - wv) ** 2)
def exp_sinh(h, T=Decimal(7)):
    # ∫_0^∞ f(σ)dσ，σ = y/scale，y = exp(π/2 sinh τ)
    tot = Decimal(0)
    n = int(T / h)
    for i in range(-n, n + 1):
        tau = h * i
        sh = (tau.exp() - (-tau).exp()) / 2
        ch = (tau.exp() + (-tau).exp()) / 2
        y = (PI / 2 * sh).exp()
        dy = PI / 2 * ch * y
        if y > Decimal(10) ** 6:
            continue
        f = integrand(y / scale)
        tot += f * dy
    return tot * h / scale
res = []
for h in (Decimal(1) / 64, Decimal(1) / 128, Decimal(1) / 256, Decimal(1) / 512):
    Iv = exp_sinh(h) / X3
    res.append(Iv - Sdec)
diff = res[-1]
conv = abs(res[-1] - res[-2])
print('INFO I-S 逐次加密（Decimal 原生格式，不经 float）: %s' % [format(r, '.30e') for r in res])
report(abs(diff / Decimal('3.81401776553037367e-62') - 1) < Decimal('2e-18') and conv < Decimal('1e-85'),
       'T3.4.5-diff', '(21/100,-1/20) 处 I-S = %s（报告 3.81401776553037367e-62；求积加密差 %s）' % (format(diff, '.25e'), format(conv, '.1e')))

summary('audit_c3_num')
print('elapsed %.1fs' % (time.time() - t0))
