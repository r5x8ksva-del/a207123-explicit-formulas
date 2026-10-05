# -*- coding: utf-8 -*-
"""审计 a1-formulas：T3.4(1)(2) 的 K 闭式与常数项恒等式（数值，Decimal 高精度）。

  I - S = x^{-3} K(x) e^a a^λ，K = Γ(-λ)[1 + λ x^5 J(x)]，J = ∫_0^∞ w e^{-w}(1+x^3 w)^{λ-1} dw；
  Σ_m t^m/P_m = x^{-3} e^a [E_{λ+1}(a) - Γ(-λ) a^λ]，E_p(a)=∫_1^∞ e^{-au}u^{-p}du；
  以及 1 < K/Γ(-λ) < 2。
"""
import time
from fractions import Fraction
from decimal import Decimal, getcontext, localcontext
from common import *  # noqa

t0 = time.time()
PREC = 140
getcontext().prec = PREC

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
        return +(16 * arctan_inv(5) - 4 * arctan_inv(239))
PI = pi_dec()

def bernoulli(nmax):
    B = [Fraction(0)] * (nmax + 1)
    B[0] = Fraction(1)
    for n in range(1, nmax + 1):
        B[n] = -sum(comb(n + 1, k) * B[k] for k in range(n)) / (n + 1)
    return B
BN = bernoulli(160)

def lngamma(z):
    """ln Γ(z)，z>0：先上移到 z>=200 再用 Stirling 级数。"""
    shift = Decimal(0)
    while z < 200:
        shift += z.ln()
        z += 1
    s = (z - Decimal(1) / 2) * z.ln() - z + (2 * PI).ln() / 2
    zp = z
    z2 = z * z
    for n in range(1, 70):
        b = BN[2 * n]
        term = Decimal(b.numerator) / Decimal(b.denominator) / (2 * n * (2 * n - 1) * zp)
        s += term
        zp *= z2
        if abs(term) < Decimal(10) ** (-(PREC + 5)):
            break
    return s - shift

def sin_dec(x):
    x = x % (2 * PI)
    if x > PI:
        x -= 2 * PI
    s, term, n = Decimal(0), x, 1
    while abs(term) > Decimal(10) ** (-(PREC + 5)):
        s += term
        term *= -x * x / ((n + 1) * (n + 2))
        n += 2
    return s

def gamma_neg(lam):
    """Γ(-λ) = -π / (sin(πλ) Γ(1+λ))。"""
    return -PI / (sin_dec(PI * lam) * lngamma(1 + lam).exp())

def exp_sinh(f, scale, h=Decimal(1) / 256, T=Decimal(7)):
    tot = Decimal(0)
    n = int(T / h)
    for i in range(-n, n + 1):
        tau = h * i
        et = tau.exp()
        sh = (et - 1 / et) / 2
        ch = (et + 1 / et) / 2
        y = (PI / 2 * sh).exp()
        if y > Decimal(10) ** 5:
            continue
        dy = PI / 2 * ch * y
        tot += f(y / scale) * dy
    return tot * h / scale

def J_of(X, lam):
    def f(w):
        base = 1 + X ** 3 * w
        e = -w + (lam - 1) * base.ln()
        if e < Decimal(-100000):
            return Decimal(0)
        return w * e.exp()
    # 衰减率约 1-(λ-1)x^3 = x + x^3·... 取 scale = x
    return exp_sinh(f, X)

def S_partial(x, t, M):
    G = Fraction(1)
    tot = Fraction(0)
    tp = Fraction(1)
    for m in range(0, M + 1):
        G = (G + m * x * x) / (1 - x - m * x ** 3)
        tot += tp * G
        tp *= t
    return tot
def S0_partial(x, t, M):
    Pm = Fraction(1)
    tot = Fraction(0)
    tp = Fraction(1)
    for m in range(0, M + 1):
        Pm *= (1 - x - m * x ** 3)
        tot += tp / Pm
        tp *= t
    return tot
def dec(fr):
    return Decimal(fr.numerator) / Decimal(fr.denominator)

xq, tq = Fraction(21, 100), Fraction(-1, 20)
X, Tt = dec(xq), dec(tq)
lam = (1 - X) / X ** 3
a = -Tt / X ** 3
g = gamma_neg(lam)
J = J_of(X, lam)
K = g * (1 + lam * X ** 5 * J)
pred = K * a.exp() * (lam * a.ln()).exp() / X ** 3
# I - S（与 audit_c3_num 同法独立再算一次）
def integrand(sig):
    es = sig.exp()
    expo = (Tt * (es - 1) - (1 - X) * sig) / X ** 3
    if expo < Decimal(-200000):
        return Decimal(0)
    wv = Tt * es
    return expo.exp() * (1 + X * X * wv / (1 - wv) ** 2)
I = exp_sinh(integrand, (1 - X - Tt) / X ** 3) / X ** 3
S = dec(S_partial(xq, tq, 260))
diff = I - S
rel = abs(pred / diff - 1)
report(rel < Decimal('1e-40'), 'T3.4.2-K', '(21/100,-1/20)：x^{-3}Γ(-λ)[1+λx^5J]e^a a^λ = %s，I-S = %s，相对差 %s' % (format(pred, '.20e'), format(diff, '.20e'), format(rel, '.1e')))
# 常数项：Σ t^m/P_m = x^{-3} e^a [E_{λ+1}(a) - Γ(-λ) a^λ]
def E_int(s):
    u = 1 + s
    e = -a * u - (lam + 1) * u.ln()
    if e < Decimal(-100000):
        return Decimal(0)
    return e.exp()
Ep = exp_sinh(E_int, a + lam + 1)
rhs = a.exp() * (Ep - g * (lam * a.ln()).exp()) / X ** 3
lhs = dec(S0_partial(xq, tq, 260))
rel0 = abs(rhs / lhs - 1)
I0 = a.exp() * Ep / X ** 3
report(rel0 < Decimal('1e-60'), 'T3.4.1-const', 'Σt^m/P_m = x^{-3}e^a[E_{λ+1}(a)-Γ(-λ)a^λ] 于 (21/100,-1/20)：相对差 %s；常数项差 I_0-Σ = %s' % (format(rel0, '.1e'), format(I0 - lhs, '.6e')))
# 1 < K/Γ(-λ) < 2
getcontext().prec = 60
PREC = 60
PI = pi_dec()
vals = []
for xs in ('0.001', '0.01', '0.05', '0.1', '0.21', '0.37', '0.5', '0.73', '0.9'):
    Xv = Decimal(xs)
    lv = (1 - Xv) / Xv ** 3
    Jv = J_of(Xv, lv)
    vals.append((xs, float(1 + lv * Xv ** 5 * Jv)))
report(all(1 < v < 2 for _, v in vals) and vals[0][1] > 1.99 and all(vals[i][1] > vals[i + 1][1] for i in range(len(vals) - 1)), 'T3.4.2-ratio', '1 < K/Γ(-λ)=1+λx^5J < 2，x→0 趋于 2：%s' % [(x_, round(v, 4)) for x_, v in vals])

summary('audit_c3_K')
print('elapsed %.1fs' % (time.time() - t0))
