# -*- coding: utf-8 -*-
"""c3a 数值部分（decimal 高精度；属于「数值证据」，不是证明）。

I(x,t)   = (1/(1-x)) int_0^inf e^{-s} exp((t/x^3)(e^{us}-1)) g(t e^{us}) ds          （= 草稿的 x^{-3} int_0^inf ... dsigma，sigma = u s）
I0(x,t)  = 同上但 g ≡ 1                                                             （= x^{-3} e^a E_{lambda+1}(a)）
S(x,t)   = sum_m t^m G_m(x)，G_m = (G_{m-1} + m x^2)/b_m(x)，G_{-1}=1（精确有理数求和）
S0(x,t)  = sum_m t^m / P_m(x)
K(x)     = reg int_0^inf tau^{-lambda-1} e^{-tau} g(-x^3 tau) dtau
         = sum_n phi_n/(n-lambda) + int_1^inf tau^{-lambda-1} phi(tau) dtau，phi(tau)=e^{-tau} g(-x^3 tau)
预测（已证明的恒等式）：I - S = x^{-3} K(x) e^a a^lambda，I0 - S0 = x^{-3} Gamma(-lambda) e^a a^lambda，a = -t/x^3。
"""
from decimal import Decimal as D, getcontext, localcontext
from fractions import Fraction
from math import comb


# ---------------- 基本函数 ----------------
def dec(fr):
    return D(fr.numerator) / D(fr.denominator)


def pi_dec():
    """Machin：pi = 16 arctan(1/5) - 4 arctan(1/239)。"""
    getcontext().prec += 10

    def arctan_inv(n):
        x = D(1) / n
        x2 = x * x
        s, term, k = D(0), x, 0
        eps = D(10) ** (-(getcontext().prec + 2))
        while abs(term) > eps:
            s += term / (2 * k + 1) if k % 2 == 0 else -term / (2 * k + 1)
            term *= x2
            k += 1
        return s
    p = 16 * arctan_inv(5) - 4 * arctan_inv(239)
    getcontext().prec -= 10
    return +p


def sin_dec(x, PI):
    getcontext().prec += 10
    twopi = 2 * PI
    x = x - twopi * (x / twopi).to_integral_value()
    s, term, k = D(0), x, 1
    eps = D(10) ** (-(getcontext().prec + 2))
    while abs(term) > eps:
        s += term
        term *= -x * x / ((2 * k) * (2 * k + 1))
        k += 1
    getcontext().prec -= 10
    return +s


def bernoulli_list(nmax):
    """B_0..B_nmax（B_1 = -1/2 约定），Fraction。"""
    B = [Fraction(0)] * (nmax + 1)
    B[0] = Fraction(1)
    for n in range(1, nmax + 1):
        B[n] = -sum(comb(n + 1, k) * B[k] for k in range(n)) / (n + 1)
    return B


def lngamma_pos(z, PI, nb=60, shift_to=None):
    """ln Gamma(z)，z>0 实数（Decimal）。先平移到 z+N >= shift_to，再用 Stirling 级数。"""
    prec = getcontext().prec
    if shift_to is None:
        shift_to = max(30, prec)
    getcontext().prec += 15
    B = bernoulli_list(2 * nb)
    acc = D(0)
    zz = z
    while zz < shift_to:
        acc += zz.ln()
        zz += 1
    s = (zz - D('0.5')) * zz.ln() - zz + (2 * PI).ln() / 2
    zp = zz
    z2 = zz * zz
    for k in range(1, nb + 1):
        s += dec(B[2 * k]) / (D(2 * k) * D(2 * k - 1) * zp)
        zp *= z2
    r = s - acc
    getcontext().prec -= 15
    return +r


def gamma_neg_reflect(lam, PI):
    """Gamma(-lambda) = -pi / (sin(pi lambda) Gamma(1+lambda))，lambda>0 非整数。"""
    return -PI / (sin_dec(PI * lam, PI) * lngamma_pos(1 + lam, PI).exp())


# ---------------- 双指数求积 ----------------
def expsinh_quad(f, tol_digits, h0=D('0.0625'), tmin=-6.5, tmax=3.5, maxlevel=8):
    """int_0^inf f(s) ds，s = exp((pi/2) sinh(tau))，梯形法逐级加密直到两级差 < 10^{-tol_digits}。"""
    PI = pi_dec()
    half_pi = PI / 2
    cache = {}

    def node(tau):
        if tau in cache:
            return cache[tau]
        et = tau.exp()
        sh = (et - 1 / et) / 2
        ch = (et + 1 / et) / 2
        s = (half_pi * sh).exp()
        w = s * half_pi * ch
        val = f(s) * w if w != 0 else D(0)
        cache[tau] = val
        return val

    h = h0
    prev = None
    for level in range(maxlevel):
        n_lo = int((D(tmin) / h).to_integral_value())
        n_hi = int((D(tmax) / h).to_integral_value())
        tot = D(0)
        for i in range(n_lo, n_hi + 1):
            tot += node(h * i)
        est = tot * h
        if prev is not None and abs(est - prev) < D(10) ** (-tol_digits):
            return est, abs(est - prev), level
        prev = est
        h = h / 2
    return est, abs(est - prev), level


# ---------------- 各量 ----------------
def I_val(x, t, with_g=True, tol_digits=None):
    """x, t 为 Fraction。返回 Decimal。"""
    if tol_digits is None:
        tol_digits = getcontext().prec - 8
    xd, td = dec(x), dec(t)
    u = xd ** 3 / (1 - xd)
    c = td / xd ** 3
    x2 = xd * xd
    big = D(10) ** 6

    def f(s):
        if s > big:
            return D(0)
        e = (u * s).exp()
        ex = -s + c * (e - 1)
        if ex < -(getcontext().prec * 3):
            return D(0)
        val = ex.exp()
        if with_g:
            w = td * e
            val *= 1 + x2 * w / ((1 - w) ** 2)
        return val
    val, err, lev = expsinh_quad(f, tol_digits)
    return val / (1 - xd), err, lev


def S_val(x, t, with_g=True, digits=None):
    """sum_m t^m G_m(x)（with_g）或 sum_m t^m / P_m(x)，精确 Fraction 求和到尾项足够小。"""
    if digits is None:
        digits = getcontext().prec + 5
    tol = Fraction(1, 10 ** digits)
    G_prev = Fraction(1)          # G_{-1}
    P = Fraction(1)               # P_{-1}
    tot = Fraction(0)
    tp = Fraction(1)
    m = 0
    small_run = 0
    while True:
        b = 1 - x - m * x ** 3
        P *= b
        if with_g:
            G = (G_prev + m * x * x) / b
        else:
            G = 1 / P
        term = tp * G
        tot += term
        # 尾项估计：m > lambda + 2 后 |G_m| 有界，按几何级数估计
        if abs(term) < tol and m > (1 - x) / x ** 3 + 5:
            small_run += 1
            if small_run >= 5:
                break
        else:
            small_run = 0
        G_prev = G
        tp *= t
        m += 1
    return dec(tot), m


def K_val(x, with_g=True, tol_digits=None):
    """K(x)（with_g）或 Gamma(-lambda)（不带 g）的正则化 Mellin 表示。"""
    if tol_digits is None:
        tol_digits = getcontext().prec - 8
    lam = (1 - x) / x ** 3
    # phi_n：phi(tau) = e^{-tau} (1 + sum_{j>=1} j x^2 (-x^3 tau)^j)
    tol = Fraction(1, 10 ** (getcontext().prec + 5))
    ser = Fraction(0)
    n = 0
    small = 0
    fact = 1
    while True:
        # phi_n = sum_{j=0}^n (-1)^{n-j}/(n-j)! c'_j
        if with_g:
            ph = Fraction(0)
            f_ = 1
            for j in range(0, n + 1):
                # (n-j)!
                pass
            ph = sum(Fraction((-1) ** (n - j), _fact(n - j)) * (1 if j == 0 else j * x * x * (-x ** 3) ** j)
                     for j in range(n + 1))
        else:
            ph = Fraction((-1) ** n, _fact(n))
        term = ph / (n - lam)
        ser += term
        if abs(term) < tol and n > lam + 5:
            small += 1
            if small >= 5:
                break
        else:
            small = 0
        n += 1
    xd = dec(x)
    lamd = dec(lam)
    x3 = xd ** 3
    x2 = xd * xd

    def f(w):
        tau = 1 + w
        val = (-(lamd + 1) * tau.ln() - tau)
        if val < -(getcontext().prec * 3):
            return D(0)
        val = val.exp()
        if with_g:
            z = -x3 * tau
            val *= 1 + x2 * z / ((1 - z) ** 2)
        return val
    tail, err, lev = expsinh_quad(f, tol_digits)
    return dec(ser) + tail


_FACT = [1]


def _fact(n):
    while len(_FACT) <= n:
        _FACT.append(_FACT[-1] * len(_FACT))
    return _FACT[n]


def predicted_gap(x, t, Kx):
    """x^{-3} K e^a a^lambda，a = -t/x^3 > 0。"""
    xd, td = dec(x), dec(t)
    a = -td / xd ** 3
    lam = dec((1 - x) / x ** 3)
    return Kx / xd ** 3 * a.exp() * (lam * a.ln()).exp()
