# -*- coding: utf-8 -*-
"""s11-b6a 复核 C1–C3：notes/11 推论 5 及其依据里写出的微分方程，逐个数值核对（双精度）。

不导入项目里的任何模块，只用标准库（math.gamma 只用于实参数）。函数都用级数或标准组合公式实现，
导数用 Cauchy 积分（小圆周上的梯形公式，圆周不碰 0 和负实轴）求，然后算方程残差。

  C1  Kummer 方程 w y'' + (beta - w) y' - alpha y = 0：1F1(alpha;beta;w)、w^{1-beta}1F1(alpha-beta+1;2-beta;w)、
      Tricomi U（beta 非整数时的组合式）、正则化 1F1/Gamma(beta)（含 beta=-2）
      Whittaker 方程 y'' + (-1/4 + kappa/w + (1/4-mu^2)/w^2) y = 0：M_{kappa,mu}、W_{kappa,mu}
  C2  不完全 Gamma：Gamma(c,w)、gamma(c,w)（c 非整数）与 Gamma(-2,w)（c 为负整数，含 log w）满足
      w y'' + (w+1-c) y' = 0；E_1=Gamma(0,.) 满足 w y'' + (w+1) y' = 0；Ei 满足 w y'' + (1-w) y' = 0；
      Bessel J_nu、Y_nu（nu 非整数）满足 w^2 y'' + w y' + (w^2-nu^2) y = 0；Airy Ai 满足 y'' = w y
  C3  反向检查：把 Gamma(c,.) 方程里的 (w+1-c) 换成 (w+1+c)、把 Ei 方程里的 (1-w) 换成 (1+w)、
      把 Whittaker 方程的 kappa/w 换成 -kappa/w，残差都显著非零
"""
import cmath
import math
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []
EG = 0.57721566490153286060651209008240243


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def rgamma(x):
    if x <= 0 and abs(x - round(x)) < 1e-14:
        return 0.0
    return 1.0 / math.gamma(x)


def hyp1f1(a, b, w, reg=False, nmax=400):
    """sum (a)_n w^n / ((b)_n n!)；reg=True 时为 sum (a)_n w^n / (Gamma(b+n) n!)（b 为非正整数时前几项为 0）。"""
    n0 = 0
    if reg and b <= 0 and abs(b - round(b)) < 1e-14:
        n0 = int(round(1 - b))
    # 第 n0 项
    term = 1.0 + 0j
    for i in range(n0):
        term *= (a + i) * w / (i + 1)
    term *= rgamma(b + n0) if reg else 1.0
    if not reg:
        term = 1.0 + 0j
    s, n = 0j, n0
    while n <= nmax:
        s += term
        term *= (a + n) * w / ((n + 1) * (b + n))
        n += 1
        if n > n0 + 20 and abs(term) < 1e-20 * max(1.0, abs(s)):
            break
    return s


def kummer_U(a, b, w):
    return (math.gamma(1 - b) / math.gamma(a - b + 1) * hyp1f1(a, b, w)
            + math.gamma(b - 1) / math.gamma(a) * cmath.exp((1 - b) * cmath.log(w)) * hyp1f1(a - b + 1, 2 - b, w))


def lower_gamma(c, w):
    s, k, term = 0j, 0, 1.0 + 0j       # term = (-w)^k / k!
    while True:
        add = term / (c + k)
        s += add
        k += 1
        term *= -w / k
        if k > 20 and abs(add) < 1e-20 * max(1.0, abs(s)):
            break
    return cmath.exp(c * cmath.log(w)) * s


def E1(w):
    s, k, term = 0j, 0, 1.0 + 0j
    while True:
        k += 1
        term *= -w / k
        add = term / k
        s += add
        if k > 20 and abs(add) < 1e-20 * max(1.0, abs(s)):
            break
    return -EG - cmath.log(w) - s


def Ei(w):
    s, k, term = 0j, 0, 1.0 + 0j
    while True:
        k += 1
        term *= w / k
        add = term / k
        s += add
        if k > 20 and abs(add) < 1e-20 * max(1.0, abs(s)):
            break
    return EG + cmath.log(w) + s


def upper_gamma_negint(n, w):
    """Gamma(-n, w) = ((-1)^n/n!) [E_1(w) - e^{-w} sum_{k<n} (-1)^k k!/w^{k+1}]。"""
    s = sum((-1) ** k * math.factorial(k) / w ** (k + 1) for k in range(n))
    return (-1) ** n / math.factorial(n) * (E1(w) - cmath.exp(-w) * s)


def besselJ(nu, w):
    s, k = 0j, 0
    half = w / 2
    lh = cmath.log(half)
    while True:
        add = (-1) ** k * cmath.exp((2 * k + nu) * lh) * rgamma(k + nu + 1) / math.factorial(k)
        s += add
        k += 1
        if k > 10 and abs(add) < 1e-20 * max(1.0, abs(s)):
            break
    return s


def besselY(nu, w):
    return (besselJ(nu, w) * math.cos(nu * math.pi) - besselJ(-nu, w)) / math.sin(nu * math.pi)


def airy_ai(w):
    c1 = 0.355028053887817239260
    c2 = 0.258819403792806798405
    f, g = 0j, 0j
    tf, tg = 1.0 + 0j, w + 0j          # 第 k 项
    k = 0
    while k < 200:
        f += tf
        g += tg
        tf *= w ** 3 / ((3 * k + 2) * (3 * k + 3))
        tg *= w ** 3 / ((3 * k + 3) * (3 * k + 4))
        k += 1
        if abs(tf) + abs(tg) < 1e-22:
            break
    return c1 * f - c2 * g


def derivs(fun, w, r=None, n=64):
    if r is None:
        r = 0.2 * abs(w)
    v0 = fun(w)
    d1 = d2 = 0j
    for j in range(n):
        th = 2 * math.pi * j / n
        e = cmath.exp(1j * th)
        fv = fun(w + r * e)
        d1 += fv / e
        d2 += fv / (e * e)
    return v0, d1 / (n * r), 2 * d2 / (n * r * r)


WS = [0.7 + 0.4j, 1.5 - 0.8j, 2.3 + 1.1j]


def resid(fun, ode, ws=WS):
    worst = 0.0
    for w in ws:
        y, y1, y2 = derivs(fun, w)
        val, scale = ode(w, y, y1, y2)
        worst = max(worst, abs(val) / scale)
    return worst


def main():
    al, be = 0.37, 1.61
    kum = lambda w, y, y1, y2: (w * y2 + (be - w) * y1 - al * y, abs(w * y2) + abs((be - w) * y1) + abs(al * y))
    items = [
        ('1F1', lambda w: hyp1f1(al, be, w), kum),
        ('w^{1-b}1F1', lambda w: cmath.exp((1 - be) * cmath.log(w)) * hyp1f1(al - be + 1, 2 - be, w), kum),
        ('Tricomi U', lambda w: kummer_U(al, be, w), kum),
    ]
    be2 = -2.0
    kum2 = lambda w, y, y1, y2: (w * y2 + (be2 - w) * y1 - al * y, abs(w * y2) + abs((be2 - w) * y1) + abs(al * y))
    items.append(('1F1/Gamma(b), b=-2', lambda w: hyp1f1(al, be2, w, reg=True), kum2))
    ka, mu = 0.3, 0.45
    whit = lambda w, y, y1, y2: (y2 + (-0.25 + ka / w + (0.25 - mu * mu) / w ** 2) * y,
                                 abs(y2) + abs((-0.25 + ka / w + (0.25 - mu * mu) / w ** 2) * y))
    Mkm = lambda w: cmath.exp(-w / 2) * cmath.exp((mu + 0.5) * cmath.log(w)) * hyp1f1(mu - ka + 0.5, 1 + 2 * mu, w)
    Wkm = lambda w: cmath.exp(-w / 2) * cmath.exp((mu + 0.5) * cmath.log(w)) * kummer_U(mu - ka + 0.5, 1 + 2 * mu, w)
    items += [('Whittaker M', Mkm, whit), ('Whittaker W', Wkm, whit)]
    worst1, lines = 0.0, []
    for name, fun, ode in items:
        r = resid(fun, ode)
        worst1 = max(worst1, r)
        lines.append('%s:%.1e' % (name, r))
    report('C1', worst1 < 1e-9, '方程残差（相对）：' + ', '.join(lines))
    # C2
    c = 0.62
    gam_ode = lambda cc: (lambda w, y, y1, y2: (w * y2 + (w + 1 - cc) * y1, abs(w * y2) + abs((w + 1 - cc) * y1)))
    items2 = [
        ('Gamma(c,w)', lambda w: math.gamma(c) - lower_gamma(c, w), gam_ode(c)),
        ('gamma(c,w)', lambda w: lower_gamma(c, w), gam_ode(c)),
        ('Gamma(-2,w)', lambda w: upper_gamma_negint(2, w), gam_ode(-2)),
        ('E_1', E1, gam_ode(0)),
        ('Ei', Ei, lambda w, y, y1, y2: (w * y2 + (1 - w) * y1, abs(w * y2) + abs((1 - w) * y1))),
    ]
    nu = 0.4
    bes = lambda w, y, y1, y2: (w * w * y2 + w * y1 + (w * w - nu * nu) * y,
                                abs(w * w * y2) + abs(w * y1) + abs((w * w - nu * nu) * y))
    items2 += [('J_nu', lambda w: besselJ(nu, w), bes), ('Y_nu', lambda w: besselY(nu, w), bes),
               ('Ai', airy_ai, lambda w, y, y1, y2: (y2 - w * y, abs(y2) + abs(w * y)))]
    worst2, lines = 0.0, []
    for name, fun, ode in items2:
        r = resid(fun, ode)
        worst2 = max(worst2, r)
        lines.append('%s:%.1e' % (name, r))
    # 额外：Gamma(-2,w) 的组合式确实是积分 ∫_w^∞ s^{-3} e^{-s} ds（w=1.3，数值积分对照）
    w0 = 1.3
    h = 1e-3
    integ = 0.0
    for k in range(200000):
        s0 = w0 + (k + 0.5) * h
        integ += s0 ** (-3) * math.exp(-s0) * h
    ok_int = abs(upper_gamma_negint(2, w0) - integ) < 1e-6
    report('C2', worst2 < 1e-9 and ok_int, '方程残差（相对）：' + ', '.join(lines)
           + '；Gamma(-2,1.3) 组合式与数值积分之差 %.1e' % abs(upper_gamma_negint(2, w0) - integ))
    # C3
    bad = [
        resid(lambda w: math.gamma(c) - lower_gamma(c, w),
              lambda w, y, y1, y2: (w * y2 + (w + 1 + c) * y1, abs(w * y2) + abs((w + 1 + c) * y1))),
        resid(Ei, lambda w, y, y1, y2: (w * y2 + (1 + w) * y1, abs(w * y2) + abs((1 + w) * y1))),
        resid(Mkm, lambda w, y, y1, y2: (y2 + (-0.25 - ka / w + (0.25 - mu * mu) / w ** 2) * y,
                                         abs(y2) + abs((-0.25 - ka / w + (0.25 - mu * mu) / w ** 2) * y))),
    ]
    report('C3', min(bad) > 1e-3, '反向：改错系数后的残差 %s（应显著非零）' % ', '.join('%.2g' % b for b in bad))
    n_pass = sum(RES)
    print('SUMMARY s11b6a_cor5_ode pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
    return 0 if n_pass == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
