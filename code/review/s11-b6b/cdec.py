# -*- coding: utf-8 -*-
"""s11-b6b 复核用的小工具：decimal 上的复数运算（加减乘除、exp、主值 log、整数幂）与常数 pi。
本机没有 mpmath，这里只实现脚本 3–5 用到的部分。精度由调用方 set_prec 设定。"""
from decimal import Decimal as D, getcontext

_PI_CACHE = {}


def set_prec(p):
    getcontext().prec = p
    _PI_CACHE.clear()


def _atan_small(u):
    """|u| <= 0.2 左右时的 Taylor 级数。"""
    eps = D(10) ** (-(getcontext().prec + 5))
    s, term, k = D(0), u, 0
    u2 = u * u
    while True:
        add = term / (2 * k + 1)
        s += add if k % 2 == 0 else -add
        if abs(add) < eps:
            break
        term *= u2
        k += 1
    return s


def atan(u):
    u = D(u)
    if u < 0:
        return -atan(-u)
    if u > 1:
        return pi() / 2 - atan(1 / u)
    # 折半：atan(u) = 2 atan(u/(1+sqrt(1+u^2)))
    h = 0
    while u > D('0.1'):
        u = u / (1 + (1 + u * u).sqrt())
        h += 1
    return _atan_small(u) * (2 ** h)


def pi():
    p = getcontext().prec
    if p not in _PI_CACHE:
        getcontext().prec = p + 10
        val = 16 * _atan_small(D(1) / 5) - 4 * _atan_small(D(1) / 239)
        getcontext().prec = p
        _PI_CACHE[p] = +val
    return _PI_CACHE[p]


def atan2(y, x):
    y, x = D(y), D(x)
    if x > 0:
        return atan(y / x)
    if x < 0:
        return atan(y / x) + (pi() if y >= 0 else -pi())
    if y > 0:
        return pi() / 2
    if y < 0:
        return -pi() / 2
    raise ValueError('atan2(0,0)')


def sincos(th):
    th = D(th)
    tp = 2 * pi()
    # 归约到 [-pi, pi]
    k = (th / tp).to_integral_value()
    th = th - k * tp
    eps = D(10) ** (-(getcontext().prec + 5))
    s, c = D(0), D(0)
    term = D(1)
    n = 0
    while True:
        if n % 4 == 0:
            c += term
        elif n % 4 == 1:
            s += term
        elif n % 4 == 2:
            c -= term
        else:
            s -= term
        n += 1
        term = term * th / n
        if abs(term) < eps and n > 4:
            break
    return s, c


class CD:
    __slots__ = ('r', 'i')

    def __init__(self, r, i=0):
        self.r = r if isinstance(r, D) else D(r)
        self.i = i if isinstance(i, D) else D(i)

    @staticmethod
    def of(v):
        if isinstance(v, CD):
            return v
        if isinstance(v, complex):
            return CD(D(repr(v.real)), D(repr(v.imag)))
        return CD(D(v) if not isinstance(v, D) else v, 0)

    def __add__(self, o):
        o = CD.of(o)
        return CD(self.r + o.r, self.i + o.i)

    __radd__ = __add__

    def __sub__(self, o):
        o = CD.of(o)
        return CD(self.r - o.r, self.i - o.i)

    def __rsub__(self, o):
        return CD.of(o) - self

    def __neg__(self):
        return CD(-self.r, -self.i)

    def __mul__(self, o):
        o = CD.of(o)
        return CD(self.r * o.r - self.i * o.i, self.r * o.i + self.i * o.r)

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = CD.of(o)
        den = o.r * o.r + o.i * o.i
        return CD((self.r * o.r + self.i * o.i) / den, (self.i * o.r - self.r * o.i) / den)

    def __rtruediv__(self, o):
        return CD.of(o) / self

    def __pow__(self, n):
        assert isinstance(n, int)
        if n < 0:
            return CD(1) / (self ** (-n))
        r, base = CD(1), self
        while n:
            if n & 1:
                r = r * base
            base = base * base
            n >>= 1
        return r

    def conj(self):
        return CD(self.r, -self.i)

    def abs(self):
        return (self.r * self.r + self.i * self.i).sqrt()

    def __repr__(self):
        return 'CD(%s, %s)' % (self.r, self.i)

    def to_complex(self):
        return complex(float(self.r), float(self.i))


def cexp(w):
    w = CD.of(w)
    e = w.r.exp()
    s, c = sincos(w.i)
    return CD(e * c, e * s)


def clog(w):
    """主值 log（辐角在 (-pi, pi]）。"""
    w = CD.of(w)
    return CD((w.r * w.r + w.i * w.i).ln() / 2, atan2(w.i, w.r))


def cpow_real_base(t, lam):
    """t^lam，t 为正实数，lam 复数：exp(lam ln t)。"""
    return cexp(CD.of(lam) * D(t).ln())


def newton_real(f, df, x0, steps=200):
    x = D(x0)
    eps = D(10) ** (-(getcontext().prec - 3))
    for _ in range(steps):
        dx = f(x) / df(x)
        x -= dx
        if abs(dx) < eps:
            break
    return x


def newton_complex(f, df, x0, steps=200):
    x = CD.of(x0)
    eps = D(10) ** (-(getcontext().prec - 3))
    for _ in range(steps):
        dx = f(x) / df(x)
        x = x - dx
        if dx.abs() < eps:
            break
    return x
