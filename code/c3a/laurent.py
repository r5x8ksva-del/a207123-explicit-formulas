# -*- coding: utf-8 -*-
"""x 的 Laurent 级数（Fraction 系数），显式记录绝对精度 top：
L = sum_{e=v}^{top} c[e-v] x^e，且对 e <= top 精确（e > top 的系数未知）。
有限多项式按 top = CAP 构造（保守）。乘法 / 求逆 / 加法按规则传播 top。"""
from fractions import Fraction

ZERO_V = None


class Lau:
    __slots__ = ('v', 'c', 'top')

    def __init__(self, v, c, top):
        # c[i] 对应 x^{v+i}，只保留 v+i <= top
        n = top - v + 1
        c = [Fraction(a) for a in c[:max(n, 0)]]
        if n > len(c):
            c += [Fraction(0)] * (n - len(c))
        i = 0
        while i < len(c) and c[i] == 0:
            i += 1
        if i == len(c):
            self.v, self.c, self.top = ZERO_V, [], top
        else:
            self.v, self.c, self.top = v + i, c[i:], top

    @staticmethod
    def poly(coeffs, cap, shift=0):
        """精确有限多项式 x^shift * sum coeffs[i] x^i（top = cap）。"""
        return Lau(shift, list(coeffs), cap)

    def is_zero(self):
        return self.v is ZERO_V

    def scale(self, a):
        if self.is_zero():
            return self
        return Lau(self.v, [a * b for b in self.c], self.top)

    def __mul__(self, o):
        if not isinstance(o, Lau):
            return self.scale(o)
        if self.is_zero() or o.is_zero():
            top = min(self.top + (o.v if not o.is_zero() else 0), o.top + (self.v if not self.is_zero() else 0))
            return Lau(0, [], top)
        v = self.v + o.v
        top = min(self.top + o.v, o.top + self.v)
        n = top - v + 1
        r = [Fraction(0)] * max(n, 0)
        for i, a in enumerate(self.c):
            if i >= n:
                break
            if a:
                for j in range(min(len(o.c), n - i)):
                    b = o.c[j]
                    if b:
                        r[i + j] += a * b
        return Lau(v, r, top)

    __rmul__ = __mul__

    def inv(self):
        assert not self.is_zero()
        v = self.v
        n = self.top - v + 1          # 相对精度（项数）
        c0 = self.c[0]
        r = [Fraction(0)] * n
        r[0] = 1 / c0
        for k in range(1, n):
            s = Fraction(0)
            for i in range(1, min(k, len(self.c) - 1) + 1):
                if self.c[i]:
                    s += self.c[i] * r[k - i]
            r[k] = -s / c0
        return Lau(-v, r, -v + n - 1)

    def __add__(self, o):
        if not isinstance(o, Lau):
            o = Lau(0, [o], self.top)
        top = min(self.top, o.top)
        if self.is_zero():
            return Lau(o.v if not o.is_zero() else 0, o.c, top)
        if o.is_zero():
            return Lau(self.v, self.c, top)
        v = min(self.v, o.v)
        n = top - v + 1
        r = [Fraction(0)] * max(n, 0)
        for L in (self, o):
            d = L.v - v
            for i, a in enumerate(L.c):
                if d + i < n:
                    r[d + i] += a
        return Lau(v, r, top)

    __radd__ = __add__

    def __neg__(self):
        return self.scale(-1)

    def __sub__(self, o):
        return self + (-o)

    def coeff(self, e):
        assert e <= self.top, '超出精度 e=%d top=%d' % (e, self.top)
        if self.is_zero() or e < self.v:
            return Fraction(0)
        return self.c[e - self.v]

    def valuation(self):
        return self.v
