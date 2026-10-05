# -*- coding: utf-8 -*-
"""final-audit / math-c3: exact Laurent series in x with tracked precision (Fractions only).

A Laurent series is stored as (val, coeffs): sum_i coeffs[i] x^(val+i), known exactly for
exponents val .. val+len(coeffs)-1 (relative precision = len(coeffs)).
"""
from fractions import Fraction
from math import comb, factorial


class L:
    __slots__ = ('v', 'c')

    def __init__(self, v, c):
        self.v = v
        self.c = [Fraction(a) for a in c]

    @staticmethod
    def poly(p, prec):
        """polynomial p (list, p[i] = coeff of x^i) as Laurent series known up to x^(prec-1)."""
        c = [Fraction(p[i]) if i < len(p) else Fraction(0) for i in range(prec)]
        return L(0, c)

    @staticmethod
    def mono(k, coef, relprec):
        return L(k, [Fraction(coef)] + [Fraction(0)] * (relprec - 1))

    def top(self):
        return self.v + len(self.c)          # first unknown exponent

    def __add__(self, o):
        v = min(self.v, o.v)
        top = min(self.top(), o.top())
        c = [Fraction(0)] * (top - v)
        for i, a in enumerate(self.c):
            e = self.v + i
            if e < top:
                c[e - v] += a
        for i, a in enumerate(o.c):
            e = o.v + i
            if e < top:
                c[e - v] += a
        return L(v, c)

    def __neg__(self):
        return L(self.v, [-a for a in self.c])

    def __sub__(self, o):
        return self + (-o)

    def scale(self, s):
        return L(self.v, [s * a for a in self.c])

    def shift(self, k):
        return L(self.v + k, list(self.c))

    def __mul__(self, o):
        n = min(len(self.c), len(o.c))
        c = [Fraction(0)] * n
        for i in range(n):
            a = self.c[i]
            if a == 0:
                continue
            for j in range(n - i):
                b = o.c[j]
                if b:
                    c[i + j] += a * b
        return L(self.v + o.v, c)

    def normalize(self):
        """drop leading zeros (decreases relative precision accordingly)."""
        i = 0
        while i < len(self.c) and self.c[i] == 0:
            i += 1
        return L(self.v + i, self.c[i:])

    def inv(self):
        s = self.normalize()
        assert s.c and s.c[0] != 0, 'cannot invert'
        n = len(s.c)
        a0 = s.c[0]
        r = [Fraction(0)] * n
        r[0] = 1 / a0
        for k in range(1, n):
            acc = Fraction(0)
            for j in range(1, k + 1):
                acc += s.c[j] * r[k - j]
            r[k] = -acc / a0
        return L(-s.v, r)

    def coeff(self, e):
        if e < self.v:
            return Fraction(0)
        assert e < self.top(), 'coefficient x^%d not known (top=%d)' % (e, self.top())
        return self.c[e - self.v]

    def check_no_negative(self, upto):
        """True iff all coefficients of x^e, e<0, vanish (within known range)."""
        for i, a in enumerate(self.c):
            e = self.v + i
            if e < 0 and a != 0:
                return False
        return True


def rf(a, n):
    """rising factorial (a)_n for a Fraction/int."""
    r = Fraction(1)
    for i in range(n):
        r *= (a + i)
    return r


def gbinom_neg(c, r):
    """[t^r](1-t)^(-c) = (c)_r/r!  (c any rational)."""
    return rf(Fraction(c), r) / factorial(r)
