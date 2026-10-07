# -*- coding: utf-8 -*-
"""s10-b2 independent review library (written from scratch; imports nothing from the project).

K_i = Q[x]/(b_i), b_i(x) = 1 - x - i*x^3, eta = class of x.  Reduction rule eta^3 = (1 - eta)/i,
eta^{-1} = 1 + i*eta^2.  Elements are triples (c0, c1, c2) meaning c0 + c1*eta + c2*eta^2.

Also: the same ring modulo M (M = l or l^2, l prime with l not dividing i), and a second exact
model in the basis 1, y, y^2 with y = 1/eta, y^3 = y^2 + i (used as an independent cross-check).
"""
from fractions import Fraction as Fr
from math import factorial

# ----------------------------------------------------------------------------------------------
# polynomials in x with integer coefficients: list, index = exponent
# ----------------------------------------------------------------------------------------------

def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for s, x in enumerate(a):
        if x:
            for t, y in enumerate(b):
                if y:
                    out[s + t] += x * y
    return out


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[k] if k < len(a) else 0) + (b[k] if k < len(b) else 0) for k in range(n)]


def pderiv(a):
    return [k * a[k] for k in range(1, len(a))] or [0]


def b_poly(v):
    """b_v(x) = 1 - x - v x^3"""
    return [1, -1, 0, -v]


def P_poly(m):
    """P_m = prod_{v=0}^{m} b_v"""
    p = [1]
    for v in range(m + 1):
        p = pmul(p, b_poly(v))
    return p


def W_poly(m):
    """W_m = 1 + x^2 * sum_{j=1}^{m} j * P_{j-1}"""
    w = [1]
    for j in range(1, m + 1):
        w = padd(w, [0, 0] + [j * c for c in P_poly(j - 1)])
    return w


def Wtilde_poly(i):
    """W~_i(x) = 1 + sum_{j=1}^{i} j * i(i-1)...(i-j+1) * x^{3j+2}  (dense list)"""
    w = [0] * (3 * i + 3)
    w[0] = 1
    fall = 1
    for j in range(1, i + 1):
        fall *= (i - j + 1)
        w[3 * j + 2] += j * fall
    return w


def series_div(num, den, N):
    """power series num/den up to x^N (den[0] == 1), integer exact"""
    assert den[0] == 1
    out = []
    num = list(num) + [0] * (N + 1)
    for k in range(N + 1):
        c = num[k] - sum(den[t] * out[k - t] for t in range(1, min(k, len(den) - 1) + 1))
        out.append(c)
    return out


# ----------------------------------------------------------------------------------------------
# exact arithmetic in K_i (eta basis)
# ----------------------------------------------------------------------------------------------

class Ki:
    def __init__(self, i):
        assert i >= 1
        self.i = i
        self.ii = Fr(1, i)
        self._pos = [(Fr(1), Fr(0), Fr(0))]   # eta^0, eta^1, ...
        self._neg = [(Fr(1), Fr(0), Fr(0))]   # eta^0, eta^-1, ...

    def red(self, p):
        p = [Fr(c) for c in p] + [Fr(0)] * 3
        for d in range(len(p) - 1, 2, -1):
            c = p[d]
            if c:
                p[d - 3] += c * self.ii
                p[d - 2] -= c * self.ii
                p[d] = Fr(0)
        return (p[0], p[1], p[2])

    def mul(self, a, b):
        prod = [Fr(0)] * 5
        for s in range(3):
            if a[s]:
                for t in range(3):
                    if b[t]:
                        prod[s + t] += a[s] * b[t]
        return self.red(prod)

    def add(self, a, b):
        return tuple(a[k] + b[k] for k in range(3))

    def scal(self, c, a):
        return tuple(c * a[k] for k in range(3))

    def mul_eta(self, a):
        c0, c1, c2 = a
        return (c2 * self.ii, c0 - c2 * self.ii, c1)

    def mul_eta_inv(self, a):
        c0, c1, c2 = a
        return (c0 + c1, c2, self.i * c0)

    def eta_pow(self, n):
        if n >= 0:
            while len(self._pos) <= n:
                self._pos.append(self.mul_eta(self._pos[-1]))
            return self._pos[n]
        while len(self._neg) <= -n:
            self._neg.append(self.mul_eta_inv(self._neg[-1]))
        return self._neg[-n]

    def ev(self, poly, shift=0):
        """value at eta of sum_k poly[k] x^{k+shift}"""
        acc = (Fr(0), Fr(0), Fr(0))
        for k, c in enumerate(poly):
            if c:
                acc = self.add(acc, self.scal(Fr(c), self.eta_pow(k + shift)))
        return acc

    def mulmat(self, a):
        """matrix (rows = coordinate index) of multiplication by a"""
        cols = [self.mul(a, e) for e in ((Fr(1), Fr(0), Fr(0)), (Fr(0), Fr(1), Fr(0)), (Fr(0), Fr(0), Fr(1)))]
        return [[cols[c][r] for c in range(3)] for r in range(3)]

    def inv(self, a):
        M = self.mulmat(a)
        sol = solve3(M, [Fr(1), Fr(0), Fr(0)])
        chk = self.mul(a, tuple(sol))
        assert chk == (1, 0, 0), "inverse failed"
        return tuple(sol)


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def solve3(M, rhs):
    A = [[Fr(M[r][c]) for c in range(3)] + [Fr(rhs[r])] for r in range(3)]
    for col in range(3):
        piv = next(r for r in range(col, 3) if A[r][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [v / pv for v in A[col]]
        for r in range(3):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [A[r][c] - f * A[col][c] for c in range(4)]
    return [A[r][3] for r in range(3)]


def cols_det(a, b, c):
    """det of the 3x3 matrix whose columns are the coordinate vectors a, b, c"""
    return det3([[a[r], b[r], c[r]] for r in range(3)])


# ----------------------------------------------------------------------------------------------
# second exact model: basis 1, y, y^2 with y = 1/eta, y^3 = y^2 + i
# ----------------------------------------------------------------------------------------------

class Ky:
    def __init__(self, i):
        self.i = i
        self._pos = [(Fr(1), Fr(0), Fr(0))]   # y^0, y^1, ...
        self._neg = [(Fr(1), Fr(0), Fr(0))]   # y^0, y^-1, ...

    def mul_y(self, a):
        c0, c1, c2 = a           # c2*y^3 = c2*(y^2 + i)
        return (self.i * c2, c0, c1 + c2)

    def mul_y_inv(self, a):
        # y^{-1} = (y^2 - y)/i ;  y^{-1}*(c0 + c1 y + c2 y^2) = c0 y^{-1} + c1 + c2 y
        c0, c1, c2 = a
        q = Fr(c0) / self.i
        return (c1, c2 - q, q)

    def y_pow(self, n):
        if n >= 0:
            while len(self._pos) <= n:
                self._pos.append(self.mul_y(self._pos[-1]))
            return self._pos[n]
        while len(self._neg) <= -n:
            self._neg.append(self.mul_y_inv(self._neg[-1]))
        return self._neg[-n]

    def eta_pow(self, n):
        return self.y_pow(-n)

    def ev_eta(self, poly, shift=0):
        acc = [Fr(0), Fr(0), Fr(0)]
        for k, c in enumerate(poly):
            if c:
                e = self.eta_pow(k + shift)
                for r in range(3):
                    acc[r] += c * e[r]
        return tuple(acc)


# ----------------------------------------------------------------------------------------------
# modular arithmetic in (Z/M)[x]/(b_i)
# ----------------------------------------------------------------------------------------------

class Kmod:
    def __init__(self, i, M):
        self.i = i
        self.M = M
        self.ii = pow(i, -1, M)

    def mul(self, a, b):
        M, ii = self.M, self.ii
        a0, a1, a2 = a
        b0, b1, b2 = b
        p0 = a0 * b0
        p1 = a0 * b1 + a1 * b0
        p2 = a0 * b2 + a1 * b1 + a2 * b0
        p3 = a1 * b2 + a2 * b1
        p4 = a2 * b2
        # eta^3 = (1 - eta)/i ; eta^4 = (eta - eta^2)/i
        c0 = (p0 + p3 * ii) % M
        c1 = (p1 - p3 * ii + p4 * ii) % M
        c2 = (p2 - p4 * ii) % M
        return (c0, c1, c2)

    def mul_eta(self, a):
        c0, c1, c2 = a
        t = c2 * self.ii
        return (t % self.M, (c0 - t) % self.M, c1 % self.M)

    def pow(self, a, e):
        assert e >= 0
        r = (1 % self.M, 0, 0)
        while e:
            if e & 1:
                r = self.mul(r, a)
            a = self.mul(a, a)
            e >>= 1
        return r

    def eta(self):
        return (0, 1 % self.M, 0)

    def ev(self, poly):
        """value of the integer polynomial poly at eta"""
        acc = (0, 0, 0)
        e = (1 % self.M, 0, 0)
        for c in poly:
            if c:
                acc = tuple((acc[r] + c * e[r]) % self.M for r in range(3))
            e = self.mul_eta(e)
        return acc


def is_prime(n):
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:              # deterministic for n < 3.3e24
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def prime_factors(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def exact_order_check(i, l, P):
    """True iff eta has multiplicative order exactly P in (F_l[x]/(b_i))^x"""
    K = Kmod(i, l)
    one = (1, 0, 0)
    if K.pow(K.eta(), P) != one:
        return False
    for q in prime_factors(P):
        if K.pow(K.eta(), P // q) == one:
            return False
    return True


def disc_b(i):
    """discriminant of -i x^3 - x + 1 (a=-i, b=0, c=-1, d=1): -4ac^3 - 27a^2d^2 (b=0)"""
    a, c, d = -i, -1, 1
    return -4 * a * c ** 3 - 27 * a * a * d * d


def const_c(i, m):
    """the rational constant (-1)^{m-i+1} / (i! (m-i)! i^2) of Lemma 5"""
    return Fr((-1) ** (m - i + 1), factorial(i) * factorial(m - i) * i * i)
