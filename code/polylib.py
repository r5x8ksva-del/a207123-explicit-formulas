# -*- coding: utf-8 -*-
"""精确有理系数多项式 / 截断幂级数小工具（只用 fractions，不依赖 sympy）。

多项式用系数列表表示：p[i] 是 x^i 的系数（Fraction 或 int），末尾零会被去掉。
"""
from fractions import Fraction


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def psub(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(n)])


def pscale(p, c):
    return trim([c * a for a in p])


def pmul(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            r[i + j] += a * b
    return trim(r)


def pshift(p, k):
    """乘 x^k（k>=0）。"""
    return trim([0] * k + list(p)) if p else []


def peval(p, x):
    r = 0
    for a in reversed(p):
        r = r * x + a
    return r


def pdiv(p, q):
    """多项式带余除法（有理系数）：返回 (商, 余)。"""
    p = [Fraction(a) for a in trim(p)]
    q = [Fraction(a) for a in trim(q)]
    if not q:
        raise ZeroDivisionError
    out = [Fraction(0)] * max(len(p) - len(q) + 1, 0)
    while len(p) >= len(q) and p:
        c = p[-1] / q[-1]
        d = len(p) - len(q)
        out[d] = c
        for i, b in enumerate(q):
            p[i + d] -= c * b
        p = trim(p)
    return trim(out), p


def pgcd(p, q):
    """首一 gcd（有理系数）。"""
    a, b = trim(p), trim(q)
    while b:
        _, r = pdiv(a, b)
        a, b = b, r
    if not a:
        return []
    lead = Fraction(a[-1])
    return [Fraction(c) / lead for c in a]


def pderiv(p):
    return trim([i * p[i] for i in range(1, len(p))])


def series_inv(p, n):
    """1/p 的前 n 项（要求 p[0] != 0）。"""
    p = list(p) + [0] * max(0, n - len(p))
    inv0 = Fraction(1) / Fraction(p[0])
    r = [Fraction(0)] * n
    r[0] = inv0
    for k in range(1, n):
        s = 0
        for i in range(1, k + 1):
            if p[i]:
                s += p[i] * r[k - i]
        r[k] = -s * inv0
    return r


def series_mul(a, b, n):
    r = [0] * n
    for i, x in enumerate(a[:n]):
        if x == 0:
            continue
        for j in range(0, min(len(b), n - i)):
            r[i + j] += x * b[j]
    return r


def interpolate(xs, ys):
    """Newton 插值，返回 Fraction 系数多项式（按 x 的升幂）。"""
    n = len(xs)
    coef = [Fraction(y) for y in ys]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (xs[i] - xs[i - j])
    # 展开 Newton 形式
    poly = [Fraction(0)]
    for i in range(n - 1, -1, -1):
        poly = pmul(poly, [-xs[i], 1]) if poly != [Fraction(0)] else []
        poly = padd(poly, [coef[i]])
    return trim(poly)


def P_poly(m):
    """P_m(x) = prod_{i=0}^m (1 - x - i x^3)；m=-1 时为 1。"""
    p = [1]
    for i in range(0, m + 1):
        p = pmul(p, [1, -1, 0, -i])
    return p


def b_poly(i):
    """b_i(x) = 1 - x - i x^3。"""
    return trim([1, -1, 0, -i])
