# -*- coding: utf-8 -*-
"""s17-b9b：精确的实根计数（复核者自写，不 import 项目代码）。
  desc_count(h,a,b)   Descartes 上界：(1+x)^d h((a+bx)/(1+x)) 的系数变号数 >= (a,b) 中的根数（同奇偶）；对实根多项式取等
  sign_at(h,p,q)      h(p/q) 的符号（精确整数）
  ivt_count(h,pts)    在严格递增的有理点列上数 h 的变号次数：每个变号区间至少一个根（介值定理），所以是 (pts[0],pts[-1]) 中根数的下界
下界 = 上界时计数精确，不依赖 A19（实根性）；所有区间加起来数到 deg h 个根时，顺带证明 h 全实根、根互异。
"""
from fractions import Fraction as Fr


def taylor_shift(c, a):
    """c(x+a) 的系数（c[i] 为 x^i 的系数，a 为整数）。"""
    c = list(c)
    n = len(c)
    if a == 0:
        return c
    for i in range(n - 1):
        for j in range(n - 2, i - 1, -1):
            c[j] += a * c[j + 1]
    return c


def desc_count(h, a, b):
    """(a,b) 中根数的 Descartes 上界（a<b 为有理数）。"""
    a, b = Fr(a), Fr(b)
    assert a < b
    d = len(h) - 1
    M = a.denominator * b.denominator // _gcd(a.denominator, b.denominator)
    A = int(a * M)
    B = int(b * M)
    # H(z)=Σ h_i M^{d-i} z^i，则 M^d h(z/M)=H(z)；q(y)=H(A+(B-A)y)
    H = [h[i] * M ** (d - i) for i in range(d + 1)]
    S = taylor_shift(H, A)
    c = B - A
    q = [S[j] * c ** j for j in range(d + 1)]
    r = q[::-1]
    P = taylor_shift(r, 1)
    sg = [1 if v > 0 else -1 for v in P if v != 0]
    return sum(1 for u, v in zip(sg, sg[1:]) if u != v)


def _gcd(x, y):
    while y:
        x, y = y, x % y
    return x


def sign_at(h, x):
    """h(x) 的符号，x 为有理数（精确）。分母是 2 的幂时走移位的 Horner（快），否则走一般整数算法。"""
    x = Fr(x)
    p, q = x.numerator, x.denominator
    if q & (q - 1) == 0:
        e = q.bit_length() - 1
        # q^d h(p/q)=Σ_i h_i p^i q^{d-i}：对 Q=2^e 做 Horner，系数 h_i p^i
        acc = 0
        pp = 1
        for i in range(len(h)):
            acc = (acc << e) + h[i] * pp
            pp *= p
        return (acc > 0) - (acc < 0)
    d = len(h) - 1
    acc = 0
    qp = 1
    # Σ h_i p^i q^{d-i}：从低次到高次，acc 累加 h_i p^i q^{d-i}
    pw = [1] * (d + 1)
    for i in range(1, d + 1):
        pw[i] = pw[i - 1] * p
    qpw = [1] * (d + 1)
    for i in range(1, d + 1):
        qpw[i] = qpw[i - 1] * q
    for i in range(d + 1):
        acc += h[i] * pw[i] * qpw[d - i]
    return (acc > 0) - (acc < 0)


def ivt_count(h, pts):
    """严格递增有理点列上的变号次数（遇到恰好为零的点时报错，由调用方换点）。"""
    sg = []
    for x in pts:
        s = sign_at(h, x)
        if s == 0:
            raise ValueError('h vanishes at %s' % x)
        sg.append(s)
    return sum(1 for u, v in zip(sg, sg[1:]) if u != v), sg
