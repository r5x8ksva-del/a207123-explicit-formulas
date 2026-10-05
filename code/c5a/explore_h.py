# -*- coding: utf-8 -*-
"""c5a 探索 4：h_k(t) 的结构（k<=60）。
h_k 由定义直接算：sum_m U_k(m) t^m = h_k(t)/(1-t)^{k+1}  =>  [t^i]h_k = sum_{j<=i} (-1)^{i-j} C(k+1,i-j) U_k(j)
"""
import os, sys, time
from fractions import Fraction
from math import factorial, comb, gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_fast_table


def h_from_U(T, k):
    h = []
    for i in range(0, k + 1):
        s = 0
        for j in range(0, i + 1):
            s += (-1) ** (i - j) * comb(k + 1, i - j) * T[k][j]
        h.append(s)
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


def ev(p, x):
    r = 0
    for c in reversed(p):
        r = r * x + c
    return r


def deriv(p):
    return [i * p[i] for i in range(1, len(p))]


def prim(p):
    """正比例缩放成本原整系数多项式（保持符号）。"""
    p = [Fraction(c) for c in p]
    while p and p[-1] == 0:
        p.pop()
    if not p:
        return []
    den = 1
    for c in p:
        den = den * c.denominator // gcd(den, c.denominator)
    q = [int(c * den) for c in p]
    g = 0
    for c in q:
        g = gcd(g, abs(c))
    return [c // g for c in q]


def prem_neg(a, b):
    """-(a mod b)，有理系数，结果再正比例本原化。"""
    a = [Fraction(c) for c in a]
    b = [Fraction(c) for c in b]
    while len(a) >= len(b) and any(a):
        c = a[-1] / b[-1]
        d = len(a) - len(b)
        for i, bb in enumerate(b):
            a[i + d] -= c * bb
        a.pop()
        while a and a[-1] == 0:
            a.pop()
    return prim([-c for c in a])


def sturm_real_roots(p):
    p = prim(p)
    seq = [p, prim(deriv(p))]
    while len(seq[-1]) > 1:
        r = prem_neg(seq[-2], seq[-1])
        if not r:
            break
        seq.append(r)
    def sgn_changes(vals):
        vals = [v for v in vals if v != 0]
        return sum(1 for a, b in zip(vals, vals[1:]) if (a > 0) != (b > 0))
    # at +inf: sign of leading coeff; at -inf: (-1)^deg * lc
    pinf = [s[-1] for s in seq]
    minf = [s[-1] * (-1) ** (len(s) - 1) for s in seq]
    nreal = sgn_changes(minf) - sgn_changes(pinf)
    squarefree = len(seq[-1]) == 1
    return nreal, squarefree, seq


def count_roots_in(seq, a, b):
    def V(x):
        vals = [ev(s, x) for s in seq]
        vals = [v for v in vals if v != 0]
        return sum(1 for u, w in zip(vals, vals[1:]) if (u > 0) != (w > 0))
    return V(a) - V(b)


def main():
    t0 = time.time()
    K = 60
    T = U_fast_table(K, K)
    out = []
    H = {k: h_from_U(T, k) for k in range(0, K + 1)}
    for k in range(0, 13):
        out.append('h_%d = %s' % (k, H[k]))
    # degree / leading coefficient
    def lead_pred(k):
        a, r = divmod(k, 3)
        if r == 0:
            return (-1) ** a * factorial(a)
        if r == 2:
            return (-1) ** a * factorial(a + 1)
        # r == 1: (-1)^a c(a+2,2) = (-1)^a (a+1)! H_{a+1}
        c = sum(Fraction(factorial(a + 1), i) for i in range(1, a + 2))
        return (-1) ** a * c
    okdeg = all(len(H[k]) - 1 == (2 * k) // 3 for k in range(1, K + 1))
    oklead = all(H[k][-1] == lead_pred(k) for k in range(1, K + 1))
    out.append('deg h_k = floor(2k/3) for 1<=k<=60: %s ; leading coeff formula: %s' % (okdeg, oklead))
    # U_k(-j)
    def U_neg(k, j):
        # via h: f(-j) = (-1)^k sum_{i > k-j} h_i C(i+j-1, k)
        h = H[k]
        return (-1) ** k * sum(h[i] * comb(i + j - 1, k) for i in range(len(h)) if i > k - j)
    okz = all(U_neg(k, j) == 0 for k in range(1, K + 1) for j in range(1, (k + 2) // 3 + 1))
    oknz = all(U_neg(k, (k + 2) // 3 + 1) != 0 for k in range(1, K + 1))
    out.append('U_k(-j)=0 for 1<=j<=floor((k+2)/3), and U_k(-floor((k+2)/3)-1)!=0, k<=60: %s %s' % (okz, oknz))
    # signs
    for k in range(1, K + 1):
        s = ''.join('+' if c > 0 else ('-' if c < 0 else '0') for c in H[k])
        if k <= 60:
            out.append('k=%2d deg=%2d signs %s   h(-1)=%d' % (k, len(H[k]) - 1, s, ev(H[k], -1)))
    # Sturm
    allreal = True
    rootinfo = []
    for k in range(2, K + 1):
        nreal, sqf, seq = sturm_real_roots(H[k])
        d = len(H[k]) - 1
        if nreal != d or not sqf:
            allreal = False
            out.append('  k=%d: deg=%d, distinct real roots=%d, squarefree=%s' % (k, d, nreal, sqf))
        if k in (5, 10, 20, 30, 40, 50, 60):
            neg = count_roots_in(seq, Fraction(-10 ** 9), Fraction(0))
            m1 = count_roots_in(seq, Fraction(-1), Fraction(0))
            pos01 = count_roots_in(seq, Fraction(0), Fraction(1))
            pos = count_roots_in(seq, Fraction(1), Fraction(10 ** 9))
            rootinfo.append('  k=%d: roots in (-inf,0]=%d (of which in (-1,0]=%d), (0,1]=%d, (1,inf)=%d' % (k, neg, m1, pos01, pos))
    out.append('all h_k real-rooted & squarefree, 2<=k<=60: %s' % allreal)
    out.extend(rootinfo)
    out.append('elapsed %.1fs' % (time.time() - t0))
    print('\n'.join(out))


if __name__ == '__main__':
    main()
