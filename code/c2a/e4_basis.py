# -*- coding: utf-8 -*-
"""探索 4：Q(x) = Q(u) + Q(u)x + Q(u)x^2（u = x^3/(1-x)），把 G_m 写成 (a + b x + c x^2)/D_m(u)，看系数是否有好结构。"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c2a_lib import *  # noqa
from core import U_fast_table
from polylib import P_poly, pmul, padd, pscale, pshift, trim


def umul(p, q):
    return pmul(p, q)


def emul(A, B):
    """A,B = [p0,p1,p2]（u 的整系数多项式），乘积并用 x^3 = u - u x 约化。"""
    t = [[] for _ in range(5)]
    for i in range(3):
        for j in range(3):
            t[i + j] = padd(t[i + j], umul(A[i], B[j]))
    r0, r1, r2 = t[0], t[1], t[2]
    # x^3 -> u - u x ; x^4 -> u x - u x^2
    r0 = padd(r0, pshift(t[3], 1))
    r1 = padd(r1, pscale(pshift(t[3], 1), -1))
    r1 = padd(r1, pshift(t[4], 1))
    r2 = padd(r2, pscale(pshift(t[4], 1), -1))
    return [trim(r0), trim(r1), trim(r2)]


def from_xpoly(p):
    """x 的多项式 -> 基表示。"""
    res = [[], [], []]
    xp = [[1], [], []]          # x^0
    X = [[], [1], []]
    for c in p:
        if c:
            res = [padd(res[i], pscale(xp[i], c)) for i in range(3)]
        xp = emul(xp, X)
    return res


inv1mx = [[1, 1], [1], [1]]      # (1-x)^{-1} = 1 + u + x + x^2
# 自检
chk = emul(from_xpoly([1, -1]), inv1mx)
print('(1-x)(1+u+x+x^2) =', chk)

def W_poly(m):
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
    return W

for m in range(0, 7):
    E = from_xpoly(W_poly(m))
    for _ in range(m + 1):
        E = emul(E, inv1mx)
    D = [1]
    for i in range(1, m + 1):
        D = pmul(D, [1, -i])
    print('m=%d  D=%s' % (m, D))
    for nm, p in zip('abc', E):
        print('   %s(u) =' % nm, p)
