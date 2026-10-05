# -*- coding: utf-8 -*-
"""c5b 探索：U_k(m) 作为 m 的多项式（由 N_brute 的二项式基精确给出），并找有理根，便于在笔记里写出显式形式。"""
import os, sys
from fractions import Fraction
from math import factorial
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import N_brute, U_fast_column
from polylib import pmul, padd, pscale, trim, pdiv

def binom_poly(q, shift):
    p = [Fraction(1)]
    for i in range(q):
        p = pmul(p, [Fraction(shift - i), Fraction(1)])
    return pscale(p, Fraction(1, factorial(q)))

for k in range(1, 9):
    Nk = N_brute(k)
    p = []
    for q, v in Nk.items():
        p = padd(p, pscale(binom_poly(q, 1), Fraction(v)))
    p = trim(p)
    # 检查
    col = [U_fast_column(m, k)[k] for m in range(0, 12)]
    ev = []
    for m in range(12):
        s = Fraction(0)
        for c in reversed(p):
            s = s * m + c
        ev.append(s)
    assert ev == col
    # 提取有理根 m=-1,-2,-3,... 以及 -1/2 等小分母
    rem = p[:]
    roots = []
    for r in [Fraction(-1), Fraction(-2), Fraction(-3), Fraction(-1, 2), Fraction(-3, 2)]:
        while True:
            q_, r_ = pdiv(rem, [-r, 1])
            if r_ == [] or all(x == 0 for x in r_):
                roots.append(r); rem = q_
            else:
                break
    lead = p[-1]
    print('k=%d N=%s' % (k, [Nk[q] for q in sorted(Nk)]))
    print('   U_k(m) coeffs (ascending, x k!):', [str(c * factorial(k)) for c in p])
    print('   rational roots found:', [str(r) for r in roots], ' remaining factor (x k!/lead...):', [str(c * factorial(k)) for c in rem])
