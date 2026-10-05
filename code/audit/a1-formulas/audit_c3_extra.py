# -*- coding: utf-8 -*-
"""审计 a1-formulas：T3.2 中 ℒ_s[e^{jus}(e^{us}-1)^n/n!]=u^n/prod_{i=j}^{j+n}(1-iu)（按 u 展开到 u^25）。"""
import time
from fractions import Fraction
from math import factorial, comb
from common import *  # noqa

t0 = time.time()
NU = 26
ok = True
for j in range(0, 7):
    for n in range(0, 7):
        # e^{jz}(e^z-1)^n/n! 的 z^N 系数 × N!，即 ℒ_s 后 u^N 的系数
        lhs = []
        for N in range(NU):
            # [z^N] e^{jz}(e^z-1)^n/n! = (1/n!) Σ_i (-1)^{n-i} C(n,i) (j+i)^N / N!
            v = Fraction(sum((-1) ** (n - i) * comb(n, i) * (j + i) ** N for i in range(n + 1)), factorial(n))
            lhs.append(v)
        den = [1]
        for i in range(j, j + n + 1):
            den = pmul(den, [1, -i])
        rhs = smul(pshift([1], n), sinv(den, NU), NU)
        if any(lhs[N] != rhs[N] for N in range(NU)):
            ok = False
report(ok, 'T3.2.Ls-identity', 'ℒ_s[e^{jus}(e^{us}-1)^n/n!]=u^n/prod_{i=j}^{j+n}(1-iu)，0<=j,n<=6，到 u^25')
summary('audit_c3_extra')
print('elapsed %.1fs' % (time.time() - t0))
