# -*- coding: utf-8 -*-
"""Verifier step 3: (#6) the inner sum over sigma is a rational combination of the SEQUENCE c_j(n);
(#8) Lambda_3 (allowed rows of length 3) vs Q_3 (monotone rows): chain counts and non-isomorphism."""
import os, sys
from itertools import permutations, product
from fractions import Fraction
from math import factorial, comb
import numpy as np

BASE = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(BASE, 'code'))
from core import allowed_rows, U_fast_table

# ---- #6
def cseq(j, N):
    c = [0] * (N + 1)
    for n in range(N + 1):
        c[n] = (1 if n == 0 else 0) + (c[n - 1] if n >= 1 else 0) + (j * c[n - 3] if n >= 3 else 0)
    return c
def gamma(j, s):
    return (s ** (3 * j + 3) / factorial(j) + sum((j - i) * s ** (3 * i + 1) / factorial(i) for i in range(j))) / (s * s + 3 * j)
worst = 0.0
for j in range(1, 6):
    roots = [complex(r) for r in np.roots([1, -1, 0, -j])]
    c = cseq(j, 200)
    cc = lambda n: c[n] if n >= 0 else 0
    for n in range(0, 40):
        lhs = sum(gamma(j, s) * s ** n for s in roots)
        rhs = Fraction(cc(n + 3 * j), factorial(j)) + sum(Fraction(j - i, factorial(i)) * cc(n + 3 * i - 2) for i in range(j))
        worst = max(worst, abs(lhs - float(rhs)) / max(1.0, abs(float(rhs))))
print(f'#6: sum_sigma gamma_j(sigma) sigma^n == c_j(n+3j)/j! + sum_(i<j) (j-i)/i! c_j(n+3i-2)  (1<=j<=5, 0<=n<40): max rel dev {worst:.1e}')

# ---- #8
L3 = list(allowed_rows(3))
Q3 = [(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1), (0, 0, 1), (0, 1, 1)]
def leq(a, b):
    return all(x <= y for x, y in zip(a, b))
def chains(P):
    bot, top = (0, 0, 0), (1, 1, 1)
    res = {}
    def rec(cur, q):
        if cur == top:
            res[q] = res.get(q, 0) + 1
            return
        for y in P:
            if y != cur and leq(cur, y):
                rec(y, q + 1)
    rec(bot, 0)
    return [res.get(q, 0) for q in range(1, 4)]
def iso(P, Q):
    for perm in permutations(Q):
        f = dict(zip(P, perm))
        if all(leq(a, b) == leq(f[a], f[b]) for a in P for b in P):
            return True
    return False
print('#8: Lambda_3 =', L3)
print('    chain counts 0^->1^ with 1,2,3 steps: Lambda_3', chains(L3), ' Q_3', chains(Q3))
print('    Lambda_3 isomorphic to Q_3 (all 720 bijections tried):', iso(L3, Q3))
T = U_fast_table(3, 20)
print('    Z(Q_3,m+1)=sum_q b_q C(m+1,q) equals U_3(m) for m<=20:',
      all(sum(b * comb(m + 1, q) for q, b in zip(range(1, 4), chains(Q3))) == T[3][m] for m in range(21)))
