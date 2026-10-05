# -*- coding: utf-8 -*-
"""探索 7：
 (a) 容斥式 Num_q = sum_i (-1)^{q-i} C(q,i) W_{i-1} prod_{v=i}^{q-1} b_v；
 (b) gcd(Num_q, b_i) 用余式判断，q<=40；
 (c) 反转分子 R_q(y)=y^{3q-2} Num_q(1/y) 的指数母函数闭式：
     A(z)=sum_{q>=1} R_q(y) z^q/q! = (y+1)(exp(y^2 Lam)-1)/y^2 - y exp(y^2 Lam) * I(z),
     Lam = (y-1) ln(1-z) + y z/(1-z),  I(z) = int_0^{z/(1-z)} (1+w)^{y^3-y^2} e^{-y^3 w} dw.
"""
from math import comb, factorial
from fractions import Fraction
from c4lib import *

QMAX = 40
Num = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for q in range(3, QMAX + 1):
    Num[q] = padd(pmul([0, 1, 0, 2 * (q - 1)], Num[q - 1]), pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), Num[q - 2]))

# (a) IE
W = {-1: [1]}
for m in range(0, QMAX + 1):
    W[m] = padd(W[m - 1], pshift(pscale(P_poly(m - 1), m), 2))
ok = True
for q in range(1, 25):
    tot = []
    for i in range(0, q + 1):
        prod = [1]
        for v in range(i, q):
            prod = pmul(prod, b_poly(v))
        tot = padd(tot, pscale(pmul(W[i - 1], prod), (-1) ** (q - i) * comb(q, i)))
    if trim(tot) != trim(Num[q]):
        ok = False
        print('IE fail q=', q)
print('(a) IE formula q<=24:', ok)

# (b) gcd via remainders
bad = []
for q in range(1, QMAX + 1):
    if peval(Num[q], 1) == 0:
        bad.append((q, 'x=1'))
    for i in range(1, q):
        _, r = pdiv(Num[q], b_poly(i))
        if not r:
            bad.append((q, i))
        if i in (4, 18):
            s = 2 if i == 4 else 3
            lin = [1, -s]
            quad = [1, 1, 2] if i == 4 else [1, 2, 6]
            assert trim(pmul(lin, quad)) == trim(b_poly(i))
            if peval(Num[q], Fraction(1, s)) == 0:
                bad.append((q, i, 'lin'))
            _, r2 = pdiv(Num[q], quad)
            if not r2:
                bad.append((q, i, 'quad'))
print('(b) common factors of Num_q and P_{q-1}, q<=%d:' % QMAX, bad if bad else 'none')

# A000262 check
a262 = [1, 1]
for n in range(2, QMAX + 1):
    a262.append((2 * n - 1) * a262[n - 1] - (n - 1) * (n - 2) * a262[n - 2])
print('Num_q(1) == A000262(q) for q<=%d:' % QMAX, all(peval(Num[q], 1) == a262[q] for q in range(1, QMAX + 1)))
# Lah sum
def lah_sum(n):
    return sum(Fraction(factorial(n), factorial(j)) * comb(n - 1, j - 1) for j in range(1, n + 1))
print('A000262 = sum Lah, n<=20:', all(lah_sum(n) == a262[n] for n in range(1, 21)))

# (c) EGF closed form, bivariate exact series
Z = 16  # z-order
# y-polynomials: lists of Fraction, ascending powers of y
def yadd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])
def ymul(a, b):
    return pmul(a, b)
def yscale(a, c):
    return trim([c * x for x in a])
# z-series: list length Z+1 of y-polys
def sadd(A, B):
    return [yadd(A[i], B[i]) for i in range(Z + 1)]
def smul(A, B):
    C = [[] for _ in range(Z + 1)]
    for i in range(Z + 1):
        if not A[i]:
            continue
        for j in range(Z + 1 - i):
            if B[j]:
                C[i + j] = yadd(C[i + j], ymul(A[i], B[j]))
    return C
def sscale_y(A, p):
    return [ymul(a, p) if a else [] for a in A]
def sexp(A):
    """exp(A), A[0]==0."""
    assert not A[0]
    res = [[] for _ in range(Z + 1)]
    res[0] = [Fraction(1)]
    term = [list(x) for x in res]
    for r in range(1, Z + 1):
        term = smul(term, A)
        term = [yscale(t, Fraction(1, r)) if t else [] for t in term]
        res = sadd(res, term)
    return res

L = [[]] + [[Fraction(1, n)] for n in range(1, Z + 1)]          # -ln(1-z)
G = [[]] + [[Fraction(1)] for n in range(1, Z + 1)]             # z/(1-z)
# Lam = -(y-1) L + y G
Lam = sadd(sscale_y(L, [Fraction(1), Fraction(-1)]), sscale_y(G, [Fraction(0), Fraction(1)]))
y2Lam = sscale_y(Lam, [0, 0, Fraction(1)])
Ex = sexp(y2Lam)
# (Ex-1)/y^2 = sum_{r>=1} y^{2r-2} Lam^r / r!
T1 = [[] for _ in range(Z + 1)]
term = [[] for _ in range(Z + 1)]
term[0] = [Fraction(1)]
for r in range(1, Z + 1):
    term = smul(term, Lam)
    term = [yscale(t, Fraction(1, r)) if t else [] for t in term]
    T1 = sadd(T1, sscale_y(term, [0] * (2 * r - 2) + [Fraction(1)]))
T1 = sscale_y(T1, [Fraction(1), Fraction(1)])
# g_n(y): (1+w)^e e^{-y^3 w} = sum g_n w^n, e = y^3 - y^2
e = [0, 0, Fraction(-1), Fraction(1)]
binoms = [[Fraction(1)]]
for n in range(1, Z + 1):
    binoms.append(yscale(ymul(binoms[-1], yadd(e, [Fraction(-(n - 1))])), Fraction(1, n)))
expo = [yscale([0, 0, 0, Fraction(1)] if n == 1 else ymul_pow, 1) for n, ymul_pow in []] if False else None
ex3 = [[Fraction(1)]]
for n in range(1, Z + 1):
    ex3.append(yscale(ymul(ex3[-1], [0, 0, 0, Fraction(-1)]), Fraction(1, n)))
g = []
for n in range(Z + 1):
    s = []
    for i in range(n + 1):
        s = yadd(s, ymul(binoms[i], ex3[n - i]))
    g.append(s)
# I = sum_n g_n Gz^{n+1}/(n+1), Gz = z/(1-z)
I = [[] for _ in range(Z + 1)]
Gp = [list(x) for x in G]   # G^1
for n in range(0, Z):
    I = sadd(I, sscale_y(Gp, yscale(g[n], Fraction(1, n + 1))))
    Gp = smul(Gp, G)
A = sadd(T1, sscale_y(smul(Ex, I), [0, Fraction(-1)]))
ok = True
for q in range(1, Z + 1):
    Rq = list(reversed([Fraction(c) for c in Num[q]]))   # y^{3q-2} Num_q(1/y): 反转系数
    Rq = Rq + [Fraction(0)] * 0
    # Num[q] 有长度 3q-1；反转后 y^j 系数 = [x^{3q-2-j}]
    Rq = trim(Rq)
    lhs = trim([c * factorial(q) for c in A[q]]) if A[q] else []
    if lhs != Rq:
        ok = False
        print('EGF mismatch q=', q, lhs[:6], Rq[:6])
print('(c) EGF closed form matches R_q(y) for q<=%d:' % Z, ok)
print('    A[0] =', A[0])
