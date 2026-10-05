# -*- coding: utf-8 -*-
"""Verifier step 2: findings #2 and #3 (C-4).
 - #2: recompute p_d by interpolation of DP data (independent of check_c4.py), and for each integer
       shift c in a window check that the expansion p_d(k)=sum_j h_j C(k+c-j,2d) has a negative h_j.
       Also check whether anything in the repo proves the claim for d>8 (the Fujiwara bound grows with d).
 - #3: compare the exception values below the threshold for d<=12 with notes/c4.md Table 2 (d<=5)
       and with logs/c4_explore1.log (d<=12)."""
import os, sys, re, ast
from fractions import Fraction
from math import comb, factorial

BASE = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(BASE, 'code'))
from core import U_fast_table, N_from_U

K, M = 60, 61
T = U_fast_table(K, M)
def D(k, d):
    q = k - d
    if q < 0 or k < 0:
        return 0
    return N_from_U(T, k, q)

def interp(xs, ys):
    n = len(xs)
    coeffs = [Fraction(0)] * n
    for i in range(n):
        num = [Fraction(1)]
        den = Fraction(1)
        for j in range(n):
            if j == i:
                continue
            num = [Fraction(0)] + num
            for t in range(len(num) - 1):
                num[t] -= xs[j] * num[t + 1]
            den *= (xs[i] - xs[j])
        for t in range(n):
            coeffs[t] += Fraction(ys[i]) * num[t] / den
    while len(coeffs) > 1 and coeffs[-1] == 0:
        coeffs.pop()
    return coeffs
def pv(p, x):
    r = Fraction(0)
    for c in reversed(p):
        r = r * x + c
    return r

PD = {}
for d in range(0, 13):
    xs = [Fraction(k) for k in range(2 * d + 2, 4 * d + 3)]
    ys = [D(int(k), d) for k in xs]
    p = interp(xs, ys)
    assert len(p) - 1 == 2 * d
    for k in range(2 * d + 2, K + 1):
        assert pv(p, k) == D(k, d), (d, k)
    PD[d] = p
print('p_d (d<=12) interpolated from DP, agree with D(k,d) on 2d+2<=k<=60')

# ---- #2
print('\n==== #2: negative coefficient in every integer shift of the basis C(k+c-j,2d) ====')
for d in range(1, 7):
    n = 2 * d
    p = PD[d]
    allneg = True
    for c in range(-300, 301):
        s = 2 * d - c   # f(k)=p(k+s), h_j = sum_i (-1)^i C(2d+1,i) f(j-i)
        h = [sum((-1) ** i * comb(n + 1, i) * pv(p, j - i + s) for i in range(j + 1)) for j in range(n + 1)]
        if min(h) >= 0:
            allneg = False
            print('   d', d, 'c', c, 'all h_j >= 0 :', h)
    print(f'd={d}: every integer shift c in [-300,300] has some h_j<0: {allneg}')

def poly_binom(x, r):
    num = Fraction(1)
    for i in range(r):
        num *= (x - i)
    return num / factorial(r)
# verify the expansion identity itself for d=2, a few c
d = 2; n = 4; p = PD[d]
for c in (-5, 0, 3, 11):
    s = 2 * d - c
    h = [sum((-1) ** i * comb(n + 1, i) * pv(p, j - i + s) for i in range(j + 1)) for j in range(n + 1)]
    for k in range(-10, 30):
        assert sum(h[j] * poly_binom(Fraction(k + c - j), n) for j in range(n + 1)) == pv(p, k)
print('expansion identity p_d(k)=sum_j h_j C(k+c-j,2d) (polynomial binomials) verified for d=2, c in {-5,0,3,11}, -10<=k<30')

# Fujiwara bound size of h_1(s) for d up to 12 (how many shifts a computer-aided proof would need to scan)
print('\nFujiwara bound for h_1(s) = p_d(s+1)-(2d+1)p_d(s) (scan window size), d=1..12:')
for d in range(1, 13):
    p = PD[d]
    n = 2 * d
    # h1 as polynomial in s: p(s+1) - (2d+1) p(s)
    # compute coefficients by interpolation
    xs = [Fraction(x) for x in range(0, n + 1)]
    ys = [pv(p, x + 1) - (n + 1) * pv(p, x) for x in xs]
    h1 = interp(xs, ys)
    lead = h1[-1]
    nn = len(h1) - 1
    bmax = 0
    for i in range(1, nn + 1):
        r = abs(h1[nn - i] / lead)
        if i == nn:
            r = r / 2
        b = 0
        while Fraction(b) ** i < r:
            b += 1
        bmax = max(bmax, b)
    print(f'  d={d:2d}: deg h_1={nn}, lead={lead} (<0: {lead < 0}), scan |s|<={2 * bmax + 1}')

# ---- #3
print('\n==== #3: exception values below threshold ====')
exc = {}
for d in range(0, 13):
    exc[d] = [(k, D(k, d), pv(PD[d], k)) for k in range(d + 1, 2 * d + 2)]
    assert all(Dv != pk for (_, Dv, pk) in exc[d]), d
print('d<=12: every k in [d+1,2d+1] is an exception (D != p_d):', True)
# Table 2 of notes/c4.md
c4md = open(os.path.join(BASE, 'notes', 'c4.md'), encoding='utf-8').read()
tab2 = c4md.split('**表 2')[1].split('**表 3')[0]
ds_in_tab2 = sorted(set(int(x) for x in re.findall(r'^- d=(\d+)：', tab2, re.M)))
print('d values listed in notes/c4.md Table 2:', ds_in_tab2)
# compare Table 2 entries
ok = True
for line in tab2.splitlines():
    mt = re.match(r'^- d=(\d+)：(.*)$', line)
    if not mt:
        continue
    d = int(mt.group(1))
    for k, Dv, pk, ev in re.findall(r'k=(\d+): (−?\d+) / (−?\d+) / (−?\d+)', mt.group(2)):
        k = int(k); Dv = int(Dv.replace('−', '-')); pk = int(pk.replace('−', '-')); ev = int(ev.replace('−', '-'))
        if (k, Dv, pk) not in [(a, b, int(c)) for (a, b, c) in exc[d]] or ev != Dv - pk:
            ok = False
            print('   Table 2 mismatch', d, k, Dv, pk, ev)
print('Table 2 entries agree with recomputation:', ok)
# explore1 log
log = open(os.path.join(BASE, 'logs', 'c4_explore1.log'), encoding='utf-8').read().splitlines()
cur = None
found = {}
for line in log:
    mt = re.match(r'^d=(\d+) deg=', line)
    if mt:
        cur = int(mt.group(1))
    if 'exceptions (k, D, p(k))' in line and cur is not None:
        lst = ast.literal_eval(line.split(':', 1)[1].strip())
        found[cur] = [(a, b, Fraction(c)) for (a, b, c) in lst]
print('d values with exception lists in logs/c4_explore1.log:', sorted(found))
print('explore1 lists agree with recomputation for all those d:', all(found[d] == [(a, b, c) for (a, b, c) in exc[d]] for d in found))
