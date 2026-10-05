# -*- coding: utf-8 -*-
"""探索 10：生成 c4.md 用的表格（全部由精确计算得到，避免手抄错误）。"""
from math import factorial, comb
from fractions import Fraction
from c4lib import *
from explore4_patterns import pattern_counts

KR = 140
NR = N_table_rec(KR)
DMAX = 12


def fit(d):
    ks = list(range(KR - 2 * d, KR + 1))
    return interpolate(ks, [Dval(NR, k, d) for k in ks])


P = {d: fit(d) for d in range(DMAX + 1)}

print('## p_d(k) * 2^d d!  (integer coefficients, descending powers of k)')
for d in range(DMAX + 1):
    den = 2 ** d * factorial(d)
    cs = [P[d][i] * den for i in range(len(P[d]))]
    assert all(c.denominator == 1 for c in cs)
    print('d=%d den=%d :' % (d, den), [int(c) for c in reversed(cs)])

print('\n## exceptions: k, D(k,d), p_d(k), e_d(k) for 0<=k<=2d+1')
for d in range(0, 6):
    rows = []
    for k in range(0, 2 * d + 2):
        Dk = Dval(NR, k, d)
        pk = pval(P[d], k)
        rows.append((k, Dk, int(pk), int(Dk - pk)))
    print('d=%d' % d, rows)

print('\n## Newton coefficients at base 2d+2 and 2d+1')
for d in range(DMAX + 1):
    for base in (2 * d + 2, 2 * d + 1):
        vals = [pval(P[d], base + i) for i in range(2 * d + 1)]
        diffs = []
        row = vals[:]
        for i in range(2 * d + 1):
            diffs.append(int(row[0]))
            row = [row[j + 1] - row[j] for j in range(len(row) - 1)]
        print('d=%d base=%d:' % (d, base), diffs)

print('\n## pattern counts M(d; sigma, beta)')
for d in range(0, 7):
    M = pattern_counts(d)
    bet = sorted(set(b for s, b in M))
    for b in bet:
        row = {s: w for (s, bb), w in M.items() if bb == b}
        print('d=%d beta=%d:' % (d, b), sorted(row.items()))
    print('   total', sum(M.values()))

# numerators
QMAX = 12
Num = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for q in range(3, QMAX + 1):
    Num[q] = padd(pmul([0, 1, 0, 2 * (q - 1)], Num[q - 1]), pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), Num[q - 2]))
print('\n## Num_q coefficient lists (ascending from x^0)')
for q in range(1, 9):
    print(q, Num[q])
