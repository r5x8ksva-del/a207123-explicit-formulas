# -*- coding: utf-8 -*-
"""s10-b2: two statements of the working-tree draft paper/main.tex, Section 'Sums of two families'.
  (i)  'U_k(1) = sum_s C(k+1-2s,s+1) + sum_s C(k-2-2s,s)' read with the paper's convention (all s with a
       nonzero summand, C(a,b)=0 unless 0<=b<=a) is off by one (the s=-1 term C(k+3,0)=1); with s>=0 it is right.
  (ii) [x^k] x^g u^s = C(k-g-2s-1, s-1) for s >= 1 (u = x^3/(1-x)), for a range of g, s, k.
"""
import sys
from math import comb
sys.path.insert(0, __file__.rsplit('\\', 1)[0] if '\\' in __file__ else '.')
from s10lib import P_poly, W_poly, series_div

FAIL = 0
PASS = 0


def report(name, ok, info=''):
    global FAIL, PASS
    if ok:
        PASS += 1
    else:
        FAIL += 1
    print(('PASS ' if ok else 'FAIL ') + name + (' | ' + info if info else ''), flush=True)


def C(a, b):
    return comb(a, b) if 0 <= b <= a else 0


N = 60
U1 = series_div(W_poly(1), P_poly(1), N)
all_s = [sum(C(k + 1 - 2 * s, s + 1) for s in range(-k - 10, k + 10)) + sum(C(k - 2 - 2 * s, s) for s in range(-k - 10, k + 10))
         for k in range(N + 1)]
s_ge0 = [sum(C(k + 1 - 2 * s, s + 1) for s in range(0, k + 10)) + sum(C(k - 2 - 2 * s, s) for s in range(0, k + 10))
         for k in range(N + 1)]
report('(i) with s>=0 the formula equals U_k(1), k<=60', s_ge0 == U1)
report('(i) with all s (paper convention) the formula equals U_k(1)+1 for every k<=60', all(a - b == 1 for a, b in zip(all_s, U1)),
       'differences k=0..5: %s' % [a - b for a, b in zip(all_s[:6], U1[:6])])

# (ii) coefficient of x^k in x^{g+3s} (1-x)^{-s}
ok = True
for g in range(-12, 8):
    for s in range(1, 7):
        # series of (1-x)^{-s}: C(t+s-1, s-1)
        for k in range(-40, 40):
            t = k - g - 3 * s
            lhs = comb(t + s - 1, s - 1) if t >= 0 else 0
            if lhs != C(k - g - 2 * s - 1, s - 1):
                ok = False
report('(ii) [x^k] x^g u^s = C(k-g-2s-1, s-1) for s>=1 (g in [-12,7], s<=6, |k|<40)', ok)

print('SUMMARY s10_paper_draft: PASS=%d FAIL=%d' % (PASS, FAIL))
sys.exit(1 if FAIL else 0)
