# -*- coding: utf-8 -*-
"""final-audit / math-c1c2 / a5 : T2.5 forms, the m=1,k=3 counterexample, R_k, and the numbers on the
formula page 07 (term counts, digit counts, cancellation size), plus a rough own timing for T2.9's order of
magnitude.  No import of core/polylib."""
import sys, os, time
from fractions import Fraction as Fr
from math import factorial
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mylib import *

T0 = time.time()
NPASS = NFAIL = 0


def rep(ok, cid, msg):
    global NPASS, NFAIL
    NPASS += bool(ok)
    NFAIL += (not ok)
    print(('PASS ' if ok else 'FAIL ') + cid + ' ' + msg, flush=True)


S = stirling2(400)


def H(m, s, j):
    return h_complete(s, j, m) if s >= 0 else 0


# ---------------------------------------------------------------- forms vs DP
KF, MF = 45, 12
cols = {m: dp_total(m, KF + 2) for m in range(0, MF + 1)}
csers = {i: c_series(i, KF + 3 * MF + 10) for i in range(0, MF + 1)}


def cval(i, n):
    return csers[i][n] if n >= 0 else 0


def Theta(t, n, m):
    v = Fr(sum((-1) ** r * C(t, r) * cval(m - r, n) for r in range(t + 1)), factorial(t))
    return v


bad = {'F3': [], 'Theta': [], 'F4': [], 'Hc': []}
for m in range(0, MF + 1):
    for k in range(0, KF + 1):
        U = cols[m][k]
        f3 = sum(S[m + s][m] * C(k + 1 + m - 2 * s, m + s) for s in range(0, k + 2)) - sum(
            H(m, s, j) * C(k + m - j - 2 * s, m - j + s) for j in range(1, m + 1) for s in range(0, k + 1))
        if f3 != U:
            bad['F3'].append((k, m))
        th = Theta(m, k + 1 + 3 * m, m) - sum(Theta(t, k + 3 * t, m) for t in range(0, m))
        if th != U:
            bad['Theta'].append((k, m))
        f4 = sum((-1) ** (m - i) * C(m, i) * (cval(i, k + 3 * m) + sum(j * falling(i, j) * cval(i, k + 3 * m - 3 * j - 2)
                                                                       for j in range(1, i + 1))) for i in range(0, m + 1))
        if f4 != factorial(m) * U:
            bad['F4'].append((k, m))
        # Theta_t(n+3t) = sum_s H(m,s,m-t) C(n+t-2s, n-3s)
        for t in range(0, m + 1):
            for n in range(0, 12):
                if Theta(t, n + 3 * t, m) != sum(H(m, s, m - t) * C(n + t - 2 * s, n - 3 * s) for s in range(0, n // 3 + 1)):
                    bad['Hc'].append((t, n, m))
rep(not any(bad.values()), 'T2.5.forms', 'F3, Theta (incl. k=0), F4 (m! U) == DP for 0<=k<=%d, 0<=m<=%d; Theta_t(n+3t)=sum_s H(m,s,m-t)C(n+t-2s,n-3s) (n<12); bad=%s'
    % (KF, MF, {a: b[:2] for a, b in bad.items() if b}))

# counterexample m=1,k=3
m, k = 1, 3
th_terms = (Theta(1, k + 1 + 3, 1), -Theta(0, k + 3 * 0, 1))
H_terms = (sum(S[m + s][m] * C(k + m - 2 * s, k - 3 * s) for s in range(0, 3)),
           1 * sum(H(1, s, 1) * C(k - 2 + m - 1 - 2 * s, k - 2 - 3 * s) for s in range(0, 3)))
rep(th_terms == (8, -2) and H_terms == (5, 1) and sum(th_terms) == 6 == sum(H_terms) == cols[1][3],
    'T2.5.cex', 'm=1,k=3: Theta-type terms %s, H-type terms %s, both sum to U_3(1)=6' % (th_terms, H_terms))

# R_k = c_1(k+3) + c_1(k-2) - 1
ok = all(cols[1][k] == cval(1, k + 3) + cval(1, k - 2) - 1 for k in range(0, KF + 1))
rep(ok, 'T2.5.Rk', 'R_k = c_1(k+3)+c_1(k-2)-1, 0<=k<=%d (c_1(n)=0 for n<0)' % KF)

# F4 congruence W_m == 1 + sum_{j<=i} j i^(j) x^{3j+2} (mod b_i), and P_{j-1} == i^(j) x^{3j}
from fractions import Fraction


def polymod_b(poly, i):
    a = [Fraction(c) for c in poly]
    for n in range(len(a) - 1, 2, -1):
        c = a[n]
        if c:
            a[n] = Fraction(0)
            a[n - 3] += c / i
            a[n - 2] -= c / i
    a = a[:3] + [Fraction(0)] * max(0, 3 - len(a))
    return a[:3]


ok = True
for i in range(1, 12):
    for j in range(1, 14):
        mono = [0] * (3 * j) + [falling(i, j)]
        if polymod_b(P_poly(j - 1), i) != polymod_b(mono, i):
            ok = False
rep(ok, 'T2.5.F4cong', 'P_{j-1} == i^(j) x^{3j} (mod b_i), 1<=i<=11, 1<=j<=13 (so W_m == W~_i mod b_i for m>=i)')

# ---------------------------------------------------------------- 07: digits and cancellation at k=m=100
k = m = 100
U100 = dp_total(100, 100)[100]
H100 = sum(S[m + s][m] * C(k + m - 2 * s, k - 3 * s) for s in range(0, k // 3 + 1)) + sum(
    j * sum(H(m, s, j) * C(k - 2 + m - j - 2 * s, k - 2 - 3 * s) for s in range(0, (k - 2) // 3 + 1)) for j in range(1, m + 1))
csers = {i: c_series(i, k + 3 * m + 5) for i in range(0, m + 1)}
maxTheta = 0
for t in range(0, m + 1):
    n = k + 1 + 3 * m if t == m else k + 3 * t
    for r in range(0, t + 1):
        maxTheta = max(maxTheta, abs(C(t, r) * csers[m - r][n]))
maxF4 = 0
for i in range(0, m + 1):
    maxF4 = max(maxF4, C(m, i) * csers[i][k + 3 * m])
    for j in range(1, i + 1):
        nn = k + 3 * m - 3 * j - 2
        if nn >= 0:
            maxF4 = max(maxF4, C(m, i) * j * falling(i, j) * csers[i][nn])
print('# k=m=100: digits(U)=%d, digits max Theta single term (C(t,r) c_{m-r}(n), before /t!)=%d, digits max F4 single term=%d'
      % (len(str(U100)), len(str(maxTheta)), len(str(maxF4))))
rep(len(str(U100)) == 99 and H100 == U100 and len(str(maxTheta)) == 289,
    '07.digits', 'U_100(100) has 99 digits (H-type == DP); largest Theta single term before dividing by t! has 289 digits (F4: %d)' % len(str(maxF4)))

# ---------------------------------------------------------------- 07: term counts
def count_H(k, m):
    n1 = sum(1 for s in range(0, k // 3 + 1) if S[m + s][m] * C(k + m - 2 * s, k - 3 * s) != 0)
    n2 = sum(1 for j in range(1, m + 1) for s in range(0, (k - 2) // 3 + 1) if H(m, s, j) * C(k - 2 + m - j - 2 * s, k - 2 - 3 * s) != 0)
    return n1 + n2


def count_Theta(k, m):
    ncv = sum(t + 1 for t in range(0, m + 1))
    nexp = 0
    for t in range(0, m + 1):
        n = k + 1 + 3 * m if t == m else k + 3 * t
        nexp += (t + 1) * (n // 3 + 1)
    return ncv, nexp


for (k, m) in ((60, 20), (100, 100), (30, 12), (300, 30), (30, 300)):
    nh = count_H(k, m)
    ncv, nexp = count_Theta(k, m)
    print('# (k,m)=(%d,%d): H terms=%d vs (m+1)k/3=%.0f | Theta c-values=%d vs m^2/2=%.0f | Theta expanded=%d vs m^2k/6+m^3/3=%.0f'
          % (k, m, nh, (m + 1) * k / 3, ncv, m * m / 2, nexp, m * m * k / 6 + m ** 3 / 3))
nh = count_H(60, 20); ncv, _ = count_Theta(60, 20)
nh2 = count_H(100, 100); ncv2, nexp2 = count_Theta(100, 100)
rep(nh == 421 and ncv == 231 and nh2 == 3334 and ncv2 == 5151, '07.counts', 'H terms 421 (60,20), 3334 (100,100); Theta c-values 231, 5151 (as in notes/c2a.md 7.1)')

# ---------------------------------------------------------------- rough own timing (order of magnitude only)
K, M = 200, 30
t = time.time()
Ul = [[0] * (M + 1) for _ in range(K + 1)]
for kk in range(0, K + 1):
    for mm in range(0, M + 1):
        if kk == 0:
            Ul[kk][mm] = 1
            continue
        v = (Ul[kk][mm - 1] if mm >= 1 else 0) + Ul[kk - 1][mm]
        if kk >= 3:
            v += mm * Ul[kk - 3][mm]
        elif kk == 2:
            v += mm
        Ul[kk][mm] = v
t_l1 = time.time() - t
t = time.time()
# H table via recurrence: Hs[m][j][s]
Ht = {}
for mm in range(0, M + 1):
    tab = [[0] * (K // 3 + 2) for _ in range(mm + 2)]
    tab[mm + 1][0] = 1
    for j in range(mm, -1, -1):
        for s in range(0, K // 3 + 2):
            tab[j][s] = tab[j + 1][s] + (j * tab[j][s - 1] if s >= 1 else 0)
    Ht[mm] = tab
UH = [[0] * (M + 1) for _ in range(K + 1)]
for kk in range(0, K + 1):
    for mm in range(0, M + 1):
        tab = Ht[mm]
        v = sum(tab[0][s] * C(kk + mm - 2 * s, kk - 3 * s) for s in range(0, kk // 3 + 1))
        for j in range(1, mm + 1):
            v += j * sum(tab[j][s] * C(kk - 2 + mm - j - 2 * s, kk - 2 - 3 * s) for s in range(0, (kk - 2) // 3 + 1))
        UH[kk][mm] = v
t_h = time.time() - t
ok = UH == Ul and all(Ul[kk][mm] == dp_total(mm, K)[kk] for mm in (0, 7, 30) for kk in (0, 5, 199, 200))
print('# own timing K=200,M=30: lemma-1 %.4fs, H-type (recurrence atoms) %.3fs, ratio %.0f' % (t_l1, t_h, t_h / max(t_l1, 1e-9)))
rep(ok, 'T2.9.own_timing', 'own run: lemma-1 table == H-type table (K=200,M=30); ratio H/lemma-1 = %.0f (order-of-magnitude corroboration only)' % (t_h / max(t_l1, 1e-9)))

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY a5 pass=%d fail=%d' % (NPASS, NFAIL))
