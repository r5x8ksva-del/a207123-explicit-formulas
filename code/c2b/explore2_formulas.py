# -*- coding: utf-8 -*-
"""探索 2：细化 DP 与各公式核对（k<=K, m<=M）。"""
import sys, os, time
from fractions import Fraction
from itertools import product
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))
from formulas import *
from blocks import dfs_legal, ascents, parse_det
import core
from polylib import P_poly, series_inv, series_mul, padd, pshift, pscale, pmul, trim

K, M = int(sys.argv[1]) if len(sys.argv) > 1 else 30, int(sys.argv[2]) if len(sys.argv) > 2 else 12
t0 = time.time()
T = core.U_fast_table(K + 1, M)
DP = {m: refined_dp(K + 1, m) for m in range(M + 1)}
print('DP built %.1fs' % (time.time() - t0))

def rep(name, ok):
    print(('PASS ' if ok else 'FAIL ') + name)

# 1. DP totals vs core
ok = all(sum(DP[m][0][k]) == T[k][m] for m in range(M + 1) for k in range(K + 2))
rep('refined DP totals == core.U_fast_table, k<=%d m<=%d' % (K + 1, M), ok)

# 2. DP vs DFS enumeration (s-refined, ending type)
ok = True
for m in range(0, 4):
    for k in range(0, 10):
        L = dfs_legal(k, m)
        tot = [0] * (k + 3); asc = [0] * (k + 3)
        for h in L:
            s = ascents(h)
            tot[s] += 1
            if k >= 2 and h[-2] < h[-1]:
                asc[s] += 1
        for s in range(k + 3):
            if tot[s] != DP[m][0][k][s] or asc[s] != DP[m][1][k][s]:
                ok = False
rep('refined DP == DFS enumeration (s, ending), k<=9 m<=3', ok)

# 3. complete part single term, E part
okA = okE = True
for m in range(M + 1):
    tot, asc = DP[m]
    for k in range(K + 1):
        for s in range(len(tot[k])):
            comp = tot[k][s] - asc[k][s]
            if comp != A_complete(k, m, s):
                okA = False
            if asc[k][s] != E_asc(k, m, s):
                okE = False
rep('complete (non-ascent-ending) with s ascents == S(m+s,m)C(k+m-2s,k-3s), k<=%d m<=%d' % (K, M), okA)
rep('ascent-ending with s ascents == sum_j j H(m,s-1,j) C(k+m-j-2s,k+1-3s), k<=%d m<=%d' % (K, M), okE)

# 4. U explicit
ok = all(U_explicit(k, m) == T[k][m] for m in range(M + 1) for k in range(K + 1))
rep('U_k(m) explicit double sum == core DP, k<=%d m<=%d' % (K, M), ok)

# 5. U = A(k+1) - sum_j A^{(j)}(k)
ok = all(A_total(k + 1, m) - sum(Aj_total(k, m, j) for j in range(1, m + 1)) == T[k][m]
         for m in range(M + 1) for k in range(K + 1))
rep('U_k(m) = A_m(k+1) - sum_{j=1}^m A^{(j)}_m(k), k<=%d m<=%d' % (K, M), ok)

# 6. (C4) Theta formula
def c_i(i, n):
    if n < 0:
        return 0
    return sum(binom(n - 2 * j, j) * i ** j for j in range(0, n // 3 + 1))

from math import factorial
def Theta(t, n, m):
    return Fraction(sum((-1) ** r * binom(t, r) * c_i(m - r, n) for r in range(t + 1)), factorial(t))

ok = ok2 = True
for m in range(0, M + 1):
    for k in range(0, K + 1):
        val = Theta(m, k + 1 + 3 * m, m) - sum(Theta(t, k + 3 * t, m) for t in range(m))
        if val != T[k][m]:
            ok = False
        for t in range(0, m + 1):
            if Theta(t, k + 3 * t, m) != Aj_total(k, m, m - t):
                ok2 = False
rep('(C4) U = Theta_m(k+1+3m) - sum_t Theta_t(k+3t) == core DP, k<=%d m<=%d' % (K, M), ok)
rep('Theta_t(n+3t) == [x^n] prod_{i=m-t}^m 1/b_i (= A^{(m-t)}_m(n)), n<=%d m<=%d' % (K, M), ok2)

# 7. bijections via direct DP
ok = True
for m in range(M + 1):
    end0, endT = ending_dp(K + 1, m)
    tot, asc = DP[m]
    for k in range(0, K + 1):
        comp = sum(tot[k]) - sum(asc[k])
        if end0[k + 1] != comp:
            ok = False
        if k >= 2 and endT[k + 1] != sum(asc[k]):
            ok = False
rep('#complete(k) == #legal(k+1) ending in 0; #ascent-ending(k) == #legal(k+1) with h_{k-1}<h_k=h_{k+1}, k<=%d m<=%d' % (K, M), ok)

# 8. bivariate GF recursion: G_m = (G_{m-1} + m y x^2)/(1 - x - m y x^3)
# 表示：G[k] = 关于 y 的多项式（list）
def ser_rec(M, K):
    G = [[1]] + [[0] for _ in range(K)]          # G_{-1} = 1
    out = []
    for m in range(0, M + 1):
        num = [list(c) for c in G]
        # + m y x^2
        if K >= 2:
            c = num[2] + [0] * max(0, 2 - len(num[2]))
            c[1] += m
            num[2] = c
        # divide by 1 - x - m y x^3:  H[k] = num[k] + H[k-1] + m y H[k-3]
        H = []
        for k in range(K + 1):
            c = list(num[k])
            if k >= 1:
                c = [ (c[i] if i < len(c) else 0) + (H[k-1][i] if i < len(H[k-1]) else 0) for i in range(max(len(c), len(H[k-1]))) ]
            if k >= 3:
                sh = [0] + [m * v for v in H[k - 3]]
                c = [ (c[i] if i < len(c) else 0) + (sh[i] if i < len(sh) else 0) for i in range(max(len(c), len(sh))) ]
            H.append(c)
        G = H
        out.append(H)
    return out

GS = ser_rec(M, K)
ok = True
for m in range(M + 1):
    tot, asc = DP[m]
    for k in range(K + 1):
        poly = GS[m][k]
        for s in range(len(tot[k])):
            if (poly[s] if s < len(poly) else 0) != tot[k][s]:
                ok = False
        if any(poly[s] for s in range(len(tot[k]), len(poly))):
            ok = False
rep('bivariate GF: (1-x-m y x^3) G_m(x,y) = G_{m-1}(x,y) + m y x^2, coefficients == DP, k<=%d m<=%d' % (K, M), ok)

# 9. G_m = W_m/P_m and (C2)
ok = True
for m in range(M + 1):
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
    ser = series_mul(W, series_inv(P_poly(m), K + 1), K + 1)
    if [int(c) for c in ser] != [T[k][m] for k in range(K + 1)]:
        ok = False
    # x W_m == 1 - P_m - x sum_{j<m} P_j
    lhs = pshift(W, 1)
    rhs = [1]
    rhs = padd(rhs, pscale(P_poly(m), -1))
    for j in range(m):
        rhs = padd(rhs, pscale(pshift(P_poly(j), 1), -1))
    if trim(lhs) != trim(rhs):
        ok = False
rep('G_m = W_m/P_m (W_m = 1 + x^2 sum_j j P_{j-1}) == DP and x W_m = 1 - P_m - x sum_{j<m} P_j, k<=%d m<=%d' % (K, M), ok)

print('elapsed %.1fs' % (time.time() - t0))
