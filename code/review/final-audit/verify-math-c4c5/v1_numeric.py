# -*- coding: utf-8 -*-
"""Verifier step 1: independent numeric checks for findings #1, #2, #4, #5, #7.
Ground truth: code/core.py (U_fast_table = DP of the original definition; N_from_U; N_brute)."""
import os, sys, cmath
from fractions import Fraction
from math import comb, factorial

BASE = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(BASE, 'code'))
from core import U_fast_table, N_from_U, N_brute, stirling2_table, U_list

def lagrange_poly(xs, ys):
    """exact interpolation -> coefficient list (ascending) in Fraction"""
    n = len(xs)
    coeffs = [Fraction(0)] * n
    for i in range(n):
        # basis polynomial
        num = [Fraction(1)]
        den = Fraction(1)
        for j in range(n):
            if j == i:
                continue
            num = [Fraction(0)] + num  # multiply by x
            for t in range(len(num) - 1):
                num[t] -= xs[j] * num[t + 1]
            den *= (xs[i] - xs[j])
        for t in range(n):
            coeffs[t] += Fraction(ys[i]) * num[t] / den
    while len(coeffs) > 1 and coeffs[-1] == 0:
        coeffs.pop()
    return coeffs

KMAX, MMAX = 30, 40
T = U_fast_table(KMAX, MMAX)
# cross-check against the reference implementation U_list for a few columns
for m in (0, 1, 2, 5, 9):
    assert U_list(m, KMAX) == [T[k][m] for k in range(KMAX + 1)], m
print('U_fast_table agrees with U_list on m in {0,1,2,5,9}, k<=30')

# ---------------------------------------------------------------- #1 Stirling
print('\n==== #1: S(k,k-d) = sum_j S_2(d+j,j) C(k,d+j) ====')
NM = 70
S = stirling2_table(NM)
# associated Stirling numbers (every block >= 2): A(n,j) = j*A(n-1,j) + (n-1)*A(n-2,j-1)
A = [[0] * (NM + 1) for _ in range(NM + 1)]
A[0][0] = 1
for n in range(1, NM + 1):
    for j in range(1, NM + 1):
        A[n][j] = j * A[n - 1][j] + ((n - 1) * A[n - 2][j - 1] if n >= 2 else 0)
# brute-force check of A on small n via set partitions
def set_partitions(n):
    if n == 0:
        yield []
        return
    for p in set_partitions(n - 1):
        for i in range(len(p)):
            yield p[:i] + [p[i] + [n]] + p[i + 1:]
        yield p + [[n]]
for n in range(0, 9):
    cnt = {}
    for p in set_partitions(n):
        if all(len(b) >= 2 for b in p):
            cnt[len(p)] = cnt.get(len(p), 0) + 1
    for j in range(0, n + 1):
        assert A[n][j] == cnt.get(j, 0), (n, j)
print('associated Stirling recurrence matches brute-force set partitions for n<=8')
ok_assoc, bad_ord = True, []
for d in range(0, 9):
    for k in range(d, 60):
        lhs = S[k][k - d]
        rhs_assoc = sum(A[d + j][j] * comb(k, d + j) for j in range(0, k - d + 1))
        rhs_ord = sum(S[d + j][j] * comb(k, d + j) for j in range(0, k - d + 1))
        if lhs != rhs_assoc:
            ok_assoc = False
        if lhs != rhs_ord:
            bad_ord.append((d, k, lhs, rhs_ord))
print('associated-Stirling reading holds for 0<=d<=8, d<=k<60:', ok_assoc)
print('ordinary-Stirling reading fails at', len(bad_ord), 'points; first few:', bad_ord[:4])
print('  k=4,d=1 terms (ordinary):', [(j, S[1 + j][j], comb(4, 1 + j)) for j in range(0, 4)], ' S(4,3)=', S[4][3])

# ---------------------------------------------------------------- #4 fixed k, m->inf
print('\n==== #4: U_k(m) as polynomial in m; mu_k form and C(m+1,.) basis ====')
UPOLY = {}
for k in range(0, 16):
    xs = list(range(0, k + 3))
    ys = [T[k][m] for m in xs]
    p = lagrange_poly([Fraction(x) for x in xs], ys)
    # verify on all remaining m
    for m in range(0, MMAX + 1):
        assert sum(c * m ** i for i, c in enumerate(p)) == T[k][m]
    UPOLY[k] = p
for k in range(0, 13):
    p = UPOLY[k]
    deg = len(p) - 1
    lead = p[deg]
    sub = p[deg - 1] if deg >= 1 else Fraction(0)
    mu = Fraction(k * k - 2 * k - 1, 2)
    # coefficients of (2/k!)(m+mu)^k
    lead_f = Fraction(2, factorial(k))
    sub_f = lead_f * k * mu
    ratio_note = ''
    if deg == k and lead == lead_f and sub == sub_f:
        ratio_note = 'top two coeffs match -> ratio = 1+O(m^-2)'
    else:
        ratio_note = 'MISMATCH -> ratio != 1+O(m^-2)'
    print(f'k={k:2d}: deg={deg} [m^k]={lead} (2/k!={lead_f})  [m^(k-1)]={sub}  (2/k!)*k*mu_k={sub_f}   {ratio_note}')
# relative error growth at k=3 for illustration
k = 3
for m in (10, 100, 1000):
    val = T[3][m] if m <= MMAX else sum(c * m ** i for i, c in enumerate(UPOLY[3]))
    approx = Fraction(2, 6) * (m + Fraction(1)) ** 3
    print(f'   k=3, m={m}: U/((2/3!)(m+mu_3)^3) - 1 = {float(Fraction(val) / approx - 1):.6g}   (m^-1 would be {1/m:.3g}, m^-2 {1/m**2:.3g})')

# N(k,q) from DP, check vs basis coefficients
print('\n  C(m+1,.) basis: N(k,k)=2? N(k,k-1)=k^2-k-4? N(k,k-2)=p_2(k)?')
def p2(k):
    return Fraction(k ** 4 - 10 * k ** 3 + 43 * k ** 2 - 98 * k + 164, 4)
for k in range(1, 13):
    Nk = [N_from_U(T, k, q) for q in range(0, k + 1)]
    # also independent: DFS definition for small k
    if k <= 8:
        nb = N_brute(k)
        assert all(nb.get(q, 0) == Nk[q] for q in range(k + 1)), k
    s1 = Nk[k] == 2
    s2 = Nk[k - 1] == k * k - k - 4 if k >= 1 else None
    s3 = (Nk[k - 2] == p2(k)) if k >= 2 else None
    print(f'  k={k:2d}: N(k,k)={Nk[k]} ({s1})  N(k,k-1)={Nk[k-1]} vs {k*k-k-4} ({s2})  ' +
          (f'N(k,k-2)={Nk[k-2]} vs p2={p2(k)} ({s3})' if k >= 2 else ''))
# direct check of the full basis statement: U_k - [2C(m+1,k)+(k^2-k-4)C(m+1,k-1)+p_2(k)C(m+1,k-2)] has degree <= k-3 ?
print('  degree of U_k(m) - [2C(m+1,k)+(k^2-k-4)C(m+1,k-1)+p_2(k)C(m+1,k-2)] in m (should be <= k-3):')
def binom_poly_vals(m, q):
    # polynomial C(m+1,q)
    num = Fraction(1)
    for i in range(q):
        num *= (m + 1 - i)
    return num / factorial(q)
for k in range(2, 13):
    xs = list(range(0, k + 3))
    ys = [T[k][m] - (2 * binom_poly_vals(m, k) + (k * k - k - 4) * binom_poly_vals(m, k - 1) + p2(k) * binom_poly_vals(m, k - 2)) for m in xs]
    r = lagrange_poly([Fraction(x) for x in xs], ys)
    print(f'    k={k:2d}: deg = {len(r) - 1 if any(r) else "-inf"}  {"OK" if (len(r) - 1) <= k - 3 or not any(r) else "FAILS"}')

# ---------------------------------------------------------------- #7 B_d identity with elementary symmetric e_j
print('\n==== #7: B_d(k) = sum_e (-1)^{d-e} N(k,k-e) e~_{d-e}(k-e), e~_j(n)=e_j(-1,0,...,n-2)/n^{(j)} ====')
def elem_sym(j, vals):
    row = [Fraction(1)] + [Fraction(0)] * j
    for v in vals:
        for t in range(j, 0, -1):
            row[t] += v * row[t - 1]
    return row[j]
def falling(n, j):
    r = 1
    for i in range(j):
        r *= (n - i)
    return r
ok7 = True
cnt7 = 0
for d in range(0, 6):
    for k in range(max(d, 1), 16):
        p = UPOLY[k]
        coef = p[k - d] if k - d < len(p) else Fraction(0)
        Bd = factorial(k - d) * coef
        rhs = Fraction(0)
        for e in range(0, d + 1):
            n = k - e
            j = d - e
            ej = elem_sym(j, list(range(-1, n - 1)))
            fj = falling(n, j)
            if fj == 0:
                # e~_j(n) is a polynomial; e_j vanishes when fewer than j values; treat 0/0 via polynomial value
                assert ej == 0
                # polynomial value: compute e~_j as polynomial in n by interpolation on large n
                xs = [Fraction(x) for x in range(j + 5, 3 * j + 10)][: j + 1]
                ys = [elem_sym(j, list(range(-1, int(x) - 1))) / falling(int(x), j) for x in xs]
                q = lagrange_poly(xs, ys)
                val = sum(c * n ** i for i, c in enumerate(q))
            else:
                val = ej / fj
            rhs += (-1) ** (d - e) * N_from_U(T, k, k - e) * val
        cnt7 += 1
        if rhs != Bd:
            ok7 = False
            print('   mismatch', d, k, Bd, rhs)
print(f'identity holds on all {cnt7} pairs (0<=d<=5, max(d,1)<=k<=15): {ok7}')
print('e~_1(n) closed form check (n-3)/2:', all(elem_sym(1, list(range(-1, n - 1))) / n == Fraction(n - 3, 2) for n in range(1, 30)))

# ---------------------------------------------------------------- #5 Binet: gamma_j are partial-fraction coefficients, recurrence
print('\n==== #5: alpha_m(sigma) recurrence; coefficient vs residue ====')
import numpy as np
def roots_j(j):
    if j == 0:
        return [1.0 + 0j]
    return [complex(r) for r in np.roots([1, -1, 0, -j])]
def gamma(j, s):
    if j == 0:
        return 1.0 + 0j
    return (s ** (3 * j + 3) / factorial(j) + sum((j - i) * s ** (3 * i + 1) / factorial(i) for i in range(j))) / (s * s + 3 * j)
maxrel = 0.0
for m in range(0, 7):
    for k in range(0, 31):
        tot = 0j
        for j in range(0, m + 1):
            for s in roots_j(j):
                tot += ((-1) ** (m - j) / factorial(m - j)) * gamma(j, s) * s ** (k + 3 * (m - j))
        exact = T[k][m]
        maxrel = max(maxrel, abs(tot - exact) / exact)
print(f'Binet formula with gamma as partial-fraction coefficients reproduces DP: max rel err {maxrel:.2e} (0<=m<=6, 0<=k<=30)')
# coefficient alpha_m(sigma) of 1/(1-sigma x) in G_m, extracted numerically by least squares from U_k(m), k=0..K
for m in (2, 3):
    poles = [(j, s) for j in range(m + 1) for s in roots_j(j)]
    K = 3 * m + 1 + 12
    M = np.array([[s ** k for (j, s) in poles] for k in range(K)], dtype=complex)
    y = np.array([T[k][m] for k in range(K)], dtype=complex)
    alpha, *_ = np.linalg.lstsq(M, y, rcond=None)
    # previous m
    poles1 = [(j, s) for j in range(m) for s in roots_j(j)]
    M1 = np.array([[s ** k for (j, s) in poles1] for k in range(K)], dtype=complex)
    y1 = np.array([T[k][m - 1] for k in range(K)], dtype=complex)
    alpha1, *_ = np.linalg.lstsq(M1, y1, rcond=None)
    worst = 0.0
    for idx, (j, s) in enumerate(poles1):
        pred = alpha1[idx] * (-s ** 3) / (m - j)
        worst = max(worst, abs(alpha[idx] - pred) / abs(alpha[idx]))
        # residue at x=1/s is -alpha/s; same recurrence for residues
        res_m, res_m1 = -alpha[idx] / s, -alpha1[idx] / s
        worst = max(worst, abs(res_m - res_m1 * (-s ** 3) / (m - j)) / abs(res_m))
    # c_m = coefficient at rho_m, residue = -c_m x_m
    jr = [(i, (j, s)) for i, (j, s) in enumerate(poles) if j == m and abs(s.imag) < 1e-12]
    i0, (_, rho) = jr[0]
    print(f'm={m}: recurrence alpha_m=alpha_(m-1)*(-s^3)/(m-j) holds for old poles (coeffs and residues alike), worst rel dev {worst:.1e}; '
          f'coefficient at rho_m = {alpha[i0].real:.10f} (= c_m), residue = {(-alpha[i0]/rho).real:.10f}')
