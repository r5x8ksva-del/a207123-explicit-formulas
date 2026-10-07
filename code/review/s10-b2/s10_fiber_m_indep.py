# -*- coding: utf-8 -*-
"""s10-b2 check (a): the fibre condition of note 08 is the same for every m.

Independent of the note's code.  Steps:
  1. my own DP / brute force for U_k(m) and U^up_k(m) (ending with an ascent)  vs  W_m/P_m, (W_m-1)/P_m;
  2. coordinates over Q(u): x^g = e_g0(u) + e_g1(u) x + e_g2(u) x^2 as Laurent polynomials in u
     (computed symbolically), checked at random rational points and against eta^g in K_i (Lemma 1(c), 3(a));
  3. residue element from the definition  rho = u'(eta) W_m(eta) / P_m'(eta)  in K_i
     vs the closed form of Lemma 5  c_{i,m} W~_i(eta) eta^{-3m-3}   (also for E: W_m - 1);
  4. residue vector R of the coordinate vector a(u) of G_m (resp. E_m) at u = 1/i, computed from the
     symbolic coordinates;  check R0 + R1 eta + R2 eta^2 = rho  (Lemma 3(b));
  5. for m = 2..7, every available fibre i <= min(m,3), all g1 != g2 in a window:
        det[e_g1(1/i), e_g2(1/i), R]  ==  (1/i)^g1 * c_{i,m} * D_i(n, b),  n = -3m-3-g1, b = g2-g1,
     where D_i is computed from W~_i only (no m);
  6. the zero sets {(n,b)} obtained from m = 2..6 coincide (fibres 1,2; fibre 3 for m = 3..6).
"""
import sys
import random
from fractions import Fraction as Fr
from itertools import product

sys.path.insert(0, __file__.rsplit('\\', 1)[0] if '\\' in __file__ else '.')
from s10lib import (P_poly, W_poly, Wtilde_poly, pderiv, series_div, Ki, cols_det, const_c, b_poly)

FAIL = 0
PASS = 0


def report(name, ok, info=''):
    global FAIL, PASS
    if ok:
        PASS += 1
    else:
        FAIL += 1
    print(('PASS ' if ok else 'FAIL ') + name + (' | ' + info if info else ''), flush=True)


# ---------------------------------------------------------------------------- 1. definitions
def good(a, b, c):
    return b == c or (a >= b and a >= c)


def dp_counts(m, K):
    U = [1, m + 1]
    Up = [0, 0]
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    U.append(sum(cnt.values()))
    Up.append(sum(v for (a, b), v in cnt.items() if a < b))
    for k in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
        cnt = new
        U.append(sum(cnt.values()))
        Up.append(sum(v for (a, b), v in cnt.items() if a < b))
    return U, Up


def brute_counts(m, k):
    tot = up = 0
    for h in product(range(m + 1), repeat=k):
        if all(good(h[j], h[j + 1], h[j + 2]) for j in range(k - 2)):
            tot += 1
            if k >= 2 and h[-2] < h[-1]:
                up += 1
    return tot, up


ok = True
for m in range(0, 4):
    U, Up = dp_counts(m, 8)
    for k in range(0, 8):
        if (m + 1) ** k > 70000:
            continue
        t, u_ = brute_counts(m, k)
        if (t, u_) != (U[k], Up[k]):
            ok = False
report('1a DP == brute force (m<=3, k<=7)', ok)

ok = True
for m in range(0, 7):
    K = 30
    U, Up = dp_counts(m, K)
    P, W = P_poly(m), W_poly(m)
    sG = series_div(W, P, K)
    Wm1 = list(W)
    Wm1[0] -= 1
    sE = series_div(Wm1, P, K)
    if sG != U or sE != Up:
        ok = False
        print('   mismatch at m =', m)
report('1b G_m = W_m/P_m and E_m = (W_m-1)/P_m vs DP (m<=6, k<=30)', ok)

# ---------------------------------------------------------------------------- 2. coordinates over Q(u)
# Laurent polynomial in u: dict exp -> Fraction
def lp_add(a, b, s=1):
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, 0) + s * c
        if out[e] == 0:
            del out[e]
    return out


def lp_shift(a, k):
    return {e + k: c for e, c in a.items()}


def lp_eval(a, u0):
    return sum((Fr(c) * Fr(u0) ** e for e, c in a.items()), Fr(0))


GMIN, GMAX = -80, 60
E = {0: ({0: Fr(1)}, {}, {})}
for g in range(0, GMAX):
    c0, c1, c2 = E[g]
    # x * (c0 + c1 x + c2 x^2) = c2 u + (c0 - c2 u) x + c1 x^2      (x^3 = u - u x)
    E[g + 1] = (lp_shift(c2, 1), lp_add(c0, lp_shift(c2, 1), -1), dict(c1))
for g in range(0, GMIN, -1):
    c0, c1, c2 = E[g]
    # x^{-1} = 1 + u^{-1} x^2 :  x^{-1}(c0 + c1 x + c2 x^2) = (c0 + c1) + c2 x + u^{-1} c0 x^2
    E[g - 1] = (lp_add(c0, c1), dict(c2), lp_shift(c0, -1))

random.seed(20261008)
ok = True
for _ in range(12):
    x0 = Fr(random.randint(-40, 40), random.randint(41, 90))
    if x0 == 0:
        continue
    u0 = x0 ** 3 / (1 - x0)
    for g in range(GMIN, GMAX + 1, 7):
        lhs = sum((lp_eval(E[g][r], u0) * x0 ** r for r in range(3)), Fr(0))
        if lhs != x0 ** g:
            ok = False
report('2a x^g = sum_r e_gr(u) x^r at 12 random rational x (g in [-80,60] step 7)', ok)

ok = True
for i in (1, 2, 3):
    K = Ki(i)
    for g in range(GMIN, GMAX + 1):
        val = tuple(lp_eval(E[g][r], Fr(1, i)) for r in range(3))
        if val != K.eta_pow(g):
            ok = False
report('2b e_g(1/i) == coordinates of eta^g in K_i (i=1,2,3; g in [-80,60])', ok)

# ---------------------------------------------------------------------------- 3-5. residues
EVC = {}


def ev_e(g, i):
    key = (g, i)
    if key not in EVC:
        EVC[key] = tuple(lp_eval(E[g][r], Fr(1, i)) for r in range(3))
    return EVC[key]


def coords_of_poly_times_xpow(poly, shift):
    """symbolic coordinate vector of sum_k poly[k] x^{k+shift}"""
    acc = ({}, {}, {})
    for k, c in enumerate(poly):
        if c:
            e = E[k + shift]
            acc = tuple(lp_add(acc[r], {ee: c * cc for ee, cc in e[r].items()}) for r in range(3))
    return acc


def u_of(x0):
    return x0 ** 3 / (1 - x0)


results = {}   # (part, m, i) -> R vector (Fractions)
ok3 = ok4 = ok4b = True
for m in range(2, 8):
    P = P_poly(m)
    W = W_poly(m)
    Pd = pderiv(P)
    # random-point check of P_m = (1-x)^{m+1} prod_{v=1}^m (1 - v u)
    for x0 in (Fr(2, 7), Fr(-3, 5), Fr(11, 13)):
        lhs = sum(Fr(c) * x0 ** k for k, c in enumerate(P))
        rhs = (1 - x0) ** (m + 1)
        for v in range(1, m + 1):
            rhs *= (1 - v * u_of(x0))
        if lhs != rhs:
            ok4b = False
    for part in ('U', 'E'):
        num = list(W)
        if part == 'E':
            num[0] -= 1
        # symbolic coordinates c(u) of num(x) * x^{-3m-3};  a(u) = c(u) u^{m+1} / prod_{v=1}^m (1 - v u)
        cvec = coords_of_poly_times_xpow(num, -3 * m - 3)
        for i in range(1, min(m, 3) + 1):
            K = Ki(i)
            eta = K.eta_pow(1)
            # --- residue element from the definition
            Pval = K.ev(P)
            if Pval != (0, 0, 0):
                ok3 = False
            Pdv = K.ev(Pd)
            numv = K.ev(num)
            one_m_eta = K.add((Fr(1), Fr(0), Fr(0)), K.scal(Fr(-1), eta))
            # u'(eta) = eta^2 (3 - 2 eta) / (1 - eta)^2
            up = K.mul(K.mul(K.eta_pow(2), (Fr(3), Fr(-2), Fr(0))), K.inv(K.mul(one_m_eta, one_m_eta)))
            rho_def = K.mul(up, K.mul(numv, K.inv(Pdv)))
            # --- closed form of Lemma 5
            Wt = Wtilde_poly(i)
            if part == 'E':
                Wt = list(Wt)
                Wt[0] -= 1
            rho_cf = K.scal(const_c(i, m), K.ev(Wt, shift=-3 * m - 3))
            if rho_def != rho_cf:
                ok3 = False
                print('   Lemma 5 mismatch', part, m, i)
            # --- residue vector R of a(u) at u = 1/i
            ui = Fr(1, i)
            cval = [lp_eval(cvec[r], ui) for r in range(3)]
            fac = ui ** (m + 1) * Fr(-1, i)          # Res_{u=1/i} 1/(1 - i u) = -1/i
            for v in range(1, m + 1):
                if v != i:
                    fac /= (1 - v * ui)
            R = tuple(fac * cval[r] for r in range(3))
            lhs = K.add(K.add(K.scal(R[0], (Fr(1), Fr(0), Fr(0))), K.scal(R[1], eta)), K.scal(R[2], K.eta_pow(2)))
            if lhs != rho_def:
                ok4 = False
                print('   Lemma 3(b) mismatch', part, m, i)
            results[(part, m, i)] = R
report('3  Lemma 5: u\'(eta) * Res = c_{i,m} W~_i(eta) eta^{-3m-3} (U and E; 2<=m<=7; i<=min(m,3)), P_m(eta)=0', ok3)
report('4a P_m = (1-x)^{m+1} prod (1 - v u) at random points (2<=m<=7)', ok4b)
report('4b R0 + R1 eta + R2 eta^2 == u\'(eta) Res_eta (residue vector from symbolic coordinates)', ok4)


def D_closed(K, Wt, n, b):
    p = K.eta_pow(b)
    q = K.mul(K.ev(Wt), K.eta_pow(n))
    return p[1] * q[2] - p[2] * q[1]


# ---------------------------------------------------------------------------- 5. determinant identity
WIN = 24
ok5 = True
cnt5 = 0
Dcache = {}
for (part, m, i), R in sorted(results.items()):
    K = Ki(i)
    Wt = Wtilde_poly(i)
    if part == 'E':
        Wt = list(Wt)
        Wt[0] -= 1
    cm = const_c(i, m)
    ui = Fr(1, i)
    for g1 in range(-3 * m - 3 - WIN, -3 * m - 3 + WIN + 1):
        e1 = ev_e(g1, i)
        n = -3 * m - 3 - g1
        for b in range(-WIN, WIN + 1):
            if b == 0:
                continue
            g2 = g1 + b
            e2 = ev_e(g2, i)
            d3 = cols_det(e1, e2, R)
            key = (part, i, n, b)
            if key not in Dcache:
                Dcache[key] = D_closed(K, Wt, n, b)
            if d3 != ui ** g1 * cm * Dcache[key]:
                ok5 = False
            cnt5 += 1
report('5  det[e_g1(1/i), e_g2(1/i), R] == (1/i)^g1 c_{i,m} D_i(n,b) (2<=m<=7, |n|,|b|<=%d, %d cases)' % (WIN, cnt5), ok5)

# ---------------------------------------------------------------------------- 6. zero sets across m
ok6 = True
summary = []
for part in ('U', 'E'):
    for i in (1, 2, 3):
        ms = [m for m in range(2, 7) if i <= m]
        zsets = []
        for m in ms:
            R = results[(part, m, i)]
            ui = Fr(1, i)
            Z = set()
            for n in range(-WIN, WIN + 1):
                g1 = -3 * m - 3 - n
                e1 = ev_e(g1, i)
                for b in range(-WIN, WIN + 1):
                    if b == 0:
                        continue
                    e2 = ev_e(g1 + b, i)
                    if cols_det(e1, e2, R) == 0:
                        Z.add((n, b))
            zsets.append(Z)
        same = all(z == zsets[0] for z in zsets)
        ok6 = ok6 and same
        summary.append('%s fibre %d: m=%s, |zero set|=%d, identical=%s' % (part, i, ms, len(zsets[0]), same))
for s in summary:
    print('   ' + s)
report('6  zero sets of the fibre determinant identical for m=2..6 (|n|,|b|<=%d, b!=0)' % WIN, ok6)

print('SUMMARY s10_fiber_m_indep: PASS=%d FAIL=%d' % (PASS, FAIL))
sys.exit(1 if FAIL else 0)
