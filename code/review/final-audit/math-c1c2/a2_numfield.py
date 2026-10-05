# -*- coding: utf-8 -*-
"""final-audit / math-c1c2 / a2 : T2.6 algebra.
 - exact arithmetic in K_i = Q[x]/(i x^3 + x - 1)  (b_i(x) = 1 - x - i x^3 = -(i x^3 + x - 1))
 - norms quoted in T2.6(ii): N(W~_2 - 1)=17/8, N(W~_2)=103/16, N(x)=1/2, N(4-2x)=68, W~_2-1 = x^5(4-2x)
 - W_m == W~_i (mod b_i) for m >= i
 - residue element of G_m and of its E part at the fiber u = 1/i, computed DIRECTLY as
       Res_{x=eta}(.) * u'(eta)  (eta = root of b_i, all embeddings at once inside K_i)
   and compared with  const(i,m) * W~_i * x^{-3m-3}   resp.  const(i,m) * (W~_i - 1) * x^{-3m-3}
 - T2.6(3): r_i u'(xi_i) = (-1)^m (1+xi) xi^{-3m-2}/(m-1)!  (K_1, m<=15)
 - v_17(N(nu_2)) == 1 mod 3 for the E part, m=2..20 (the obstruction used in T2.6(ii))
 - T2.6(i) numerics: v_0 = xi^{-3} in (3.04,3.18) for (1,2); fiber polynomials have exactly one real root.
No import of core/polylib."""
import sys, os, time
from fractions import Fraction as Fr
from math import factorial
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mylib import P_poly, W_poly, falling, padd, pmul, ptrim
import numpy as np

T0 = time.time()
NPASS = NFAIL = 0


def rep(ok, cid, msg):
    global NPASS, NFAIL
    NPASS += bool(ok)
    NFAIL += (not ok)
    print(('PASS ' if ok else 'FAIL ') + cid + ' ' + msg, flush=True)


class K:
    """K_i = Q[x]/(i x^3 + x - 1): x^3 = (1 - x)/i"""
    def __init__(self, i):
        self.i = Fr(i)

    def red(self, poly):
        a = [Fr(c) for c in poly]
        for n in range(len(a) - 1, 2, -1):
            c = a[n]
            if c:
                a[n] = Fr(0)
                a[n - 3] += c / self.i
                a[n - 2] -= c / self.i
        a = a[:3] + [Fr(0)] * max(0, 3 - len(a))
        return a[:3]

    def mul(self, a, b):
        p = [Fr(0)] * 5
        for s in range(3):
            for t in range(3):
                p[s + t] += a[s] * b[t]
        return self.red(p)

    def add(self, a, b):
        return [a[t] + b[t] for t in range(3)]

    def sc(self, a, c):
        return [a[t] * c for t in range(3)]

    def mat(self, a):
        cols = [self.mul(a, e) for e in ([1, 0, 0], [0, 1, 0], [0, 0, 1])]
        return [[cols[c][r] for c in range(3)] for r in range(3)]

    def norm(self, a):
        M = self.mat(a)
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
                - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))

    def inv(self, a):
        M = self.mat(a)
        # solve M y = e0 by Gauss
        A = [row[:] + [Fr(1 if r == 0 else 0)] for r, row in enumerate(M)]
        n = 3
        for c in range(n):
            piv = next(r for r in range(c, n) if A[r][c] != 0)
            A[c], A[piv] = A[piv], A[c]
            pv = A[c][c]
            A[c] = [v / pv for v in A[c]]
            for r in range(n):
                if r != c and A[r][c] != 0:
                    f = A[r][c]
                    A[r] = [A[r][t] - f * A[c][t] for t in range(n + 1)]
        return [A[r][n] for r in range(n)]

    def pw(self, a, e):
        if e < 0:
            a = self.inv(a)
            e = -e
        r = [Fr(1), Fr(0), Fr(0)]
        b = a
        while e:
            if e & 1:
                r = self.mul(r, b)
            b = self.mul(b, b)
            e >>= 1
        return r

    def ev(self, poly):
        return self.red(poly)


def is_rational(a):
    return a[1] == 0 and a[2] == 0


def Wtilde(i):
    """W~_i = 1 + sum_{j=1}^i j * i^{(j)} x^{3j+2} (integer polynomial)"""
    p = [0] * (3 * i + 3)
    p[0] = 1
    for j in range(1, i + 1):
        p[3 * j + 2] += j * falling(i, j)
    return p


X = [Fr(0), Fr(1), Fr(0)]
ONE = [Fr(1), Fr(0), Fr(0)]

# ---------------------------------------------------------------- K_2 facts
K2 = K(2)
# field: 2x^3+x-1 has no rational root (candidates +-1, +-1/2)
roots = [r for r in (Fr(1), Fr(-1), Fr(1, 2), Fr(-1, 2)) if 2 * r ** 3 + r - 1 == 0]
W2 = Wtilde(2)
W2m1 = list(W2); W2m1[0] -= 1
lhs = K2.ev(W2m1)
rhs = K2.mul(K2.pw(X, 5), [Fr(4), Fr(-2), Fr(0)])
n_w2m1 = K2.norm(lhs)
n_w2 = K2.norm(K2.ev(W2))
n_x = K2.norm(X)
n_4m2x = K2.norm([Fr(4), Fr(-2), Fr(0)])
print('# K_2: W~_2 =', W2, ' N(W~_2-1)=', n_w2m1, ' N(W~_2)=', n_w2, ' N(x)=', n_x, ' N(4-2x)=', n_4m2x)
rep(not roots and lhs == rhs and n_w2m1 == Fr(17, 8) and n_w2 == Fr(103, 16) and n_x == Fr(1, 2) and n_4m2x == 68,
    'T2.6ii.K2', 'K_2 is a field; W~_2-1 = 2x^5+4x^8 = x^5(4-2x) in K_2; N(W~_2-1)=17/8, N(W~_2)=103/16, N(x)=1/2, N(4-2x)=68 (all exact)')

# ---------------------------------------------------------------- K_1 facts (Theorem S)
K1 = K(1)
W1 = K1.ev(Wtilde(1))
xi1px = K1.mul(X, [Fr(1), Fr(1), Fr(0)])
rep(W1 == xi1px and K1.norm(X) == 1 and K1.norm([Fr(1), Fr(1), Fr(0)]) == 3 and K1.norm(W1) == 3,
    'T2.6.K1', 'in K_1: W~_1 = 1+x^5 = x(1+x); N(x)=1, N(1+x)=3, N(W~_1)=3')

# ---------------------------------------------------------------- W_m == W~_i (mod b_i), m>=i
def polymod_b(poly, i):
    """remainder of integer poly modulo b_i = 1 - x - i x^3 (exact, Fractions), as length-3 list"""
    a = [Fr(c) for c in poly]
    # b_i = -i x^3 - x + 1 : x^3 = (1 - x)/i
    for n in range(len(a) - 1, 2, -1):
        c = a[n]
        if c:
            a[n] = Fr(0)
            a[n - 3] += c / i
            a[n - 2] -= c / i
    a = a[:3] + [Fr(0)] * max(0, 3 - len(a))
    return a[:3]


bad = []
for i in range(1, 15):
    wt = polymod_b(Wtilde(i), i)
    for m in range(i, 15):
        if polymod_b(W_poly(m), i) != wt:
            bad.append((i, m))
    # and for m < i it is NOT W~_i in general (just report the first)
rep(not bad, 'T2.6.Wtilde', 'W_m == W~_i (mod b_i) for 1<=i<=m<=14 (exact remainders); bad=%s' % bad[:3])


# ---------------------------------------------------------------- direct residues in K_i
def bval(Ki, v):
    return Ki.ev([1, -1, 0, -v])


def residues(i, m):
    """returns (res_u of G_m, res_u of E part) at the fiber u=1/i, computed directly in K_i"""
    Ki = K(i)
    eta = X
    bprime_i = Ki.ev([-1, 0, -3 * i])                 # b_i'(x) = -1 - 3 i x^2
    one_m_eta = Ki.add(ONE, Ki.sc(eta, -1))
    uprime = Ki.mul(Ki.mul(Ki.pw(eta, 2), Ki.ev([3, -2])), Ki.pw(one_m_eta, -2))   # u' = x^2(3-2x)/(1-x)^2
    resE = [Fr(0)] * 3
    for j in range(1, min(i, m) + 1):
        den = bprime_i
        for v in range(j, m + 1):
            if v != i:
                den = Ki.mul(den, bval(Ki, v))
        term = Ki.mul(Ki.sc(Ki.pw(eta, 2), j), Ki.inv(den))
        resE = Ki.add(resE, term)
    den0 = bprime_i
    for v in range(0, m + 1):
        if v != i:
            den0 = Ki.mul(den0, bval(Ki, v))
    resA = Ki.inv(den0)
    resU = Ki.add(resA, resE)
    return Ki, Ki.mul(resU, uprime), Ki.mul(resE, uprime)


def is_field(i):
    # i x^3 + x - 1 has a rational root iff i = y^2 (y-1)
    return all(y * y * (y - 1) != i for y in range(2, 60))


bad = []
ncase = 0
for i in range(1, 13):
    if not is_field(i):
        continue
    for m in range(i, 15):
        Ki, rU, rE = residues(i, m)
        const = Fr(-1, i * i * factorial(i) * (-1) ** (m - i) * factorial(m - i))
        wt = Ki.ev(Wtilde(i))
        wtm1 = Ki.add(wt, [Fr(-1), Fr(0), Fr(0)])
        xp = Ki.pw(X, -3 * m - 3)
        predU = Ki.sc(Ki.mul(wt, xp), const)
        predE = Ki.sc(Ki.mul(wtm1, xp), const)
        ncase += 1
        if rU != predU or rE != predE:
            bad.append((i, m))
rep(not bad, 'T2.6.residue_closed_form', 'directly computed Res_x*u\' at the roots of b_i equals '
    '-W~_i x^{-3m-3}/(i^2 i! (-1)^{m-i}(m-i)!) for G_m, and the same with W~_i-1 for the E part '
    '(%d cases, field i<=12, i<=m<=14); bad=%s' % (ncase, bad[:3]))

# T2.6(3) quoted formula, directly from W_m / P_m' (no structure assumed)
bad = []
for m in range(1, 16):
    Kq = K(1)
    Wm = Kq.ev(W_poly(m))
    Pm = P_poly(m)
    dP = [n * Pm[n] for n in range(1, len(Pm))]
    r = Kq.mul(Wm, Kq.inv(Kq.ev(dP)))                         # residue of G_m at xi
    one_m = Kq.add(ONE, Kq.sc(X, -1))
    up = Kq.mul(Kq.mul(Kq.pw(X, 2), Kq.ev([3, -2])), Kq.pw(one_m, -2))
    lhs = Kq.mul(r, up)
    rhs = Kq.sc(Kq.mul([Fr(1), Fr(1), Fr(0)], Kq.pw(X, -3 * m - 2)), Fr((-1) ** m, factorial(m - 1)))
    if lhs != rhs or Kq.ev(W_poly(m)) != Kq.mul(X, [Fr(1), Fr(1), Fr(0)]):
        bad.append(m)
rep(not bad, 'T2.6.(3)', 'r_i u\'(xi_i) = (-1)^m (1+xi) xi^{-3m-2}/(m-1)! and W_m(xi)=xi(1+xi), exact in K_1 from W_m/P_m\', m=1..15; bad=%s' % bad)


# T2.6(ii) obstruction: v_17(N(nu)) for the E part at u=1/2 is 1 mod 3
def vp(q, p):
    q = Fr(q)
    if q == 0:
        return None
    n, d = q.numerator, q.denominator
    e = 0
    while n % p == 0:
        n //= p; e += 1
    while d % p == 0:
        d //= p; e -= 1
    return e


bad = []
vals = []
for m in range(2, 21):
    Ki, rU, rE = residues(2, m)
    N = Ki.norm(rE)
    e = vp(N, 17)
    vals.append(e)
    if e is None or e % 3 != 1:
        bad.append(m)
rep(not bad, 'T2.6ii.v17', 'E part, fiber u=1/2: v_17(N(residue element)) = %s (== 1 mod 3) for m=2..20; '
    'so x^N * nu in Q is impossible; bad=%s' % (sorted(set(vals)), bad))

# c2b table check: N(nu_2) for E m=2 is 17 and for U m=2 is 103/2 in c2b normalisation nu = -i*theta
Ki, rU, rE = residues(2, 2)
nE = Ki.norm(Ki.sc(rE, Fr(-2)))
nU = Ki.norm(Ki.sc(rU, Fr(-2)))
rep(nE == 17 and nU == Fr(103, 2), 'T2.6ii.c2b_table', 'with c2b normalisation nu_i=-i*theta_i: N=17 (E, m=2), 103/2 (U, m=2); got %s, %s' % (nE, nU))

# ---------------------------------------------------------------- T2.6(i) numerics
xi = [r.real for r in np.roots([1, 0, 1, -1]) if abs(r.imag) < 1e-12][0]
v0_12 = xi ** 3 / (1 - xi) ** 2
v0_23 = xi ** 5 / (1 - xi) ** 3
ok = (0.68 < xi < 0.69) and abs(v0_12 - xi ** -3) < 1e-12 and 3.04 < v0_12 < 3.18 and abs(v0_23 - xi ** -4) < 1e-12
disc = 4 * v0_12 * (v0_12 - 6)
r12 = np.roots([1, -v0_12, 2 * v0_12, -v0_12])            # x^3 - v0 (1-x)^2
r23 = np.roots(np.polysub([1, 0, 0, 0, 0, 0], v0_23 * np.array([0, 0, -1, 3, -3, 1])))   # x^5 - v0 (1-x)^3
real12 = [r for r in r12 if abs(r.imag) < 1e-9]
real23 = [r for r in r23 if abs(r.imag) < 1e-9]
print('# xi=%.12f  v0(1,2)=%.10f  v0(2,3)=%.10f  disc f\'=%.4f' % (xi, v0_12, v0_23, disc))
print('# fiber (1,2) roots:', np.round(r12, 8))
print('# fiber (2,3) roots:', np.round(r23, 8))


def not_b_root(eta, wmax=200):
    w = (1 - eta) / eta ** 3
    return not (abs(w.imag) < 1e-7 and abs(w.real - round(w.real)) < 1e-7 and 1 <= round(w.real) <= wmax)


ok2 = (disc < 0 and len(real12) == 1 and abs(real12[0].real - xi) < 1e-9 and len(real23) == 1 and abs(real23[0].real - xi) < 1e-9
       and all(not_b_root(r) for r in r12 if abs(r.imag) > 1e-9) and all(not_b_root(r) for r in r23 if abs(r.imag) > 1e-9))
rep(ok and ok2, 'T2.6i.numeric', 'xi in (0.68,0.69); (1,2): v0=xi^3/(1-xi)^2=xi^{-3}=%.6f in (3.04,3.18), disc(f\')<0, one real fiber point (=xi); '
    '(2,3): v0=xi^{-4}, one real fiber point (=xi); non-real fiber points are not roots of any b_w (w<=200) [float, corroboration]' % v0_12)

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY a2 pass=%d fail=%d' % (NPASS, NFAIL))
