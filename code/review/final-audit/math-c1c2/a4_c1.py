# -*- coding: utf-8 -*-
"""final-audit / math-c1c2 / a4 : section C-1 (02_C1.md), with emphasis on T1.3(2) and the c_m / residue claim.
No import of core/polylib."""
import sys, os, time
from fractions import Fraction as Fr
from decimal import Decimal as D, getcontext
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


# ---------------------------------------------------------------- rational polynomial helpers
def qtrim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def qdivmod(a, b):
    a = [Fr(x) for x in a]
    b = qtrim([Fr(x) for x in b])
    q = [Fr(0)] * max(1, len(a) - len(b) + 1)
    a = qtrim(a)
    while len(a) >= len(b) and a:
        c = a[-1] / b[-1]
        d = len(a) - len(b)
        q[d] = c
        for i, bi in enumerate(b):
            a[i + d] -= c * bi
        a = qtrim(a)
    return q, a


def qgcd(a, b):
    a, b = qtrim([Fr(x) for x in a]), qtrim([Fr(x) for x in b])
    while b:
        _, r = qdivmod(a, b)
        a, b = b, r
    return [x / a[-1] for x in a]


def berlekamp_massey(seq):
    """over Q; returns connection polynomial C (C[0]=1) of minimal length L"""
    seq = [Fr(x) for x in seq]
    Cc, B = [Fr(1)], [Fr(1)]
    L, mm, b = 0, 1, Fr(1)
    for n in range(len(seq)):
        d = seq[n] + sum(Cc[i] * seq[n - i] for i in range(1, L + 1))
        if d == 0:
            mm += 1
        elif 2 * L <= n:
            T = Cc[:]
            coef = d / b
            Cc = Cc + [Fr(0)] * (len(B) + mm - len(Cc))
            for i, Bi in enumerate(B):
                Cc[i + mm] -= coef * Bi
            L, B, b, mm = n + 1 - L, T, d, 1
        else:
            coef = d / b
            Cc = Cc + [Fr(0)] * (len(B) + mm - len(Cc))
            for i, Bi in enumerate(B):
                Cc[i + mm] -= coef * Bi
            mm += 1
    return qtrim(Cc), L


# ---------------------------------------------------------------- T1.3(2)
MM = 14
bad_gcd, bad_bm, bad_rev, bad_rec, bad_deg = [], [], [], [], []
for m in range(0, MM + 1):
    P = P_poly(m)
    W = W_poly(m)
    g = qgcd(W, P)
    if g != [Fr(1)]:
        bad_gcd.append(m)
    if not (len(W) - 1 == 3 * m and W[-1] == (-1) ** m * factorial(m) and len(P) - 1 == 3 * m + 1 and P[0] == 1):
        bad_deg.append(m)
    col = dp_total(m, 6 * m + 8)
    Cc, L = berlekamp_massey(col)
    if L != 3 * m + 1 or qtrim(Cc) != [Fr(c) for c in P]:
        bad_bm.append((m, L))
    # reversal = (y-1) prod (y^3 - y^2 - i)
    rev = list(reversed(P))                      # y^{3m+1} P(1/y), low->high
    target = [-1, 1]
    for i in range(1, m + 1):
        target = pmul(target, [-i, 0, -1, 1])
    if ptrim(rev) != ptrim(target):
        bad_rev.append(m)
    # recurrence with connection polynomial P holds for every k >= 3m+1 on DP data (k<=6m+8)
    for k in range(3 * m + 1, len(col)):
        if sum(P[i] * col[k - i] for i in range(len(P))) != 0:
            bad_rec.append((m, k))
            break
rep(not bad_gcd and not bad_deg, 'T1.3(2).gcd', 'gcd(W_m,P_m)=1 (Fraction Euclid), deg W_m=3m with lc (-1)^m m!, deg P_m=3m+1, P_m(0)=1, 0<=m<=%d; bad=%s %s' % (MM, bad_gcd, bad_deg))
rep(not bad_bm and not bad_rec, 'T1.3(2).BM', 'Berlekamp-Massey on DP data U_0..U_{6m+8}(m): linear complexity 3m+1, connection polynomial == P_m; '
    'recurrence holds for all 3m+1<=k<=6m+8; 0<=m<=%d; bad=%s %s' % (MM, bad_bm, bad_rec))
rep(not bad_rev, 'T1.3(2).reversal', 'y^{3m+1} P_m(1/y) == (y-1) prod_{i=1}^m (y^3-y^2-i) exactly, 0<=m<=%d' % MM)

# W_4(1/2) and W_1 - b_1
W4 = W_poly(4)
w4h = sum(Fr(c) * Fr(1, 2) ** n for n, c in enumerate(W4))
W1 = W_poly(1)
rep(w4h == Fr(645, 512) and ptrim(padd(W1, pscale(b_poly(1), -1))) == [0, 1, 1], 'T1.3(2).facts',
    'W_4(1/2)=%s (claimed 645/512); W_1-b_1 = x+x^2' % w4h)

# reducible b_i: i = y^2(y-1), factorization and discriminant
ok = True
for y in range(2, 8):
    i = y * y * (y - 1)
    f = pmul([1, -y], [1, y - 1, y * (y - 1)])
    if ptrim(f) != ptrim(b_poly(i)):
        ok = False
    disc = (y - 1) ** 2 - 4 * y * (y - 1)
    if disc != -(y - 1) * (3 * y + 1) or disc >= 0:
        ok = False
# rational roots of b_i only for those i (i<=400)
for i in range(1, 401):
    has = any(z ** 3 - z ** 2 - i == 0 for z in range(-50, 50))
    if has != any(y * y * (y - 1) == i for y in range(2, 50)):
        ok = False
# discriminant of z^3 - z^2 - i
for i in range(1, 61):
    a, b, c, d = 1, -1, 0, -i
    disc = 18 * a * b * c * d - 4 * b ** 3 * d + b * b * c * c - 4 * a * c ** 3 - 27 * a * a * d * d
    if disc != -i * (4 + 27 * i):
        ok = False
rep(ok, 'T1.3(2)(3).algebra', 'b_{y^2(y-1)}=(1-yx)(1+(y-1)x+y(y-1)x^2), quadratic disc -(y-1)(3y+1)<0 (y<=7); z^3-z^2-i has an integer root iff i=y^2(y-1) (i<=400); disc(z^3-z^2-i)=-i(4+27i) (i<=60)')

# x W_m = 1 - P_m - x sum_{j<m} P_j  (T1.3(1))
bad = []
for m in range(0, 16):
    lhs = [0] + W_poly(m)
    rhs = padd([1], pscale(P_poly(m), -1))
    s = []
    for j in range(0, m):
        s = padd(s, P_poly(j))
    rhs = padd(rhs, pscale([0] + s, -1))
    if ptrim(lhs) != ptrim(rhs):
        bad.append(m)
rep(not bad, 'T1.3(1).closed', 'x W_m = 1 - P_m - x sum_{j<m} P_j as polynomials, m<=15; bad=%s' % bad)

# ---------------------------------------------------------------- T1.3(4): c_m and residue (high precision)
getcontext().prec = 220


def dpoly(poly, x):
    r = D(0)
    for c in reversed(poly):
        r = r * x + D(c)
    return r


def rho(m):
    y = D(2)
    for _ in range(400):
        f = y ** 3 - y ** 2 - m
        fp = 3 * y ** 2 - 2 * y
        y2 = y - f / fp
        if abs(y2 - y) < D(10) ** (-210):
            y = y2
            break
        y = y2
    return y


claimed = {1: D('2.2096081318'), 2: D('7.8411192294'), 3: D('28.976857317')}
lines = []
ok = True
KBIG = 3000
for m in range(1, 9):
    r = rho(m)
    xm = 1 / r
    G = dpoly(W_poly(m - 1), xm) / dpoly(P_poly(m - 1), xm)
    cm = (G + m * xm * xm) / (xm * (1 + 3 * m * xm * xm))
    col = dp_total(m, KBIG) if m <= 3 else dp_total(m, 1200)
    kk = len(col) - 1
    ratio = D(col[kk]) / (cm * r ** kk)
    err = abs(ratio - 1)
    # residue of W_m/P_m at x_m
    P = P_poly(m)
    dP = [n * P[n] for n in range(1, len(P))]
    res = dpoly(W_poly(m), xm) / dpoly(dP, xm)
    rerr = abs(res + cm * xm)
    # c_m via the second closed form of T5.1(3) as an extra cross-check
    alt = r * (r ** (3 * m + 1) / factorial(m) - sum(r ** (3 * i) / factorial(i) for i in range(m))) / (3 * r - 2)
    aerr = abs(alt - cm)
    lines.append('#   m=%d rho=%s c_m=%s |U_%d/(c rho^k)-1|=%.2e |res+c x|=%.1e |alt-c|=%.1e'
                 % (m, str(+r)[:16], str(+cm)[:16], kk, float(err), float(rerr), float(aerr)))
    if m <= 3:
        if err > D(10) ** -100 or rerr > D(10) ** -150 or aerr > D(10) ** -150:
            ok = False
        if abs(cm - claimed[m]) > D(10) ** -9 * 2:
            ok = False
    else:
        if err > D(10) ** -10 or rerr > D(10) ** -150 or aerr > D(10) ** -150:
            ok = False
    if m == 1:
        c1 = (10 + 15 * r + 17 * r * r) / 31
        if abs(c1 - cm) > D(10) ** -150:
            ok = False
print('\n'.join(lines))
rep(ok, 'T1.3(4).cm_residue', 'c_m=(G_{m-1}(x_m)+m x_m^2)/(x_m(1+3m x_m^2)) satisfies U_k(m)/(c_m rho_m^k) -> 1 (m=1..3 at k=3000: err<1e-100; m<=8 at k=1200: <1e-10); '
    'Res_{x_m} W_m/P_m = W_m(x_m)/P_m\'(x_m) == -c_m x_m (to 1e-150); c_1..c_3 match 06 decimals; c_1=(10+15rho+17rho^2)/31 [decimal, 220 digits]')

# dominance facts used in the proof
ok = True
for i in range(1, 30):
    r = rho(i)
    if not (r > 1 and r ** 3 > i and D(i) / r < r * r and (i == 1 or r > rho(i - 1))):
        ok = False
    f_next = r ** 3 - r ** 2 - (i + 1)
    if abs(f_next + 1) > D(10) ** -150:
        ok = False
rep(ok, 'T1.3(4).dominance', 'rho_i>1, rho_i^3>i, |w|^2=i/rho_i<rho_i^2, f_{i+1}(rho_i)=-1, rho strictly increasing (i<30) [decimal]')

# ---------------------------------------------------------------- T1.4 numbers via inversion from DP
KN = 40
cols = {m: dp_total(m, KN) for m in range(0, KN + 1)}


def N(k, q):
    if q < 0:
        return 0
    if k == 0:
        return 1 if q == 0 else 0
    return sum((-1) ** (q - i) * C(q, i) * cols[i - 1][k] for i in range(1, q + 1))


ok = all(N(k, k) == 2 for k in range(2, KN + 1)) and all(N(k, k - 1) == k * k - k - 4 for k in range(4, KN + 1))
ok = ok and N(3, 2) == 4 and N(2, 1) == 1 and N(4, 3) == 8 and 3 * 3 - 3 - 4 != 4
# triangle recurrence with the two alternative initial conventions
def tri(Kmax, conv):
    T = {}
    def get(k, q):
        if q < 0:
            return 0
        if k == -1:
            return (1 if q == 0 else 0) if conv == 'ext' else 0
        if k == -2:
            return 0
        if k < -2:
            return 0
        return T.get((k, q), 0)
    T[(0, 0)] = 1
    start = 1 if conv == 'ext' else 1
    for k in range(start, Kmax + 1):
        for r in range(-1, k):
            if r < 0:
                continue
            v = get(k - 1, r) + get(k - 1, r + 1) + r * (get(k - 3, r - 1) + 2 * get(k - 3, r) + get(k - 3, r + 1))
            T[(k, r + 1)] = v
    return T


Text = tri(30, 'ext')
Tzero = tri(3, 'zero')
ok_ext = all(Text.get((k, q), 0) == N(k, q) for k in range(1, 31) for q in range(1, k + 1))
ok_zero_fail = Tzero.get((2, 2)) == 1
rep(ok and ok_ext and ok_zero_fail, 'T1.4.numbers', 'N(k,k)=2 (2<=k<=40), N(k,k-1)=k^2-k-4 (4<=k<=40), N(3,2)=4, N(2,1)=1, N(4,3)=8; '
    'triangle recurrence from N(0,0)=1 + zero boundary gives N(2,2)=1 (wrong); with N(-1,0)=1,N(-1,q>0)=0,N(-2,.)=0 it reproduces N for all 1<=k<=30')

# ---------------------------------------------------------------- T1.5 note examples
from math import comb as _c


def Cgen(a, b):
    if b < 0:
        return 0
    num = 1
    for t in range(b):
        num *= (a - t)
    return Fr(num, factorial(b))


S2 = stirling2(20)
ok = (S2[2][1] * Cgen(-1, 2) == 1) and (Cgen(1, 0) * 1 + Cgen(-1, 1) * 5 == -4) and c_series(5, 3)[1] == 1
rep(ok, 'T1.5.note', 'generalized binomials: m=1,n=0,s=1 term S(2,1)C(-1,2)=1; c_5(1) summed to j<=1 gives 1-5=-4, true c_5(1)=1')

# ---------------------------------------------------------------- T1.7 h_3 with h_2=1
# h polynomials as coefficient lists in t; h_k = h_{k-1} + t(1-t)[(1-t)h'_{k-3} + (k-2) h_{k-3}]
def hrec(h2):
    h = {0: [1], 1: [1], 2: h2}
    for k in range(3, 8):
        hp = [n * h[k - 3][n] for n in range(1, len(h[k - 3]))] or [0]
        inner = padd(pmul([1, -1], hp), pscale(h[k - 3], k - 2))
        h[k] = ptrim(padd(h[k - 1], pmul([0, 1, -1], inner)))
    return h


hA = hrec([1, 1])
hB = hrec([1])
ok = hA[3] == [1, 2, -1] and hA[4] == [1, 4, -3] and hA[5] == [1, 8, -5, -2] and hA[6] == [1, 14, -7, -8, 2] and hB[3] == [1, 1, -1]
# h_k via sum_q N(k,q) t^{q-1} (1-t)^{k-q}
for k in range(1, 8):
    hk = []
    for q in range(1, k + 1):
        term = [0] * (q - 1) + [N(k, q)]
        for _ in range(k - q):
            term = pmul(term, [1, -1])
        hk = padd(hk, term)
    if ptrim(hk) != hA[k]:
        ok = False
rep(ok, 'T1.7.h', 'h_3..h_6 from h_0=1,h_1=1,h_2=1+t match the prompt; h_2=1 would give h_3=1+t-t^2; recurrence == sum_q N(k,q)t^{q-1}(1-t)^{k-q} (k<=7)')

# ---------------------------------------------------------------- T1.8 Num_q
ok = True
for q in range(1, 9):
    # sum_k N(k,q) x^k up to x^40, times P_{q-1}
    ser = [N(k, q) for k in range(0, KN + 1)]
    num = pmul(P_poly(q - 1), ser, KN)
    num_t = ptrim(num[:3 * q + 2])
    tail_zero = all(v == 0 for v in num[3 * q - 1:KN + 1])
    low = next(i for i, v in enumerate(num_t) if v)
    if not (tail_zero and len(num_t) - 1 == 3 * q - 2 and num_t[-1] == factorial(q - 1)):
        ok = False
    if q >= 2 and not (low == q and num_t[q] == 2):
        ok = False
    if q == 1 and num_t != [0, 1]:
        ok = False
rep(ok, 'T1.8.Num', 'Num_q=P_{q-1} sum_k N(k,q)x^k: polynomial of degree 3q-2, lc (q-1)!, lowest term 2x^q for q>=2, Num_1=x (q<=8)')

# ---------------------------------------------------------------- T1.2 and T1.9 leading coefficients
def interp(points):
    """Lagrange interpolation over Q; returns coefficient list low->high"""
    n = len(points)
    coeffs = [Fr(0)] * n
    for i, (xi, yi) in enumerate(points):
        num = [Fr(1)]
        den = Fr(1)
        for j, (xj, _) in enumerate(points):
            if j != i:
                num = [Fr(0)] + num
                for t in range(len(num) - 1):
                    num[t] -= xj * num[t + 1]
                den *= (xi - xj)
        for t in range(len(num)):
            coeffs[t] += yi * num[t] / den
    return qtrim(coeffs)


ok = True
for k in range(0, 9):
    pts = [(Fr(m), Fr(cols[m][k])) for m in range(0, k + 3)]
    u = interp(pts)
    deg = len(u) - 1
    lc = u[-1]
    if k >= 1 and sum(c * Fr(-1) ** n for n, c in enumerate(u)) != 0:
        ok = False
    if deg != k or (k >= 2 and lc != Fr(2, factorial(k))) or (k <= 1 and lc != 1):
        ok = False
    if k >= 1:
        # a_k(n): E(n)=u(n/2)^2, O(n)=u((n+1)/2)u((n-1)/2); p=(E+O)/2, q=(E-O)/2 as polynomials in n
        def ev(c, x):
            return sum(cc * x ** e for e, cc in enumerate(c))
        npts = [Fr(n) for n in range(0, 4 * k + 4)]
        Ev = [ev(u, n / 2) ** 2 for n in npts]
        Od = [ev(u, (n + 1) / 2) * ev(u, (n - 1) / 2) for n in npts]
        p = interp([(n, (e + o) / 2) for n, e, o in zip(npts, Ev, Od)])
        qq = interp([(n, (e - o) / 2) for n, e, o in zip(npts, Ev, Od)])
        if len(p) - 1 != 2 * k or p[-1] != lc ** 2 / 4 ** k:
            ok = False
        if len(qq) - 1 != 2 * k - 2 or qq[-1] != lc ** 2 * k / (2 * 4 ** k):
            ok = False
        # sanity: a_k(n) = p(n)+(-1)^n q(n) equals product of U's
        for n in range(0, 12):
            a = cols[(n + 1) // 2][k] * cols[n // 2][k]
            if ev(p, Fr(n)) + (-1) ** n * ev(qq, Fr(n)) != a:
                ok = False
rep(ok, 'T1.2/T1.9.lc', 'u_k: deg k, lc 2/k! (k>=2), u_k(-1)=0; a_k(n)=p(n)+(-1)^n q(n) with deg p=2k, lc c^2/4^k, deg q=2k-2, lc c^2 k/(2*4^k) (k<=8)')

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY a4 pass=%d fail=%d' % (NPASS, NFAIL))
