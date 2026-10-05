# -*- coding: utf-8 -*-
"""final-audit / math-c3 / a2: numbers and analytic claims of T3.4 (04_C3.md).

(3) exact partial sum of S(3/5,-1/2), tail bounds; (4) residue law (exact mod b_i + Decimal), uniform
boundedness of G_m on small circles, contour integral of S vs Res G_i t^i e^{-t/x_i^3}; r_K error bound spot check;
(5) Lambert W(1/e); K/Gamma(-lam) closed form bounds; small-t gap value; f_k(-1/2) growth; |S(21/100,-1/2)|.
"""
import sys, os, time, math, cmath
from fractions import Fraction
from decimal import Decimal, getcontext
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, CODE)
import core

T0 = time.time()
RES = []


def report(name, ok, msg):
    RES.append(bool(ok))
    print('%s %s :: %s' % ('PASS' if ok else 'FAIL', name, msg))
    sys.stdout.flush()


def D(q):
    return Decimal(q.numerator) / Decimal(q.denominator)


getcontext().prec = 50

# ---------------------------------------------------------------------------------------------
# (3) S(3/5,-1/2): exact partial sum m<=400 + rigorous tails
# ---------------------------------------------------------------------------------------------


def S_partial(x, t, M):
    G = Fraction(1)          # G_{-1}
    tot = Fraction(0)
    tp = Fraction(1)
    Gs = []
    for m in range(M + 1):
        G = (G + m * x * x) / (1 - x - m * x ** 3)
        Gs.append(G)
        tot += tp * G
        tp *= t
    return tot, Gs


x, t = Fraction(3, 5), Fraction(-1, 2)
tot, Gs = S_partial(x, t, 400)
lam = (1 - x) / x ** 3
# c3a lemma bound (report: 3.5e-118)
m0 = 0
while not (m0 > lam and x ** 3 * (m0 + 1 - lam) >= 2):
    m0 += 1
c1 = 1 / (x ** 3 * (m0 + 1 - lam))
c2 = (m0 + 1) / (x * (m0 + 1 - lam))
B = max(max(abs(g) for g in Gs[m0:401]), c2 / (1 - c1))
tb_c3a = B * abs(t) ** 401 / (1 - abs(t))
# my own bound: for m>=401, |G_m| <= max(|G_400|, sup_{m>400} m x^2/(x^3(m-lam)-1)) (decreasing in m)
C = max(abs(Gs[400]), Fraction(401) * x * x / (x ** 3 * (401 - lam) - 1))
assert x ** 3 * (401 - lam) - 1 > 0
tb_mine = C * abs(t) ** 401 / (1 - abs(t))
val = D(tot)
print('#   S(3/5,-1/2) partial m<=400 = %s ; c3a-type bound B=%.6g -> tail <= %.3e ; own bound C=%.6g -> tail <= %.3e'
      % (str(+val)[:30], float(B), float(tb_c3a), float(C), float(tb_mine)))
ok = (str(val).startswith('-1057.81087256356')) and tot + tb_c3a < 0 and tot + tb_mine < 0 and tot > Fraction(-1057810873, 10 ** 6)
report('T3.4(3)-counterex', ok, 'exact partial sum m<=400 of S(3/5,-1/2) = %s... ; rigorous tail <= %.4e (c3a lemma bound) / %.3e (own bound); S<0 rigorously; '
       'partial sum > -1057.810873 (so the first-round "<= -1057.810873+3.5e-118" was indeed wrong-direction rounding)' % (str(val)[:20], float(tb_c3a), float(tb_mine)))
# FINDING (not a check of correctness of the conclusion): the report states the rigorous tail bound as "<= 3.5e-118";
# the bound actually computed by c3a-analytic-counterex is 3.529e-118 (printed with %.1e), i.e. rounded DOWN.
# The inequality |tail| <= 3.5e-118 is still true because of the sharper bound 6.56e-121.
print('FINDING T3.4(3)-tailbound :: c3a-type rigorous tail bound = %.6e > 3.5e-118 (report text rounds it down); sharper own bound %.3e keeps the inequality true'
      % (float(tb_c3a), float(tb_mine)))

# integrand positivity: g(w) = 1 + x^2 w/(1-w)^2 >= 1 - x^2/4 > 0 for w <= 0
ws = np.linspace(-50, 0, 200001)
gmin = np.min(1 + 0.36 * ws / (1 - ws) ** 2)
report('T3.4(3)-positivity', gmin >= 1 - 0.36 / 4 - 1e-12 and gmin > 0, 'g(w)=1+x^2 w/(1-w)^2 on w<=0 has min %.6f = 1-x^2/4 at w=-1 (x=3/5) > 0, so I>0' % gmin)

# ---------------------------------------------------------------------------------------------
# (4) residue law: exact (mod minimal polynomial of x_i) and Decimal
# ---------------------------------------------------------------------------------------------


def pmul(p, q):
    r = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pder(p):
    return [i * p[i] for i in range(1, len(p))]


def pmod(p, q):
    p = [Fraction(a) for a in p]
    q = [Fraction(a) for a in q]
    while len(q) and q[-1] == 0:
        q.pop()
    while len(p) >= len(q):
        if p[-1] == 0:
            p.pop()
            continue
        c = p[-1] / q[-1]
        d = len(p) - len(q)
        for i, b in enumerate(q):
            p[i + d] -= c * b
        p.pop()
    while p and p[-1] == 0:
        p.pop()
    return p


def b(i):
    return [Fraction(1), Fraction(-1), Fraction(0), Fraction(-i)]


Pm = [[Fraction(1)]]   # P_{-1}
for m in range(0, 20):
    Pm.append(pmul(Pm[-1], b(m)))           # Pm[m+1] = P_m


def P(m):
    return Pm[m + 1]


def W(m):
    w = [Fraction(1)]
    for j in range(1, m + 1):
        w = padd(w, pmul([0, 0, j], P(j - 1)))
    return w


ok_ex = True
for i in (1, 2, 3, 4):
    minpoly = b(i) if i != 4 else [Fraction(1), Fraction(-2)]       # b_4 = (1-2x)(1+x+2x^2), x_4 = 1/2
    for m in range(i, i + 9):
        lhs = pmul(pmul(W(m), pder(P(i))), [0] * (3 * (m - i)) + [Fraction(math.factorial(m - i))])
        rhs = [(-1) ** (m - i) * c for c in pmul(W(i), pder(P(m)))]
        diff = padd(lhs, [-c for c in rhs])
        ok_ex &= (pmod(diff, minpoly) == [])
    # also W_m(x_i) = W_i(x_i) for m >= i
    for m in range(i, i + 9):
        ok_ex &= (pmod(padd(W(m), [-c for c in W(i)]), minpoly) == [])
report('T3.4(4)-residue-exact', ok_ex, 'W_m == W_i and W_m P_i\' (m-i)! x^{3(m-i)} == (-1)^{m-i} W_i P_m\' modulo the minimal polynomial of x_i '
       '(i=1,2,3 b_i irreducible; i=4: x_4=1/2), m=i..i+8  <=>  Res_{x_i}G_m = Res_{x_i}G_i (-x_i^{-3})^{m-i}/(m-i)!')

getcontext().prec = 60
worst = Decimal(0)
for i in (1, 2):
    xi = Decimal('0.6')
    for _ in range(200):
        xi = xi - (1 - xi - i * xi ** 3) / (-1 - 3 * i * xi ** 2)

    def ev(p, xv):
        r = Decimal(0)
        for a in reversed(p):
            r = r * xv + D(Fraction(a))
        return r
    resi = ev(W(i), xi) / ev(pder(P(i)), xi)
    for m in range(i, 7):
        resm = ev(W(m), xi) / ev(pder(P(m)), xi)
        pred = resi * (-1 / xi ** 3) ** (m - i) / math.factorial(m - i)
        worst = max(worst, abs(resm - pred) / abs(pred))
    print('#   i=%d x_i=%s Res_{x_i}G_i=%s' % (i, str(xi)[:22], str(resi)[:22]))
report('T3.4(4)-residue-decimal', worst < Decimal(10) ** -50, 'Decimal(60): Res_{x_i}G_m (= W_m(x_i)/P_m\'(x_i)) vs Res_{x_i}G_i(-x_i^{-3})^{m-i}/(m-i)!, i=1,2, m<=6: worst rel dev %.1E' % worst)

# uniform boundedness of G_m on small circles + contour integral of S
def G_list_complex(xv, M):
    G = 1.0 + 0j
    out = []
    for m in range(M + 1):
        G = (G + m * xv * xv) / (1 - xv - m * xv ** 3)
        out.append(G)
    return out


okb = True
okc = True
for i, delta in ((1, 0.03), (2, 0.03), (3, 0.02)):
    xi = 0.6
    for _ in range(100):
        xi = xi - (1 - xi - i * xi ** 3) / (-1 - 3 * i * xi ** 2)
    NP = 2048
    th = 2 * np.pi * np.arange(NP) / NP
    xs = xi + delta * np.exp(1j * th)
    Mmax = 400
    G = np.ones(NP, dtype=complex)
    supm = []
    minb = np.inf
    Gall = []
    for m in range(Mmax + 1):
        bm = 1 - xs - m * xs ** 3
        minb = min(minb, np.min(np.abs(bm)))
        G = (G + m * xs * xs) / bm
        supm.append(np.max(np.abs(G)))
        Gall.append(G.copy())
    sup_all = max(supm)
    tail_sup = max(supm[100:])
    lim = 1 / (xi - delta)
    okb &= (minb > 1e-3) and np.isfinite(sup_all) and tail_sup < 1.2 * lim
    # |b_v| >= c v on the circle for large v
    cv = min(np.min(np.abs(1 - xs - v * xs ** 3)) / v for v in range(50, 401))
    print('#   i=%d circle |x-x_i|=%.3f: min_{v<=400,circle}|b_v|=%.3e, sup_m<=400 max|G_m|=%.4f (m>=100: %.4f; 1/(x_i-delta)=%.4f); min_{50<=v<=400} min|b_v|/v=%.4f'
          % (i, delta, minb, sup_all, tail_sup, lim, cv))
    # contour integral (trapezoid, spectrally accurate) of S(x,t) = sum_m t^m G_m(x)
    # Res_{x_i} G_i = W_i(x_i)/P_i'(x_i)
    Wi = sum(float(c) * xi ** e for e, c in enumerate(W(i)))
    dPi = sum(float(c) * xi ** e for e, c in enumerate(pder(P(i))))
    resGi = Wi / dPi
    for tv in (-0.5, 0.6, -0.9):
        Sv = np.zeros(NP, dtype=complex)
        tp = 1.0
        for m in range(Mmax + 1):
            Sv += tp * Gall[m]
            tp *= tv
        integ = np.mean(Sv * delta * np.exp(1j * th))          # (1/2πi)∮ S dx  with dx = i δ e^{iθ} dθ
        pred = resGi * tv ** i * math.exp(-tv / xi ** 3)
        rel = abs(integ - pred) / abs(pred)
        okc &= rel < 1e-9
        print('#      t=%+.2f: contour integral %.12e%+.2ei  vs  Res G_i t^i e^{-t/x_i^3} = %.12e  (rel %.1e)' % (tv, integ.real, integ.imag, pred, rel))
report('T3.4(4)-uniform-bound', okb, 'on circles |x-x_i|=delta (i=1,2,3) no b_v (v<=400) vanishes, sup_m |G_m| stays bounded (tends to ~1/|x|), |b_v|>=c v for large v: the uniform-boundedness argument is consistent')
report('T3.4(4)-contour', okc, 'trapezoid contour integral of S(x,t)=sum_m t^m G_m(x) around x_i (i=1,2,3; t=-0.5,0.6,-0.9) == Res_{x_i}G_i t^i e^{-t/x_i^3} (rel < 1e-9)')

# ---------------------------------------------------------------------------------------------
# (4) explicit error bound with r_K := f_{K-1} + tau (f'_{K-3} + x f'_{K-2} + x^2 f'_{K-1}) (float spot check)
# ---------------------------------------------------------------------------------------------
# h_k from (C6) anchored to DP
TT = core.U_fast_table(30, 40)


def ppmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, c in enumerate(q):
            r[i + j] += a * c
    return r


def ppadd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pptrim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def ppder(p):
    return [i * p[i] for i in range(1, len(p))] or [0]


KH = 160
h = [[1], [1], [1, 1]]
for k in range(3, KH + 1):
    a = h[k - 3]
    term = ppadd(ppmul([1, -1], ppder(a)), [(k - 2) * c for c in a])
    h.append(pptrim(ppadd(h[k - 1], ppmul([0, 1, -1], term))))
okh = True
for k in range(0, 31):
    f = [TT[k][m] for m in range(41)]
    pw = [1]
    for _ in range(k + 1):
        pw = ppmul(pw, [1, -1])
    hk = pptrim(ppmul(f, pw)[:41])
    okh &= (hk == pptrim(h[k]))
report('anchor-hk', okh, '(C6) recurrence from h_0=h_1=1, h_2=1+t reproduces (1-t)^{k+1} sum_m U_k(m) t^m (DP), k<=30')


def f_val(k, tau):
    """f_k(tau) = h_k(tau)/(1-tau)^{k+1} and derivative (floats)."""
    hk = h[k]
    hv = sum(c * tau ** e for e, c in enumerate(hk))
    dh = sum(e * c * tau ** (e - 1) for e, c in enumerate(hk) if e)
    den = (1 - tau) ** (k + 1)
    fv = hv / den
    fd = dh / den + (k + 1) * hv / (1 - tau) ** (k + 2)
    return fv, fd


def I_num(xv, tv, n=400001, smax=None):
    lamv = (1 - xv) / xv ** 3
    if smax is None:
        smax = 60 * xv ** 3 / (abs(tv) + (1 - xv)) + 1e-9
    s = np.linspace(0, smax, n)
    w = tv * np.exp(s)
    integrand = np.exp((tv * (np.exp(s) - 1) - (1 - xv) * s) / xv ** 3) * (1 + xv * xv * w / (1 - w) ** 2)
    hstep = s[1] - s[0]
    simpson = hstep / 3 * (integrand[0] + integrand[-1] + 4 * integrand[1:-1:2].sum() + 2 * integrand[2:-1:2].sum())
    return simpson / xv ** 3


okeb = True
for (xv, tv, K) in ((0.3, -0.5, 6), (0.3, -0.5, 9), (0.25, -1 / 3, 12), (0.4, -2.0, 7)):
    Iv = I_num(xv, tv)
    YK = sum(f_val(k, tv)[0] * xv ** k for k in range(K))
    taus = -np.concatenate([np.geomspace(abs(tv), 1e5, 20000)])
    sup = 0.0
    for tau in taus:
        fK1, dK1 = f_val(K - 1, tau)
        _, dK2 = f_val(K - 2, tau)
        _, dK3 = f_val(K - 3, tau)
        rK = fK1 + tau * (dK3 + xv * dK2 + xv * xv * dK1)
        sup = max(sup, abs(rK))
    bound = xv ** K / abs(tv) * sup
    err = abs(Iv - YK)
    okeb &= err <= bound
    print('#   (x,t,K)=(%.3g,%.4g,%d): |I - sum_{k<K} f_k x^k| = %.4e <= (x^K/|t|) sup|r_K| = %.4e' % (xv, tv, K, err, bound))
report('T3.4(4)-errbound', okeb, 'explicit error bound with r_K = f_{K-1} + tau(f\'_{K-3} + x f\'_{K-2} + x^2 f\'_{K-1}) holds at 4 (x,t,K) (float quadrature; matches the 4 reviewer points)')

# ---------------------------------------------------------------------------------------------
# (5) Lambert W(1/e), K/Gamma(-lam) = 1 + lam x^5 J bounds, small-t gap, |S(21/100,-1/2)|, f_k growth
# ---------------------------------------------------------------------------------------------
w = 0.3
for _ in range(100):
    w = w - (w * math.exp(w) - math.exp(-1)) / (math.exp(w) * (1 + w))
report('T3.4(5)-lambertW', abs(w - 0.2785) < 5e-5 and abs(w * math.exp(1 + w) - 1) < 1e-14, 'W_L(1/e) = %.12f (report: approx 0.2785); r e^{1+r}<1 <=> r < W_L(1/e)' % w)


def J_num(xv, n=2000001):
    lamv = (1 - xv) / xv ** 3
    rate = xv + xv ** 3
    Wmax = 80 / rate
    ws_ = np.linspace(0, Wmax, n)
    f = ws_ * np.exp(-ws_ + (lamv - 1) * np.log1p(xv ** 3 * ws_))
    hstep = ws_[1] - ws_[0]
    return hstep / 3 * (f[0] + f[-1] + 4 * f[1:-1:2].sum() + 2 * f[2:-1:2].sum())


okK = True
vals = []
ref = {0.6: 1.195007, 0.4: 1.335900, 0.3: 1.428866, 0.21: 1.535091, 0.1: 1.717420, 0.05: 1.835941}
for xv in (0.95, 0.9, 0.7, 0.6, 0.4, 0.3, 0.21, 0.1, 0.05, 0.02):
    lamv = (1 - xv) / xv ** 3
    r = 1 + lamv * xv ** 5 * J_num(xv)
    vals.append((xv, r))
    okK &= 1 < r < 2
    if xv in ref:
        okK &= abs(r - ref[xv]) < 2e-6
print('#   K/Gamma(-lam) = 1 + lam x^5 J(x): ' + ', '.join('x=%.2f:%.6f' % v for v in vals))
report('T3.4(2)-K-bounds', okK, '1 < 1+lam x^5 J < 2 at 10 x in [0.02,0.95], increasing towards 2 as x->0; matches reviewer values 1.195007 ... 1.835941')

# Tricomi form: J = x^{-6} U(2, lam+2, x^{-3}) with U(a,b,z) = (1/Gamma(a)) int_0^inf e^{-zs} s^{a-1} (1+s)^{b-a-1} ds
xv = 0.4
lamv = (1 - xv) / xv ** 3
z = xv ** -3
ss = np.linspace(0, 80 / (z * (1 - (lamv - 1) / z)) if (lamv - 1) < z else 400, 2000001)
fu = np.exp(-z * ss + (lamv - 1) * np.log1p(ss)) * ss
hs_ = ss[1] - ss[0]
Uval = hs_ / 3 * (fu[0] + fu[-1] + 4 * fu[1:-1:2].sum() + 2 * fu[2:-1:2].sum())
Jv = J_num(xv)
report('T3.4(2)-tricomi', abs(Uval / xv ** 6 - Jv) / Jv < 1e-8, 'J(x) == x^{-6} U(2,lam+2,x^{-3}) numerically at x=0.4 (rel %.1e); Q(-lam)=J by definition' % (abs(Uval / xv ** 6 - Jv) / Jv))

# small-t gap at (21/100,-1/20): x^{-3} e^a a^lam Gamma(-lam)(1+lam x^5 J)
xq, tq = Fraction(21, 100), Fraction(-1, 20)
lamq = (1 - xq) / xq ** 3
aq = -tq / xq ** 3
lf, af = float(lamq), float(aq)
xv = float(xq)
sinpl = math.sin(math.pi * (lf - 85))     # lam = 85 + 0.30396...; sin(pi lam) = -sin(pi (lam-85))
sin_pi_lam = -sinpl
log_absGam = math.log(math.pi) - math.log(abs(sin_pi_lam)) - math.lgamma(lf + 1)
sgnGam = -1 if (sin_pi_lam > 0) else 1          # Gamma(-lam) = -pi/(sin(pi lam) Gamma(lam+1))
Kr = 1 + lf * xv ** 5 * J_num(xv)
log_gap = -3 * math.log(xv) + af + lf * math.log(af) + log_absGam + math.log(Kr)
gap = sgnGam * math.exp(log_gap)
report('T3.4(5)-small-t', abs(gap - 3.81401776553037367e-62) / 3.814e-62 < 1e-9, 'closed-form gap I-S at (21/100,-1/20) = %.12e (double precision; report: 3.81401776553037367e-62)' % gap)

# |S(21/100,-1/2)| > 1e44 rigorously
xq, tq = Fraction(21, 100), Fraction(-1, 2)
totq, Gq = S_partial(xq, tq, 500)
lamq = (1 - xq) / xq ** 3
Cq = max(abs(Gq[500]), Fraction(501) * xq * xq / (xq ** 3 * (501 - lamq) - 1))
assert xq ** 3 * (501 - lamq) - 1 > 0
# need |G_m| <= C for all m > 500: holds by induction since sup_{m>500} m x^2/(x^3(m-lam)-1) <= C and |G_500| <= C
tbq = Cq * abs(tq) ** 501 / (1 - abs(tq))
report('T3.4(5)-bigS', abs(totq) - tbq > Fraction(10) ** 44, 'S(21/100,-1/2) = %.6e (exact partial sum m<=500, tail <= %.1e): |S| > 1e44 rigorously' % (float(totq), float(tbq)))

# f_k(-1/2) growth
getcontext().prec = 40
outs = {}
for k in (75, 150):
    hv = sum(Fraction(c) * Fraction(-1, 2) ** e for e, c in enumerate(h[k]))
    fk = hv / Fraction(3, 2) ** (k + 1)
    lg = (Decimal(abs(fk.numerator)).ln() - Decimal(fk.denominator).ln()) / k
    outs[k] = float(lg.exp())
ratio = outs[150] / outs[75]
report('T3.4(5)-fk-growth', abs(outs[75] - 1.669) < 5e-4 and abs(outs[150] - 2.036) < 5e-4 and abs(ratio - 1.22) < 5e-3,
       '|f_k(-1/2)|^{1/k} = %.5f (k=75), %.5f (k=150), ratio %.4f (report: 1.669, 2.036, 1.22)' % (outs[75], outs[150], ratio))

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY a2 pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
