# -*- coding: utf-8 -*-
"""fixcheck：逐条核对 patch_final_audit.py 新文字里可计算的数学事实（只读；自写实现，core 只作交叉核对）。"""
import sys
import math
import cmath
from fractions import Fraction as F
from math import comb, factorial

ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
sys.path.insert(0, ROOT + r'\code')
import core  # noqa: E402

RES = []


def report(name, ok, desc):
    RES.append(bool(ok))
    print(('PASS ' if ok else 'FAIL ') + name + ' ' + desc, flush=True)


# ---------- 自写 U 表（三元组 DP） ----------
def good(a, b, c):
    return b == c or a >= max(b, c)


def U_col(m, K):
    n = m + 1
    out = [1]
    if K >= 1:
        out.append(n)
    if K >= 2:
        cnt = [[1] * n for _ in range(n)]
        out.append(n * n)
        for k in range(3, K + 1):
            new = [[0] * n for _ in range(n)]
            for a in range(n):
                for b in range(n):
                    v = cnt[a][b]
                    if v:
                        for c in range(n):
                            if good(a, b, c):
                                new[b][c] += v
            cnt = new
            out.append(sum(map(sum, cnt)))
    return out


KU, MU = 60, 14
Ucols = [U_col(m, KU) for m in range(MU + 1)]


def U(k, m):
    return Ucols[m][k]


T = core.U_fast_table(KU, MU)
report('own-DP', all(T[k][m] == U(k, m) for k in range(KU + 1) for m in range(MU + 1)),
       'own triple DP == core.U_fast_table (k<=60,m<=14)')


# ---------- (1) 03_C2: R_k:=U_k(1)=c_1(k+3)+c_1(k-2)-1 ----------
def cser(i, n):
    c = [0] * (n + 1)
    for t in range(n + 1):
        c[t] = (1 if t == 0 else 0) + (c[t - 1] if t >= 1 else 0) + (i * c[t - 3] if t >= 3 else 0)
    return c


c1 = cser(1, 80)


def cc(n):
    return c1[n] if n >= 0 else 0


report('Rk-formula', all(U(k, 1) == cc(k + 3) + cc(k - 2) - 1 for k in range(0, KU + 1)),
       'U_k(1)=c_1(k+3)+c_1(k-2)-1 with c_1(n<0)=0, 0<=k<=60; R_1..R_10=%s' % [U(k, 1) for k in range(1, 11)])

# ---------- (2) 03_C2: v_0 values ----------
lo, hi = 0.0, 1.0
for _ in range(200):
    mid = (lo + hi) / 2
    if 1 - mid - mid ** 3 > 0:
        lo = mid
    else:
        hi = mid
xi = lo
v12 = xi ** 3 / (1 - xi) ** 2
v23 = xi ** 5 / (1 - xi) ** 3
report('v0-values', abs(v12 - xi ** -3) < 1e-12 and 3.04 < v12 < 3.18 and abs(v23 - xi ** -4) < 1e-12 and abs(v23 - 4.61) < 0.005,
       'xi=%.10f: v_(1,2)=xi^-3=%.6f in (3.04,3.18); v_(2,3)=xi^5/(1-xi)^3=xi^-4=%.6f (~4.61)' % (xi, v12, v23))


# ---------- (3) 02_C1/06_C5: rho_0, tau_1 ----------
def rho(m):
    if m == 0:
        return 1.0
    lo_, hi_ = 1.0, 3.0 + m
    for _ in range(300):
        mid_ = (lo_ + hi_) / 2
        if mid_ ** 3 - mid_ ** 2 - m < 0:
            lo_ = mid_
        else:
            hi_ = mid_
    return lo_


r1 = rho(1)
tau1 = math.sqrt(r1 * (r1 - 1))
bq, cq = (r1 - 1), r1 * (r1 - 1)       # y^3-y^2-1 = (y-r1)(y^2+(r1-1)y+r1(r1-1))
z = (-bq + cmath.sqrt(bq * bq - 4 * cq)) / 2
report('tau1', abs(tau1 - 0.826) < 5e-4 and abs(abs(z) - tau1) < 1e-12 and tau1 < 1.0,
       'rho_1=%.9f, tau_1=sqrt(rho_1(rho_1-1))=%.6f = |complex root|=%.6f < rho_0=1' % (r1, tau1, abs(z)))


# ---------- (4) 04_C3: formal Laplace identity ----------
def egf_coeffs_e(j, n, NMAX):
    """a_N = N! [z^N] e^{jz}(e^z-1)^n/n!"""
    def exp_ser(a):
        return [F(a) ** t / factorial(t) for t in range(NMAX + 1)]

    def mul(p, q):
        r = [F(0)] * (NMAX + 1)
        for i, x in enumerate(p):
            if x:
                for k2, y in enumerate(q[:NMAX + 1 - i]):
                    r[i + k2] += x * y
        return r
    em1 = exp_ser(1)
    em1[0] -= 1
    s = exp_ser(j)
    for _ in range(n):
        s = mul(s, em1)
    return [s[t] * factorial(t) / factorial(n) for t in range(NMAX + 1)]


def h_complete(s, lo_, hi_):
    if s < 0:
        return 0
    dp = [1] + [0] * s
    for v in range(lo_, hi_ + 1):
        for t in range(1, s + 1):
            dp[t] += v * dp[t - 1]
    return dp[s]


NN = 22
ok = True
for j in range(0, 5):
    for n in range(0, 5):
        a = egf_coeffs_e(j, n, NN)
        for Nn in range(NN + 1):
            rhs = h_complete(Nn - n, j, j + n) if Nn >= n else 0
            ok &= (a[Nn] == rhs)
report('laplace-identity', ok,
       'N![s^N] of e^{jus}(e^{us}-1)^n/n! == [u^N] u^n/prod_{i=j}^{j+n}(1-iu), 0<=j,n<=4, N<=22')


# ---------- (5) 04_C3: K/Gamma bounds (float Simpson) ----------
def Jval(x):
    lam = (1 - x) / x ** 3
    a = x + x ** 3

    def f(v):
        return v * math.exp(-v / a + (lam - 1) * math.log1p(x ** 3 * v / a))
    n = 40000
    h = 80.0 / n
    s = f(0) + f(80.0)
    for i in range(1, n):
        s += (4 if i % 2 else 2) * f(i * h)
    return s * h / 3 / a ** 2


ok = True
rows = []
for x in (0.05, 0.1, 0.21, 0.3, 0.4, 0.6, 0.8, 0.95):
    lam = (1 - x) / x ** 3
    val = lam * x ** 5 * Jval(x)
    ub = (1 - x) / (1 + x * x) ** 2 if lam >= 1 else (1 - x) * x * x
    ok &= (0 < val <= ub + 1e-9) and ub < 1
    rows.append('x=%.2f lam=%.3g K/G=%.6f ub=%.6f' % (x, lam, 1 + val, 1 + ub))
report('K-ratio-bounds', ok, '1 < 1+lam x^5 J <= 1+bound < 2 at 8 points; ' + '; '.join(rows))

# ---------- (6) 05_C4: p_d data ----------
DM = 12
K = 4 * DM + 8
N = [[0] * (K + 2) for _ in range(K + 1)]
N[0][0] = 1
N[1][1] = 1
N[2][1] = 1
N[2][2] = 2
for k in range(3, K + 1):
    for q in range(1, k + 1):
        r = q - 1
        v = N[k - 1][r] + N[k - 1][r + 1]
        if r >= 1:
            v += r * (N[k - 3][r - 1] + 2 * N[k - 3][r] + N[k - 3][r + 1])
        N[k][q] = v
UT = core.U_fast_table(40, 41)
report('N-tri', all(core.N_from_U(UT, k, q) == N[k][q] for k in range(41) for q in range(k + 1)),
       'triangle N == core inclusion-exclusion (k<=40)')


def D(k, d):
    return N[k][k - d] if 0 <= k - d <= k else 0


def interp(xs, ys):
    n = len(xs)
    coeffs = [F(0)] * n
    for i in range(n):
        num = [F(1)]
        den = F(1)
        for j2 in range(n):
            if j2 != i:
                num = [F(0)] + num
                for t in range(len(num) - 1):
                    num[t] -= xs[j2] * num[t + 1]
                den *= (xs[i] - xs[j2])
        for t in range(n):
            coeffs[t] += ys[i] * num[t] / den
    return coeffs


def peval(p, x):
    s = F(0)
    for c in reversed(p):
        s = s * x + c
    return s


P = {}
for d in range(0, DM + 1):
    xs = list(range(2 * d + 2, 4 * d + 3))
    ys = [D(k, d) for k in xs]
    p = interp(xs, ys)
    assert all(peval(p, k) == D(k, d) for k in range(2 * d + 2, 4 * d + 9))
    P[d] = p
ok_lc = all(P[d][2 * d] == F(2, 2 ** d * factorial(d)) for d in range(DM + 1))
ok_rec = all(2 * d * P[d][2 * d] == P[d - 1][2 * d - 2] for d in range(1, DM + 1))
ok_r = all(P[d][2 * d - 1] / P[d][2 * d] == -(4 * d * d - 3 * d) for d in range(1, DM + 1))
report('lc-rd', ok_lc and ok_rec and ok_r, 'lc(p_d)=2/(2^d d!), 2d*lc(p_d)=lc(p_{d-1}), r_d=-(4d^2-3d) for d<=12')


def pbinom(y, b):
    r = F(1)
    for i in range(b):
        r *= F(y - i)
    return r / factorial(b)


ok = True
for d in range(1, 7):
    for c in range(-20, 21):
        s = 2 * d - c
        h = []
        for i in range(2 * d + 1):
            kk = s + i
            val = peval(P[d], kk) - sum(h[jj] * pbinom(kk + c - jj, 2 * d) for jj in range(i))
            h.append(val / pbinom(kk + c - i, 2 * d))
        ok &= all(peval(P[d], kk) == sum(h[jj] * pbinom(kk + c - jj, 2 * d) for jj in range(2 * d + 1))
                  for kk in range(s - 5, s + 2 * d + 6))
        ok &= (h[1] == peval(P[d], s + 1) - (2 * d + 1) * peval(P[d], s))
        ok &= any(hj < 0 for hj in h)
    ss = list(range(0, 2 * d + 1))
    qpoly = interp(ss, [peval(P[d], t + 1) - (2 * d + 1) * peval(P[d], t) for t in ss])
    ok &= (qpoly[2 * d] == -2 * d * P[d][2 * d]) and qpoly[2 * d] < 0
report('hstar1', ok, 'h*_1 = p_d(s+1)-(2d+1)p_d(s), s=2d-c; some h*_j<0; h*_1(s) has degree 2d, lc -2d*lc(p_d)<0 (d<=6, |c|<=20)')


def S2assoc(n, j):
    A = [[0] * (j + 2) for _ in range(n + 2)]
    A[0][0] = 1
    for nn in range(1, n + 1):
        for jj in range(0, j + 1):
            A[nn][jj] = jj * A[nn - 1][jj] + ((nn - 1) * A[nn - 2][jj - 1] if nn >= 2 and jj >= 1 else 0)
    return A[n][j]


St = core.stirling2_table(60)
ok = all(St[k][k - d] == sum(S2assoc(d + j, j) * comb(k, d + j) for j in range(0, d + 1))
         for d in range(0, 9) for k in range(d, 45))
ok_plain = all(St[k][k - d] == sum(St[d + j][j] * comb(k, d + j) for j in range(0, d + 1))
               for d in range(1, 3) for k in range(d, 10))
report('S2-identity', ok and not ok_plain,
       'S(k,k-d)=sum_j S_2(d+j,j)C(k,d+j) holds with associated Stirling (blocks>=2), 0<=d<=8, d<=k<45; fails if S_2 read as plain S')


def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j2, y in enumerate(b):
            r[i + j2] += x * y
    return r


ok = True
for q in range(1, 18):
    Pq = [1]
    for i in range(q):
        Pq = polymul(Pq, [1, -1, 0, -i])
    Fq = [N[k][q] for k in range(K + 1)]
    Num = polymul(Pq, Fq)[:K + 1]
    for j in range(0, 6):
        if q + j > K - 3 * q:
            continue
        lhs = Num[q + j]
        rhs = sum((Pq[i] if i < len(Pq) else 0) * D(q + j - i, j - i) for i in range(j + 1))
        ok &= (lhs == rhs)
        if q >= j + 2:
            ok &= (lhs == sum((Pq[i] if i < len(Pq) else 0) * peval(P[j - i], q + j - i) for i in range(j + 1)))
report('nu_j', ok, '[x^{q+j}]Num_q = sum_{i<=j} pi_i(q) D(q+j-i,j-i), = polynomial form for q>=j+2 (q<=17, j<=5)')

# ---------- (7) 06_C5 ----------
UT2 = core.U_fast_table(14, 40)


def Upoly(k):
    xs = list(range(0, k + 1))
    return interp(xs, [UT2[k][m] for m in xs])


ok_mu = True
ok_mu3 = None
for k in range(3, 15):
    up = Upoly(k)
    mu = F(k * k - 2 * k - 1, 2)
    good_mu = (up[k - 1] == F(2, factorial(k)) * k * mu) and up[k] == F(2, factorial(k))
    if k == 3:
        ok_mu3 = good_mu
    else:
        ok_mu &= good_mu
report('mu_k', ok_mu and ok_mu3 is False, 'first two m-coefficients of (2/k!)(m+mu_k)^k match U_k for 4<=k<=14, not for k=3')
ok = (all(N[k][k] == 2 for k in range(2, 30)) and all(N[k][k - 1] == k * k - k - 4 for k in range(4, 30))
      and all(N[k][k - 2] == peval(P[2], k) for k in range(6, 30)) and N[5][3] == 25 and peval(P[2], 5) == 31
      and N[4][2] == 7 and peval(P[2], 4) == 19 and N[3][2] == 4)
report('C-basis', ok, 'N(k,k)=2, N(k,k-1)=k^2-k-4 (k>=4), N(k,k-2)=p_2(k) (k>=6); N(5,3)=25 vs p_2(5)=31; N(4,2)=7 vs 19')


def esym(j, vals):
    dp = [1] + [0] * j
    for v in vals:
        for t in range(j, 0, -1):
            dp[t] += v * dp[t - 1]
    return dp[j]


def fall(n, j):
    r = 1
    for i in range(j):
        r *= (n - i)
    return r


ok = True
for k in range(1, 15):
    up = Upoly(k)
    for d in range(0, k + 1):
        Bd = factorial(k - d) * up[k - d]
        rhs = sum((-1) ** (d - e) * N[k][k - e] * F(esym(d - e, list(range(-1, k - e - 1))), fall(k - e, d - e))
                  for e in range(0, d + 1))
        ok &= (Bd == rhs)
report('e_j-formula', ok, 'B_d(k) = sum_e (-1)^{d-e} N(k,k-e) e_{d-e}(-1,0,..,k-e-2)/(k-e)^{fall d-e} (e_j elementary symmetric), 0<=d<=k<=14')
ok = True
for k in range(0, 15):
    up = [UT2[k][m] for m in range(41)]
    h = [sum((-1) ** r * comb(k + 1, r) * up[i - r] for r in range(i + 1)) for i in range(0, 30)]
    ok &= (sum(h) == N[k][k])
    ok &= all(x2 == 0 for x2 in h[k + 1:])
report('h_k(1)=N(k,k)', ok, 'h_k(1)=N(k,k) for 0<=k<=14 (h_0(1)=h_1(1)=1); h_{k,i}=sum_r (-1)^r C(k+1,r)U_k(i-r) vanishes for i>k')

print('SUMMARY fixcheck-math pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
