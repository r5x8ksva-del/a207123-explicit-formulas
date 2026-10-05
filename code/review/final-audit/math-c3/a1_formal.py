# -*- coding: utf-8 -*-
"""final-audit / math-c3 / a1: exact checks of the formal identities in report section C-3
(04_C3.md: T3.1, T3.2, T3.3(1)(2), T3.5, T3.6) against the original definition (core.U_list / DP / DFS).

Independent implementation: Laurent series in x (lser.py), plain truncated series in (x,t[,s]).
"""
import sys, os, time, random
from fractions import Fraction
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, CODE)
sys.path.insert(0, HERE)
import core
from lser import L, rf, gbinom_neg

T0 = time.time()
RES = []


def report(name, ok, msg):
    RES.append(bool(ok))
    print('%s %s :: %s' % ('PASS' if ok else 'FAIL', name, msg))
    sys.stdout.flush()


# ----------------------------------------------------------------------------------------------
# truth tables
# ----------------------------------------------------------------------------------------------
KT, MT = 40, 20
T = core.U_fast_table(KT, MT)
ok = all(core.U_list(m, KT) == [T[k][m] for k in range(KT + 1)] for m in range(0, 9))
ok &= all(core.PROMPT_TABLE[k][m] == T[k][m] for k in range(1, 11) for m in range(7))
report('anchor', ok, 'U_fast_table(40,20) == reference U_list (m<=8, k<=40) == prompt table (k<=10,m<=6)')


def legal(h):
    return all(core.good(h[i], h[i + 1], h[i + 2]) for i in range(len(h) - 2))


def enum_legal(k, m):
    out = []
    seq = []

    def dfs():
        if len(seq) == k:
            out.append(tuple(seq))
            return
        for v in range(m + 1):
            if len(seq) >= 2 and not core.good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            dfs()
            seq.pop()
    dfs()
    return out


# brute refined counts: not ending in ascent (k<=1 counts as not), ending with ascent to value j
KB, MB = 9, 3
A_br = {}
B_br = {}
for k in range(KB + 1):
    for m in range(MB + 1):
        seqs = enum_legal(k, m)
        assert len(seqs) == T[k][m]
        A_br[(k, m)] = sum(1 for h in seqs if k <= 1 or h[-2] >= h[-1])
        for j in range(1, m + 1):
            B_br[(k, m, j)] = sum(1 for h in seqs if k >= 2 and h[-2] < h[-1] == j)


def ser_inv(p, K):
    """power-series inverse of polynomial/series p (p[0] != 0) up to x^K."""
    p = [Fraction(a) for a in p] + [Fraction(0)] * (K + 1)
    r = [Fraction(0)] * (K + 1)
    r[0] = 1 / p[0]
    for k in range(1, K + 1):
        acc = Fraction(0)
        for j in range(1, k + 1):
            if p[j]:
                acc += p[j] * r[k - j]
        r[k] = -acc / p[0]
    return r


def smul(p, q, K):
    r = [Fraction(0)] * (K + 1)
    for i, a in enumerate(p[:K + 1]):
        if a:
            for j in range(min(len(q), K + 1 - i)):
                if q[j]:
                    r[i + j] += a * q[j]
    return r


def b_poly(i):
    return [1, -1, 0, -i]


def P_poly(m):
    p = [Fraction(1)]
    for i in range(m + 1):
        q = b_poly(i)
        r = [Fraction(0)] * (len(p) + 3)
        for a, x in enumerate(p):
            for b, y in enumerate(q):
                r[a + b] += x * y
        p = r
    return p


S2 = core.stirling2_table(80)

# ----------------------------------------------------------------------------------------------
# T3.1  sum_m t^m/P_m = 1F1(1;1-lam;-t/x^3)/(1-x); Stirling count; Kummer; lower-gamma form
# ----------------------------------------------------------------------------------------------
K1, M1 = 24, 8
REL = K1 + 3 * M1 + 6
LAM = L(-3, [1, -1] + [0] * (REL - 2))          # lambda = x^-3 - x^-2  (exact)


def c_minus_lam(c):
    """(c - lambda) as Laurent series."""
    cc = [Fraction(0)] * REL
    cc[0] = Fraction(-1); cc[1] = Fraction(1); cc[3] = Fraction(c)
    return L(-3, cc)


INV_CML = {}


def inv_cml(c):
    if c not in INV_CML:
        INV_CML[c] = c_minus_lam(c).inv()
    return INV_CML[c]


one_minus_x_inv = L.poly([1, -1], REL).inv()
ok_1f1, ok_neg, ok_stir, ok_brute = True, True, True, True
for m in range(M1 + 1):
    invP = ser_inv(P_poly(m), K1)
    # 1F1 coefficient: (1)_m a^m/((1-lam)_m m!) = (-1)^m x^{-3m} / prod_{i=1}^m (i - lam)
    term = L.mono(-3 * m, (-1) ** m, REL)
    for i in range(1, m + 1):
        term = term * inv_cml(i)
    term = term * one_minus_x_inv
    ok_neg &= term.check_no_negative(0)
    ok_1f1 &= all(term.coeff(k) == invP[k] for k in range(K1 + 1))
    # Stirling count
    for k in range(K1 + 1):
        st = sum(S2[m + s][m] * core.binom(k + m - 2 * s, k - 3 * s) for s in range(0, k // 3 + 1))
        ok_stir &= (st == invP[k])
        if k <= KB and m <= MB:
            ok_brute &= (A_br[(k, m)] == invP[k])
report('T3.1-1f1', ok_1f1 and ok_neg, 'Pochhammer/Laurent expansion of 1F1(1;1-lam;-t/x^3)/(1-x): no negative x-powers and == 1/P_m, k<=%d, m<=%d' % (K1, M1))
report('T3.1-count', ok_stir and ok_brute, '[x^k]1/P_m == sum_s S(m+s,m)C(k+m-2s,k-3s) (k<=%d,m<=%d) == DFS count of legal sequences not ending in an ascent (k<=%d,m<=%d)' % (K1, M1, KB, MB))

# Kummer: 1F1(1;1-lam;a) = e^a 1F1(-lam;1-lam;-a); gamma: sum t^m/P_m = x^{-3} e^a sum_n (-a)^n/(n!(lam-n))
ok_k, ok_g = True, True
for M in range(M1 + 1):
    invP = ser_inv(P_poly(M), K1)
    target = smul(invP, [1, -1], K1)                  # (1-x)/P_M = [t^M] 1F1(1;1-lam;a)
    acc_k = None
    acc_g = None
    for p in range(M + 1):
        n = M - p
        ea = L.mono(-3 * p, Fraction((-1) ** p, factorial(p)), REL)     # [t^p] e^a
        # (-lam)_n/(1-lam)_n = (-lam)/(n-lam)
        ratio = L(0, [1] + [0] * (REL - 1))
        for i in range(n):
            ratio = ratio * c_minus_lam(i) * inv_cml(i + 1)
        tk = ea * ratio * L.mono(-3 * n, Fraction(1, factorial(n)), REL)  # (-a)^n = x^{-3n} t^n
        acc_k = tk if acc_k is None else acc_k + tk
        tg = ea * L.mono(-3 * n, Fraction(1, factorial(n)), REL) * (LAM - L.mono(0, n, REL)).inv()
        acc_g = tg if acc_g is None else acc_g + tg
    acc_g = acc_g.shift(-3)
    ok_k &= acc_k.check_no_negative(0) and all(acc_k.coeff(k) == target[k] for k in range(K1 + 1))
    ok_g &= acc_g.check_no_negative(0) and all(acc_g.coeff(k) == invP[k] for k in range(K1 + 1))
report('T3.1-kummer-gamma', ok_k and ok_g, 'e^a 1F1(-lam;1-lam;-a) == (1-x) sum t^m/P_m and x^{-3} e^a sum_n (-a)^n/(n!(lam-n)) == sum t^m/P_m (Laurent, k<=%d, m<=%d)' % (K1, M1))

# ----------------------------------------------------------------------------------------------
# T3.2  Psi = Phi_A * gamma(x, t e^{vs}),  x^3 t d_t Psi = A d_s Psi - t Psi;  Y = A^{-1} L_s[Psi] solves L_A[Y]=gamma
# ----------------------------------------------------------------------------------------------


def zeros3(K, M, NS):
    return [[[Fraction(0)] * (K + 1) for _ in range(M + 1)] for _ in range(NS + 1)]


def mul3(P, Q, K, M, NS):
    R = zeros3(K, M, NS)
    for N1 in range(NS + 1):
        for m1 in range(M + 1):
            nz = [(k1, a) for k1, a in enumerate(P[N1][m1]) if a]
            if not nz:
                continue
            for N2 in range(NS + 1 - N1):
                for m2 in range(M + 1 - m1):
                    q = Q[N2][m2]
                    nzq = [(k2, b) for k2, b in enumerate(q) if b]
                    if not nzq:
                        continue
                    r = R[N1 + N2][m1 + m2]
                    for k1, a in nz:
                        for k2, b in nzq:
                            if k1 + k2 <= K:
                                r[k1 + k2] += a * b
    return R


def laplace_case(Apoly, gamma, K, M, NS, label):
    """gamma: dict (k,m)->coef (truncated to k<=K, m<=M). Returns Y (list Y[m][k]) and check results."""
    Ainv = ser_inv(Apoly, K)
    # powers Ainv^N
    AinvP = [[Fraction(1)] + [Fraction(0)] * K]
    for N in range(1, NS + 1):
        AinvP.append(smul(AinvP[-1], Ainv, K))
    # Z = (t/x^3)(e^{vs}-1) = t sum_{N>=1} x^{3N-3} A^{-N} s^N/N!
    Z = zeros3(K, M, NS)
    if M >= 1:
        for N in range(1, NS + 1):
            for k in range(K + 1):
                kk = k - (3 * N - 3)
                if kk >= 0:
                    Z[N][1][k] = AinvP[N][kk] / factorial(N)
    # Phi = exp(Z)
    Phi = zeros3(K, M, NS)
    Phi[0][0][0] = Fraction(1)
    term = [[[c for c in row] for row in lay] for lay in Phi]
    for j in range(1, M + 1):
        term = mul3(term, Z, K, M, NS)
        term = [[[c / j for c in row] for row in lay] for lay in term]
        for N in range(NS + 1):
            for m in range(M + 1):
                for k in range(K + 1):
                    Phi[N][m][k] += term[N][m][k]
    # Gamma = sum gamma_{k,m} x^k t^m e^{m v s},  e^{mvs} = sum_N m^N x^{3N} A^{-N} s^N/N!
    Gam = zeros3(K, M, NS)
    for (k0, m0), g in gamma.items():
        if k0 > K or m0 > M or g == 0:
            continue
        for N in range(NS + 1):
            c = Fraction(m0 ** N, factorial(N)) * g
            if c == 0:
                continue
            for k in range(K + 1):
                kk = k - k0 - 3 * N
                if kk >= 0:
                    Gam[N][m0][k] += c * AinvP[N][kk]
    Psi = mul3(Phi, Gam, K, M, NS)
    # (a) identity x^3 t d_t Psi = A d_s Psi - t Psi   (all N <= NS-1)
    ok_id = True
    for N in range(NS):
        for m in range(M + 1):
            dsA = smul(Apoly, [(N + 1) * c for c in Psi[N + 1][m]], K)
            for k in range(K + 1):
                lhs = m * Psi[N][m][k - 3] if k >= 3 else 0
                rhs = dsA[k] - (Psi[N][m - 1][k] if m >= 1 else 0)
                if lhs != rhs:
                    ok_id = False
    # (b) valuation bounds: ord_x [s^N t^m] >= 3N-3m ; ord_(x,t) [s^N] >= N
    ok_val = True
    for N in range(NS + 1):
        for m in range(M + 1):
            for k in range(K + 1):
                if Psi[N][m][k] != 0:
                    if k < 3 * N - 3 * m or k + m < N:
                        ok_val = False
    # (c) Y = A^{-1} L_s[Psi] (needs N <= k/3+m: NS >= K/3+M)
    assert NS >= K // 3 + M
    Y = []
    for m in range(M + 1):
        acc = [Fraction(0)] * (K + 1)
        for N in range(NS + 1):
            f = factorial(N)
            for k in range(K + 1):
                acc[k] += f * Psi[N][m][k]
        Y.append(smul(Ainv, acc, K))
    # L_A[Y] == gamma
    ok_sol = True
    for m in range(M + 1):
        AY = smul(Apoly, Y[m], K)
        for k in range(K + 1):
            val = AY[k] - (Y[m - 1][k] if m >= 1 else 0) - (m * Y[m][k - 3] if k >= 3 else 0)
            if val != gamma.get((k, m), 0):
                ok_sol = False
    # unique solution via the report's coefficient recursion  y_{k,m} = g_{k,m} - sum_{i>=1} A_i y_{k-i,m} + y_{k,m-1} + m y_{k-3,m}
    y = {}
    for s_ in range(K + M + 1):
        for m in range(M + 1):
            k = s_ - m
            if k < 0 or k > K:
                continue
            v = Fraction(gamma.get((k, m), 0))
            for i in range(1, min(k, len(Apoly) - 1) + 1):
                v -= Apoly[i] * y[(k - i, m)]
            if m >= 1:
                v += y[(k, m - 1)]
            if k >= 3:
                v += m * y[(k - 3, m)]
            y[(k, m)] = v
    ok_rec = all(y[(k, m)] == Y[m][k] for k in range(K + 1) for m in range(M + 1))
    return Y, ok_id, ok_val, ok_sol, ok_rec


random.seed(20261004)
cases = []
for Apoly in ([1, -1], [1, -1, 0, 1], [1, 2, -1, 3]):
    gam = {(k, m): random.randint(-4, 4) for k in range(10) for m in range(4)}
    cases.append((Apoly, gam))
allok = True
for Apoly, gam in cases:
    Y, a, b, c, d = laplace_case(Apoly, gam, 9, 3, 6, 'rand')
    allok &= a and b and c and d
    print('#   A=%s random gamma: identity=%s valuation=%s L_A[Y]=gamma %s recursion==Y %s' % (Apoly, a, b, c, d))
report('T3.2-general', allok, 'Phi_A=exp((t/x^3)(e^{vs}-1)), v=x^3/A, Psi=Phi_A gamma(x,t e^{vs}): x^3 t d_tPsi = A d_sPsi - tPsi exactly; ord_x[s^N t^m]>=3N-3m, ord[s^N]>=N; '
       'Y=A^{-1}L_s[Psi] satisfies L_A[Y]=gamma and equals the coefficient recursion of T3.2(i); 3 A x random integer gamma, k<=9, m<=3, s^N N<=6')

# F case: A = 1-x, gamma = 1 + x^2 t/(1-t)^2
KF, MF = 12, 4
gamF = {(0, 0): 1}
for j in range(1, MF + 1):
    gamF[(2, j)] = j
Y, a, b, c, d = laplace_case([1, -1], gamF, KF, MF, KF // 3 + MF, 'F')
okF = a and b and c and d and all(Y[m][k] == T[k][m] for k in range(KF + 1) for m in range(MF + 1))
report('T3.2-F', okF, 'F = (1/(1-x)) L_s[exp((t/x^3)(e^{us}-1))(1 + x^2 t e^{us}/(1-t e^{us})^2)] == DP U_k(m), k<=%d, m<=%d (exact); identity/valuation also hold' % (KF, MF))

# 1 + tF native Laplace: A = 1-x+x^3, gamma = A + x^2 t^2/(1-t)^2
gamN = {(0, 0): 1, (1, 0): -1, (3, 0): 1}
for j in range(2, MF + 1):
    gamN[(2, j)] = j - 1
Y, a, b, c, d = laplace_case([1, -1, 0, 1], gamN, KF, MF, KF // 3 + MF, 'N')
okN = a and b and c and d
for m in range(MF + 1):
    for k in range(KF + 1):
        target = (1 if (k == 0 and m == 0) else 0) + (T[k][m - 1] if m >= 1 else 0)
        okN &= (Y[m][k] == target)
report('T3.5-native-laplace', okN, '1+tF = A^{-1} L_s[exp((t/x^3)(e^{vs}-1))(A + x^2 t^2 e^{2vs}/(1-t e^{vs})^2)], A=1-x+x^3, v=x^3/A == 1+tF from DP, k<=%d, m<=%d' % (KF, MF))

# second independent proof claim: L_s[e^{jus}(e^{us}-1)^n/n!] = u^n/prod_{i=j}^{j+n}(1-iu)
# check as power series in u (u formal): L_s[e^{cs}] = 1/(1-c)
KU = 14
ok_lc = True
for j in range(0, 5):
    for n in range(0, 5):
        # e^{jus}(e^{us}-1)^n/n! = (1/n!) sum_r C(n,r)(-1)^{n-r} e^{(j+r)us}; L_s[e^{cus}] = 1/(1-cu) = sum (cu)^N
        lhs = [Fraction(0)] * (KU + 1)
        for r in range(n + 1):
            c = comb(n, r) * (-1) ** (n - r)
            for N in range(KU + 1):
                lhs[N] += Fraction(c * (j + r) ** N, factorial(n))
        den = [Fraction(1)]
        for i in range(j, j + n + 1):
            den = smul(den + [0], [1, -i], KU)
        rhs = [Fraction(0)] * n + ser_inv(den, KU)[:KU + 1 - n]
        ok_lc &= (lhs == rhs)
report('T3.2-Lcoef', ok_lc, 'L_s[e^{jus}(e^{us}-1)^n/n!] = u^n/prod_{i=j}^{j+n}(1-iu) as series in u (j,n<=4, u^N N<=%d)' % KU)

# ----------------------------------------------------------------------------------------------
# T3.3(1)  F = sum_j kappa_j (t^j/b_j) 1F1(1;j+1-lam;-t/x^3); term j = sequences ending with ascent to j; Kummer form of F
# ----------------------------------------------------------------------------------------------
K3, M3 = 24, 8
ok_sum, ok_terms, ok_negs = True, True, True
for m in range(M3 + 1):
    tot = L(0, [0] * REL)
    for j in range(0, m + 1):
        n = m - j
        kap = 1 if j == 0 else None
        term = L.mono(-3 * n, (-1) ** n, REL)
        for i in range(n):
            term = term * inv_cml(j + 1 + i)
        term = term * L.poly(b_poly(j), REL).inv()
        if j >= 1:
            term = term * L.poly([0, 0, j], REL)          # kappa_j = j x^2
        ok_negs &= term.check_no_negative(0)
        # compare individual terms with refined brute counts
        if m <= MB:
            for k in range(KB + 1):
                want = A_br[(k, m)] if j == 0 else B_br[(k, m, j)]
                ok_terms &= (term.coeff(k) == want)
        tot = tot + term
    ok_sum &= all(tot.coeff(k) == T[k][m] for k in range(K3 + 1))
report('T3.3(1)-1f1sum', ok_sum and ok_negs and ok_terms,
       'sum_j kappa_j (t^j/b_j) 1F1(1;j+1-lam;a), kappa_0=1, kappa_j=j x^2 (Pochhammer from lambda=x^-3-x^-2 as Laurent): no negative powers, '
       'sum == U_k(m) (k<=%d, m<=%d); term j>=1 == #legal seq ending with ascent to j, term 0 == #not ending in ascent (DFS, k<=%d, m<=%d)' % (K3, M3, KB, MB))

# Kummer form of F: F = x^{-3} e^a sum_n phi_n a^n/(lam-n), phi(tau) = e^{-tau}(1 - x^5 tau/(1+x^3 tau)^2)
K4, M4 = 20, 7
REL4 = K4 + 3 * M4 + 8
LAM4 = L(-3, [1, -1] + [0] * (REL4 - 2))
# phi_n as polynomials in x: series in tau
NT = M4 + 1
inner = [[Fraction(0)] * (3 * NT + 6) for _ in range(NT)]     # 1 - x^5 tau (1+x^3 tau)^{-2}
inner[0][0] = Fraction(1)
for j in range(NT - 1):
    # x^5 tau * (-1)^j (j+1) x^{3j} tau^j  -> tau^{j+1}
    inner[j + 1][5 + 3 * j] -= (-1) ** j * (j + 1)
phi = []
for n in range(NT):
    p = [Fraction(0)] * (3 * NT + 6)
    for i in range(n + 1):
        c = Fraction((-1) ** i, factorial(i))
        for e, a in enumerate(inner[n - i]):
            p[e] += c * a
    phi.append(p)
ok_kF = True
for M in range(M4 + 1):
    acc = None
    for p_ in range(M + 1):
        n = M - p_
        ea = L.mono(-3 * p_, Fraction((-1) ** p_, factorial(p_)), REL4)
        an = L.mono(-3 * n, (-1) ** n, REL4)
        tk = ea * L.poly(phi[n], REL4) * an * (LAM4 - L.mono(0, n, REL4)).inv()
        acc = tk if acc is None else acc + tk
    acc = acc.shift(-3)
    ok_kF &= acc.check_no_negative(0) and all(acc.coeff(k) == T[k][M] for k in range(K4 + 1))
report('T3.3(1)-kummerF', ok_kF, 'F = x^{-3} e^a sum_n phi_n a^n/(lam-n), phi = e^{-tau}(1 - x^5 tau/(1+x^3 tau)^2): Laurent expansion == U_k(m), k<=%d, m<=%d' % (K4, M4))

# ----------------------------------------------------------------------------------------------
# T3.3(2)  Humbert closed form of F; coefficient form Y_beta solves L_A[Y] = (1-t)^{-beta}
# ----------------------------------------------------------------------------------------------
K5, M5 = 20, 8
REL5 = K5 + 4


def cml5(c):
    cc = [Fraction(0)] * REL5
    cc[0] = Fraction(-1); cc[1] = Fraction(1); cc[3] = Fraction(c)
    return L(-3, cc)


INV5 = {}


def inv_poch(gamma_shift, N):
    """1/(gamma_shift - lam)_N  as Laurent (gamma = gamma_shift - lambda)."""
    key = (gamma_shift, N)
    if key not in INV5:
        r = L(0, [1] + [0] * (REL5 - 1))
        for i in range(N):
            r = r * cml5(gamma_shift + i).inv()
        INV5[key] = r
    return INV5[key]


def phi1_tcoef(beta, gamma_shift, M):
    """[t^M] (1-t)^{-beta} Phi_1(1,beta;gamma_shift-lam; -t/(1-t), -t/x^3) as Laurent in x."""
    acc = L(0, [0] * REL5)
    for mm in range(M + 1):
        for n in range(M + 1 - mm):
            Nn = mm + n
            coef = Fraction(factorial(Nn)) * rf(Fraction(beta), mm) / (factorial(mm) * factorial(n))
            coef *= (-1) ** (mm + n)                                # X^m Y^n signs
            coef *= gbinom_neg(Fraction(beta) + mm, M - Nn)          # [t^{M-N}](1-t)^{-beta-m}
            if coef == 0:
                continue
            acc = acc + inv_poch(gamma_shift, Nn).shift(-3 * n).scale(coef)
    return acc


ok_h = True
inv1mx5 = L.poly([1, -1], REL5).inv()
for M in range(M5 + 1):
    f11 = inv_poch(1, M).shift(-3 * M).scale((-1) ** M)          # [t^M] 1F1(1;1-lam;a)
    bracket = f11 + (phi1_tcoef(2, 1, M) - phi1_tcoef(1, 1, M)) * L.poly([0, 0, 1], REL5)
    val = bracket * inv1mx5
    ok_h &= val.check_no_negative(0) and all(val.coeff(k) == T[k][M] for k in range(K5 + 1))
report('T3.3(2)-humbertF', ok_h, 'F = (1/(1-x))[1F1(1;1-lam;a) + x^2((1-t)^{-2}Phi_1(1,2;1-lam;-t/(1-t),a) - (1-t)^{-1}Phi_1(1,1;1-lam;-t/(1-t),a))] from the series definitions == U_k(m), k<=%d, m<=%d' % (K5, M5))

# coefficient form: Y_beta = (1-t)^{-beta} sum_N [t^N/(A prod_{i=1}^N (A - i x^3))] sum_{m<=N} C(N,m)(beta)_m (x^3/(1-t))^m
K6, M6 = 18, 8
ok_yb = True
details = []
for Apoly in ([1, -1], [1, -1, 0, 1], [1, 2, -1, 3], [1, 0, 5, -2]):
    for beta in (Fraction(1), Fraction(2), Fraction(1, 2), Fraction(-3), Fraction(0)):
        Y = [[Fraction(0)] * (K6 + 1) for _ in range(M6 + 1)]
        for N in range(M6 + 1):
            den = list(Apoly)
            for i in range(1, N + 1):
                bi = list(Apoly) + [0] * 4
                bi[3] -= i
                den = smul(den + [0] * 4, bi, K6)
            dinv = ser_inv(den, K6)
            for mm in range(N + 1):
                c = comb(N, mm) * rf(beta, mm)
                if c == 0 or 3 * mm > K6:
                    continue
                for r in range(M6 + 1 - N):
                    cr = c * gbinom_neg(beta + mm, r)
                    if cr == 0:
                        continue
                    row = Y[N + r]
                    for k in range(K6 + 1 - 3 * mm):
                        row[k + 3 * mm] += cr * dinv[k]
        ok1 = True
        for m in range(M6 + 1):
            AY = smul(Apoly, Y[m], K6)
            want = gbinom_neg(beta, m)
            for k in range(K6 + 1):
                val = AY[k] - (Y[m - 1][k] if m >= 1 else 0) - (m * Y[m][k - 3] if k >= 3 else 0)
                if val != (want if k == 0 else 0):
                    ok1 = False
        ok_yb &= ok1
        details.append('A=%s beta=%s:%s' % (Apoly, beta, 'ok' if ok1 else 'BAD'))
print('#   ' + '; '.join(details))
report('T3.3(2)-Ybeta', ok_yb, 'coefficient form Y_beta (b_i^{(A)} = A - i x^3) satisfies (A-t)Y - x^3 t Y_t = (1-t)^{-beta} exactly, '
       '4 A (incl. 1-x, 1-x+x^3) x beta in {1,2,1/2,-3,0}, k<=%d, m<=%d' % (K6, M6))

# F = Y_0 + x^2 (Y_2 - Y_1) for A = 1-x via the coefficient form, compared with DP
# (also confirms the closed form's coefficient version is free of negative powers)

# ----------------------------------------------------------------------------------------------
# T3.5  Ncal: substitution, PDE, [y^q] formula (vs DFS), Humbert closed form, 1F1 sum form
# ----------------------------------------------------------------------------------------------
KN, QN = 20, 14
NTb = [[core.N_from_U(T, k, q) if q <= MT + 1 else None for q in range(QN + 3)] for k in range(KN + 1)]
ok_dfs = True
for k in range(0, 9):
    d = core.N_brute(k)
    for q in range(QN + 1):
        ok_dfs &= (NTb[k][q] == d.get(q, 0))
report('T3.5-N-anchor', ok_dfs, 'N(k,q) by DFS over surjective legal words (k<=8) == binomial inversion sum_i (-1)^{q-i}C(q,i)U_k(i-1) (i.e. [y^q]Ncal = sum_i(-1)^{q-i}C(q,i)G_{i-1})')

# substitution 1 + tF = Ncal(x, t/(1-t))/(1-t): [x^k t^n]
ok_sub = True
for k in range(KN + 1):
    for n in range(QN + 1):
        rhs = sum(NTb[k][q] * comb(n, q) for q in range(0, n + 1))     # [t^n] t^q (1-t)^{-q-1} = C(n,q)
        lhs = (1 if (k == 0 and n == 0) else 0) + (T[k][n - 1] if n >= 1 else 0)
        ok_sub &= (lhs == rhs)
# equivalent form Ncal = 1/(1+y) + y F(x, y/(1+y))/(1+y)^2
for k in range(KN + 1):
    for q in range(QN + 1):
        rhs = Fraction((-1) ** q if k == 0 else 0)
        # y F(x,y/(1+y))/(1+y)^2 = sum_m U_k(m) y^{m+1} (1+y)^{-m-2}
        for m in range(0, q):
            r = q - m - 1
            rhs += T[k][m] * (-1) ** r * comb(m + 1 + r, r)
        ok_sub &= (rhs == NTb[k][q])
report('T3.5-subst', ok_sub, '1+tF(x,t) = Ncal(x,t/(1-t))/(1-t) and Ncal = 1/(1+y) + y F(x,y/(1+y))/(1+y)^2, coefficientwise k<=%d, n,q<=%d' % (KN, QN))

# PDE (1 - x(1+y) + x^3(1-y^2)) N - x^3 y (1+y)^2 N_y = 1 - x + x^3 + x^2 y^2
def Nv(k, q):
    if k < 0 or q < 0:
        return 0
    return NTb[k][q]


ok_pde = True
for k in range(KN + 1):
    for q in range(QN + 1):
        v = Nv(k, q) - Nv(k - 1, q) - Nv(k - 1, q - 1) + Nv(k - 3, q) - Nv(k - 3, q - 2)
        # y(1+y)^2 d_y = (y + 2y^2 + y^3) d_y
        v -= q * Nv(k - 3, q) + 2 * (q - 1) * Nv(k - 3, q - 1) + (q - 2) * Nv(k - 3, q - 2)
        rhs = {(0, 0): 1, (1, 0): -1, (3, 0): 1, (2, 2): 1}.get((k, q), 0)
        ok_pde &= (v == rhs)
# triangle recurrence (C3) for k>=3, q>=1
ok_tri = True
for k in range(3, KN + 1):
    for q in range(1, QN + 1):
        r = q - 1
        v = Nv(k - 1, q - 1) + Nv(k - 1, q) + r * (Nv(k - 3, q - 2) + 2 * Nv(k - 3, q - 1) + Nv(k - 3, q))
        ok_tri &= (v == Nv(k, q))
report('T3.5-pde', ok_pde and ok_tri, 'Ncal PDE coefficientwise (k<=%d, q<=%d; boundary terms exactly at (0,0),(1,0),(3,0),(2,2)); (C3) triangle recurrence for k>=3,q>=1' % (KN, QN))

# Humbert closed form for Ncal (Laurent in x, series in y)
K7, Q7 = 18, 9
REL7 = K7 + 4


def cml7(c):
    cc = [Fraction(0)] * REL7
    cc[0] = Fraction(-1); cc[1] = Fraction(1); cc[3] = Fraction(c)
    return L(-3, cc)


INV7 = {}


def inv_poch7(N):
    """1/(-lam)_N."""
    if N not in INV7:
        r = L(0, [1] + [0] * (REL7 - 1))
        for i in range(N):
            r = r * cml7(i).inv()
        INV7[N] = r
    return INV7[N]


def coef_y(n, r):
    """[y^r] y^n (1+y)^{-n}."""
    if r < n:
        return 0
    if n == 0:
        return 1 if r == 0 else 0
    return (-1) ** (r - n) * comb(r - 1, r - n)


zero7 = lambda: L(0, [0] * REL7)
# series in y (list of Laurent) up to y^Q7
F11 = [zero7() for _ in range(Q7 + 1)]
for n in range(Q7 + 1):
    base = inv_poch7(n).shift(-3 * n).scale((-1) ** n)
    for r in range(n, Q7 + 1):
        c = coef_y(n, r)
        if c:
            F11[r] = F11[r] + base.scale(c)
PH = {}
for beta in (1, 2):
    s = [zero7() for _ in range(Q7 + 1)]
    for mm in range(Q7 + 1):
        for n in range(Q7 + 1 - mm):
            Nn = mm + n
            coef = Fraction(factorial(Nn)) * rf(Fraction(beta), mm) / (factorial(mm) * factorial(n)) * (-1) ** mm * (-1) ** n
            base = inv_poch7(Nn).shift(-3 * n).scale(coef)
            for r in range(Nn, Q7 + 1):
                c = coef_y(n, r - mm)
                if c:
                    s[r] = s[r] + base.scale(c)
    PH[beta] = s


def ymul_poly(ser, poly):          # multiply series in y by polynomial in y (int coeffs)
    out = [zero7() for _ in range(Q7 + 1)]
    for i, a in enumerate(poly):
        for r in range(Q7 + 1 - i):
            out[r + i] = out[r + i] + ser[r].scale(a)
    return out


Apol = L.poly([1, -1, 0, 1], REL7)
x2 = L.poly([0, 0, 1], REL7)
t1 = [s * (Apol + x2) for s in F11]
t2 = [s * x2.scale(-2) for s in ymul_poly(PH[1], [1, 1])]
t3 = [s * x2 for s in ymul_poly(PH[2], [1, 2, 1])]
num = [t1[r] + t2[r] + t3[r] for r in range(Q7 + 1)]
# divide by A(1+y)
invA = Apol.inv()
geo = [(-1) ** j for j in range(Q7 + 1)]
res = ymul_poly([s * invA for s in num], geo)
ok_nh = True
for q in range(Q7 + 1):
    ok_nh &= res[q].check_no_negative(0)
    ok_nh &= all(res[q].coeff(k) == NTb[k][q] for k in range(K7 + 1))
report('T3.5-humbertN', ok_nh, 'Ncal = [(A+x^2)1F1(1;-lam;yh) - 2x^2(1+y)Phi_1(1,1;-lam;-y,yh) + x^2(1+y)^2 Phi_1(1,2;-lam;-y,yh)]/(A(1+y)), yh=-y/((1+y)x^3), A=1-x+x^3: == N(k,q), k<=%d, q<=%d' % (K7, Q7))

# ----------------------------------------------------------------------------------------------
# T3.6  H(z,t) = sum_k h_k(t) z^k: definitions and PDE (k<=12, exact polynomials in t)
# ----------------------------------------------------------------------------------------------
KH = 12


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def ptrim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


hs = []
ok_deg = True
for k in range(KH + 1):
    f = [T[k][m] for m in range(MT + 1)]
    pw = [1]
    for _ in range(k + 1):
        pw = pmul(pw, [1, -1])
    h = pmul(f, pw)[:MT + 1]
    hp = ptrim(h)
    ok_deg &= (len(hp) <= max(k, 1))
    hs.append(hp)
# h_k = sum_q N(k,q) t^{q-1}(1-t)^{k-q}  (k>=1)
ok_hN = True
for k in range(1, KH + 1):
    acc = [0]
    for q in range(1, k + 1):
        term = [0] * (q - 1) + [1]
        for _ in range(k - q):
            term = pmul(term, [1, -1])
        acc = padd(acc, [NTb[k][q] * c for c in term])
    ok_hN &= (ptrim(acc) == hs[k])
# H = 1 + (Ncal(z(1-t), t/(1-t)) - 1)/t : [z^k] = sum_q N(k,q)(1-t)^{k-q} t^{q-1} for k>=1 -- identical to the above; k=0 gives 1
ok_hN &= (hs[0] == [1])


def hget(k):
    return hs[k] if k >= 0 else [0]


def pder(p):
    return [i * p[i] for i in range(1, len(p))] or [0]


ok_hpde = True
for k in range(KH + 1):
    # (1 - z - z^3 t(1-t))H - z^4 t(1-t) H_z - z^3 t(1-t)^2 H_t = 1 + z^2 t ; z^k coefficient
    v = padd(hget(k), [-c for c in hget(k - 1)])
    t1t = [0, 1, -1]
    v = padd(v, [-c for c in pmul(t1t, hget(k - 3))])
    v = padd(v, [-(k - 3) * c for c in pmul(t1t, hget(k - 3))]) if k >= 3 else v
    v = padd(v, [-c for c in pmul([0, 1, -2, 1], pder(hget(k - 3)))]) if k >= 3 else v
    rhs = {0: [1], 2: [0, 1]}.get(k, [0])
    ok_hpde &= (ptrim(v) == ptrim(rhs))
# (C6) recurrence and the c5a form (1-z)H - t(1-t)z^3[(1-t)H_t + H + zH_z] = 1 + tz^2 (algebraically identical; checked on the same data)
ok_c5a = True
for k in range(KH + 1):
    v = padd(hget(k), [-c for c in hget(k - 1)])
    if k >= 3:
        inner = padd(padd(pmul([1, -1], pder(hget(k - 3))), hget(k - 3)), [(k - 3) * c for c in hget(k - 3)])
        v = padd(v, [-c for c in pmul([0, 1, -1], inner)])
    rhs = {0: [1], 2: [0, 1]}.get(k, [0])
    ok_c5a &= (ptrim(v) == ptrim(rhs))
report('T3.6-H', ok_deg and ok_hN and ok_hpde and ok_c5a,
       'h_k=(1-t)^{k+1}sum_m U_k(m)t^m has degree<=k-1 (t^k..t^20 vanish), == sum_q N(k,q)t^{q-1}(1-t)^{k-q} (k>=1) [=1+(Ncal(z(1-t),t/(1-t))-1)/t]; '
       'H-PDE z^k coefficients exact for k<=%d; c5a form gives the same equations' % KH)

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY a1 pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
