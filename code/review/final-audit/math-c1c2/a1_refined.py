# -*- coding: utf-8 -*-
"""final-audit / math-c1c2 / a1 :
T2.1 stats, T2.2 (refined lemma 1 + its boundary conventions, G_m(x,y), PDE), T2.3, T2.4 (refined and
unrefined), 07 formula page bounds.  Truth = enumeration / DP from good() only (mylib)."""
import sys, os, time
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mylib import *

T0 = time.time()
NPASS = NFAIL = 0


def rep(ok, cid, msg):
    global NPASS, NFAIL
    if ok:
        NPASS += 1
    else:
        NFAIL += 1
    print(('PASS ' if ok else 'FAIL ') + cid + ' ' + msg, flush=True)


# ------------------------------------------------------------------ ground truth tables
MREF, KREF = 12, 40
ref = {m: dp_refined(m, KREF) for m in range(MREF + 1)}          # ref[m][k] -> dict

# anchor 1: DP vs full enumeration of all (m+1)^k sequences
bad = []
nseq = 0
for m in range(0, 8):
    for k in range(0, 12):
        if (m + 1) ** k > 1_200_000:
            continue
        nseq += (m + 1) ** k
        e = enum_full(m, k) if k > 0 else {('c', 0): 1}
        d = {kk: v for kk, v in ref[m][k].items() if v}
        if e != d:
            bad.append((m, k))
rep(not bad, 'anchor.full_enum', 'refined DP (by #ascents and ending) == enumeration of all (m+1)^k sequences, '
    '(m+1)^k<=1.2e6, m<=7, k<=11; %d sequences; bad=%s' % (nseq, bad[:5]))

# anchor 2: DP vs DFS (bigger)
bad = []
for m in range(0, 7):
    for k in range(0, 12):
        if m >= 5 and k > 10:
            continue
        e = enum_dfs(m, k) if k > 0 else {('c', 0): 1}
        d = {kk: v for kk, v in ref[m][k].items() if v}
        if e != d:
            bad.append((m, k))
rep(not bad, 'anchor.dfs', 'refined DP == DFS enumeration of legal sequences (m<=4,k<=11; m=5,6,k<=10); bad=%s' % bad[:5])

# anchor 3: prompt table (section 2)
PROMPT = {1: [1, 2, 3, 4, 5, 6, 7], 2: [1, 4, 9, 16, 25, 36, 49], 3: [1, 6, 17, 36, 65, 106, 161],
          4: [1, 9, 32, 80, 165, 301, 504], 5: [1, 14, 64, 192, 457, 938, 1736],
          6: [1, 21, 119, 419, 1136, 2604, 5306], 7: [1, 31, 214, 873, 2669, 6778, 15108],
          8: [1, 46, 388, 1837, 6334, 17802, 43326], 9: [1, 68, 694, 3788, 14666, 45488, 120650],
          10: [1, 100, 1222, 7629, 32971, 112349, 323647]}
ok = all(sum(ref[m][k].values()) == PROMPT[k][m] for k in PROMPT for m in range(7))
rep(ok, 'anchor.prompt', 'DP totals == prompt table k=1..10, m=0..6')


def U(k, m, s):
    if k < 0 or m < 0 or s < 0:
        return 0
    return U_s(ref, k, m, s)


SMAX = KREF // 3 + 2

# ------------------------------------------------------------------ T2.2 refined lemma with the report's conventions
def Ur_report(k, m, s):
    """boundary conventions exactly as written in 03_C2.md T2.2"""
    if k == 0:
        return 1 if s == 0 else 0          # U_0(m,s)=[s=0]
    if k in (-1, -2):
        return 0                           # U_{-1}=U_{-2}=0
    if m == -1:
        return 0                           # U_k(-1,s)=0 (k>=1)
    if s < 0:
        return 0
    return U(k, m, s)


bad = []
for m in range(0, MREF + 1):
    for k in range(1, KREF + 1):
        for s in range(0, SMAX + 1):
            lhs = U(k, m, s)
            rhs = (Ur_report(k, m - 1, s) + Ur_report(k - 1, m, s) + m * Ur_report(k - 3, m, s - 1)
                   + (m if (k == 2 and s == 1) else 0))
            if lhs != rhs:
                bad.append((k, m, s, lhs, rhs))
rep(not bad, 'T2.2.refined_lemma', 'U_k(m,s)=U_k(m-1,s)+U_{k-1}(m,s)+m U_{k-3}(m,s-1)+m[k=2][s=1] with '
    'U_0(m,s)=[s=0], U_{-1}=U_{-2}=0, U_k(-1,s)=0 (k>=1): 1<=k<=%d, 0<=m<=%d, all s; bad=%s' % (KREF, MREF, bad[:4]))

# the warning: T1.1's U_{-1}=1 must not be reused (two natural variants)
def Ur_alt(k, m, s, variant):
    if k == -1:
        return 1 if variant == 'const1' else (1 if s == 0 else 0)
    return Ur_report(k, m, s)


fails = {}
for variant in ('const1', 'delta_s0'):
    cnt = 0
    for m in range(1, 6):
        for s in range(0, 4):
            k = 2
            rhs = (Ur_alt(k, m - 1, s, variant) + Ur_alt(k - 1, m, s, variant) + m * Ur_alt(k - 3, m, s - 1, variant)
                   + (m if s == 1 else 0))
            if rhs != U(2, m, s):
                cnt += 1
    fails[variant] = cnt
rep(all(v > 0 for v in fails.values()), 'T2.2.no_U-1=1',
    'using U_{-1}=1 (or U_{-1}(.,s)=[s=0]) together with m[k=2][s=1] breaks k=2 (double count): #bad (m<=5,s<=3) = %s' % fails)

# check that the k=2 recurrence with the report's conventions is literally U_2(m,s) = U_2(m-1,s)+U_1(m,s)+m[s=1]
ok = all(U(2, m, 0) == (m + 1) * (m + 2) // 2 and U(2, m, 1) == m * (m + 1) // 2 for m in range(MREF + 1))
rep(ok, 'T2.2.k2', 'U_2(m,0)=C(m+2,2), U_2(m,1)=C(m+1,2) (m<=12)')

# ------------------------------------------------------------------ G_m(x,y): closed forms as bivariate series
K2, M2 = 30, 10
S2 = K2 // 3 + 2


def bz():
    return [[0] * (S2 + 1) for _ in range(K2 + 1)]


def bmul(A, B):
    R = bz()
    for i in range(K2 + 1):
        for t in range(S2 + 1):
            a = A[i][t]
            if a == 0:
                continue
            for j in range(K2 + 1 - i):
                Bj = B[j]
                for u in range(S2 + 1 - t):
                    if Bj[u]:
                        R[i + j][t + u] += a * Bj[u]
    return R


def badd(A, B):
    return [[A[i][t] + B[i][t] for t in range(S2 + 1)] for i in range(K2 + 1)]


def bsc(A, c):
    return [[c * A[i][t] for t in range(S2 + 1)] for i in range(K2 + 1)]


def bshift(A, dx, dy):
    R = bz()
    for i in range(K2 + 1 - dx):
        for t in range(S2 + 1 - dy):
            R[i + dx][t + dy] = A[i][t]
    return R


def bdiv(A, B):
    """A/B, B[0][0]==1"""
    assert B[0][0] == 1
    nz = [(j, u, B[j][u]) for j in range(K2 + 1) for u in range(S2 + 1) if B[j][u] and (j, u) != (0, 0)]
    Q = bz()
    for i in range(K2 + 1):
        for t in range(S2 + 1):
            v = A[i][t]
            for (j, u, b) in nz:
                if j <= i and u <= t:
                    q = Q[i - j][t - u]
                    if q:
                        v -= b * q
            Q[i][t] = v
    return Q


def bv(v):
    B = bz()
    B[0][0] = 1
    B[1][0] = -1
    B[3][1] = -v                      # 1 - x - v y x^3
    return B


ONE = bz(); ONE[0][0] = 1
Pm = [None] * (M2 + 2)
cur = ONE
for v in range(0, M2 + 1):
    cur = bmul(cur, bv(v))
    Pm[v] = cur                       # Pm[v] = P_v(x,y)
bad_w = []
bad_q = []
for m in range(0, M2 + 1):
    W = ONE
    for j in range(1, m + 1):
        W = badd(W, bsc(bshift(Pm[j - 1], 2, 1), j))
    G1 = bdiv(W, Pm[m])
    # 1/P_m + y x^2 sum_j j / prod_{v=j}^m b_v
    G2 = bdiv(ONE, Pm[m])
    for j in range(1, m + 1):
        Qj = ONE
        for v in range(j, m + 1):
            Qj = bmul(Qj, bv(v))
        G2 = badd(G2, bsc(bshift(bdiv(ONE, Qj), 2, 1), j))
    for k in range(K2 + 1):
        for s in range(S2 + 1):
            if G1[k][s] != U(k, m, s):
                bad_w.append((m, k, s))
            if G2[k][s] != U(k, m, s):
                bad_q.append((m, k, s))
rep(not bad_w and not bad_q, 'T2.2.gf_closed', 'G_m(x,y)=W_m/P_m=1/P_m+y x^2 sum_j j/prod_{v=j}^m b_v (b_v=1-x-v y x^3) '
    'coefficientwise == refined DP, k<=%d, m<=%d, all s; bad=%s %s' % (K2, M2, bad_w[:3], bad_q[:3]))

# recurrence form (1-x-m y x^3) G_m = G_{m-1} + m y x^2, G_{-1}=1
bad = []
for m in range(0, MREF + 1):
    for k in range(0, KREF + 1):
        for s in range(0, SMAX + 1):
            lhs = U(k, m, s) - U(k - 1, m, s) - m * U(k - 3, m, s - 1)
            prev = (1 if (k == 0 and s == 0) else 0) if m == 0 else U(k, m - 1, s)
            rhs = prev + (m if (k == 2 and s == 1) else 0)
            if lhs != rhs:
                bad.append((m, k, s))
rep(not bad, 'T2.2.gf_rec', '(1-x-m y x^3)G_m=G_{m-1}+m y x^2, G_{-1}=1 coefficientwise, k<=40, m<=12; bad=%s' % bad[:3])

# PDE (1-x-t)F - y x^3 t dF/dt = 1 + y x^2 t/(1-t)^2
bad = []
for m in range(0, MREF + 1):
    for k in range(0, KREF + 1):
        for s in range(0, SMAX + 1):
            lhs = U(k, m, s) - U(k - 1, m, s) - U(k, m - 1, s) - m * U(k - 3, m, s - 1)
            rhs = (1 if (k == 0 and m == 0 and s == 0) else 0) + (m if (k == 2 and s == 1) else 0)
            if lhs != rhs:
                bad.append((m, k, s))
rep(not bad, 'T2.2.pde', '(1-x-t)F - y x^3 t F_t = 1 + y x^2 t/(1-t)^2 coefficientwise, k<=40, m<=12, all s; bad=%s' % bad[:3])

# ------------------------------------------------------------------ T2.1 statistics
bad = []
for m in range(0, 5):
    for k in range(2, 10):
        # ascents == #T + #E via greedy parse, ends with ascent <=> last block E
        import itertools
        for h in itertools.product(range(m + 1), repeat=k):
            if not all(good(h[i], h[i + 1], h[i + 2]) for i in range(k - 2)):
                continue
            # parse
            pos, nT, nE, last = 0, 0, 0, None
            hh = list(h)
            while pos < k:
                M = max(hh[pos:])
                if hh[pos] == M:
                    pos += 1; last = 'S'
                elif k - pos == 2:
                    pos += 2; nE += 1; last = 'E'
                else:
                    assert hh[pos + 1] == M and hh[pos + 2] == M
                    pos += 3; nT += 1; last = 'T'
            asc = sum(1 for i in range(k - 1) if h[i] < h[i + 1])
            if asc != nT + nE or ((h[-2] < h[-1]) != (last == 'E')):
                bad.append(h)
rep(not bad, 'T2.1.stats', 'greedy block parse: #ascents = #T+#E and (ends with ascent <=> last block E), all legal h, m<=4, 2<=k<=9; bad=%s' % bad[:3])

# ------------------------------------------------------------------ H atoms
S = stirling2(120)
HM = 14


def H(m, s, j):
    return h_complete(s, j, m) if s >= 0 else 0


# recurrence (07) and explicit alternating formula (07)
bad = []
for m in range(0, HM + 1):
    for j in range(0, m + 2):
        for s in range(0, 20):
            h = H(m, s, j) if j <= m else (1 if s == 0 else 0)
            if j <= m:
                rec = H(m, s, j + 1) if j + 1 <= m else (1 if s == 0 else 0)
                rec += j * H(m, s - 1, j)
                if s == 0:
                    rec = 1
                if rec != h:
                    bad.append(('rec', m, s, j))
                L = m - j
                num = sum((-1) ** (L - i) * C(L, i) * (j + i) ** (s + L) for i in range(L + 1))
                if num % factorial(L) != 0 or num // factorial(L) != h:
                    bad.append(('expl', m, s, j))
rep(not bad, '07.H_rec_explicit', 'H(m,s,j)=H(m,s,j+1)+j H(m,s-1,j), H(m,0,j)=1, H(m,s,m+1)=[s=0]; '
    'H(m,s,j)=(1/(m-j)!) sum_i (-1)^{m-j-i} C(m-j,i)(j+i)^{s+m-j}; 0<=j<=m<=14, s<20; bad=%s' % bad[:3])

# H(m,s,0)=H(m,s,1)=S(m+s,m) and r-Stirling by brute force set partitions
bad = []
for m in range(0, 15):
    for s in range(0, 20):
        if not (H(m, s, 0) == S[m + s][m] and (m == 0 or H(m, s, 1) == S[m + s][m])):
            bad.append(('S', m, s))
for m in range(1, 8):
    for s in range(0, 9 - m + 1):
        for j in range(1, m + 1):
            if m + s > 9:
                continue
            if r_stirling_brute(m + s, m, j) != H(m, s, j):
                bad.append(('r', m, s, j))
rep(not bad, 'T2.3.rstirling', 'H(m,s,0)=H(m,s,1)=S(m+s,m) (m<15,s<20); H(m,s,j)={m+s, m}_j by brute-force set partitions (m+s<=9); bad=%s' % bad[:3])

# T2.3(3): (1/t!) nabla^t i^p |_{i=m} = h_{p-t}(m-t..m) = {p+m-t, m}_{m-t}
bad = []
for m in range(0, 13):
    for t in range(0, m + 1):
        for p in range(0, 31):
            val = Fraction(sum((-1) ** r * C(t, r) * (m - r) ** p for r in range(t + 1)), factorial(t))
            if val != h_complete(p - t, m - t, m):
                bad.append((m, t, p))
for m in range(1, 7):
    for t in range(0, m + 1):
        for p in range(t, t + 9 - m + 1):
            if p + m - t > 9:
                continue
            if r_stirling_brute(p + m - t, m, m - t) != h_complete(p - t, m - t, m):
                bad.append(('r', m, t, p))
rep(not bad, 'T2.3.nabla', '(1/t!) sum_r (-1)^r C(t,r)(m-r)^p == h_{p-t}(m-t..m) (t<=m<=12, p<=30) == brute r-Stirling (n<=9); bad=%s' % bad[:3])

# T2.3(1) coefficient extraction [x^n y^s] prod_{v=j}^m b_v^{-1}
bad = []
for m in range(0, M2 + 1):
    for j in range(0, m + 1):
        Qj = ONE
        for v in range(j, m + 1):
            Qj = bmul(Qj, bv(v))
        I = bdiv(ONE, Qj)
        for n in range(K2 + 1):
            for s in range(S2 + 1):
                if I[n][s] != H(m, s, j) * C(n + m - j - 2 * s, n - 3 * s):
                    bad.append((m, j, n, s))
rep(not bad, 'T2.3.coef', '[x^n y^s] prod_{v=j}^m (1-x-v y x^3)^{-1} = H(m,s,j) C(n+m-j-2s,n-3s), n<=30, 0<=j<=m<=10; bad=%s' % bad[:3])

# ------------------------------------------------------------------ T2.4
bad_ref = []
bad_parts = []
for m in range(0, MREF + 1):
    for k in range(0, KREF + 1):
        d = ref[m][k]
        for s in range(0, SMAX + 1):
            first = S[m + s][m] * C(k + m - 2 * s, k - 3 * s)
            second = sum(j * H(m, s - 1, j) * C(k + m - j - 2 * s, k + 1 - 3 * s) for j in range(1, m + 1))
            if first + second != U(k, m, s):
                bad_ref.append((k, m, s))
            if first != d.get(('c', s), 0):
                bad_parts.append(('c', k, m, s))
            for j in range(1, m + 1):
                if j * H(m, s - 1, j) * C(k + m - j - 2 * s, k + 1 - 3 * s) != d.get(('E', s, j), 0):
                    bad_parts.append(('E', k, m, s, j))
rep(not bad_ref, 'T2.4.refined', 'U_k(m,s)=S(m+s,m)C(k+m-2s,k-3s)+sum_j j H(m,s-1,j) C(k+m-j-2s,k+1-3s) == DP, '
    '0<=k<=%d, 0<=m<=%d, all s; bad=%s' % (KREF, MREF, bad_ref[:3]))
rep(not bad_parts, 'T2.4.parts', 'term-by-term meaning: first term == #(not ending in ascent, s ascents); j-th summand == '
    '#(ending with ascent to value j, s ascents); k<=40, m<=12; bad=%s' % bad_parts[:3])

# unrefined, 07 version with explicit upper limits, against plain DP k<=60, m<=20
bad = []
for m in range(0, 21):
    col = dp_total(m, 60)
    for k in range(0, 61):
        f1 = sum(S[m + s][m] * C(k + m - 2 * s, k - 3 * s) for s in range(0, k // 3 + 1))
        f2 = sum(j * sum(H(m, s, j) * C(k - 2 + m - j - 2 * s, k - 2 - 3 * s) for s in range(0, (k - 2) // 3 + 1))
                 for j in range(1, m + 1))
        if f1 + f2 != col[k]:
            bad.append((k, m))
rep(not bad, 'T2.4.U(07)', 'U_k(m)=sum_{s<=floor(k/3)} S(m+s,m)C(k+m-2s,k-3s)+sum_j j sum_{s<=floor((k-2)/3)} H(m,s,j)C(k-2+m-j-2s,k-2-3s) '
    '== plain DP, 0<=k<=60, 0<=m<=20; bad=%s' % bad[:3])

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY a1 pass=%d fail=%d' % (NPASS, NFAIL))
