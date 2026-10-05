# -*- coding: utf-8 -*-
"""final-audit / math-c1c2 / a1b : larger-range check of T2.2's refined lemma 1 (with the report's boundary
conventions) and of T2.4's refined formula, using a suffix-sum transfer DP that is still a literal
implementation of good(a,b,c) <=> b==c or a>=max(b,c):
   new[b][c][s + [b<c]] += sum_{a : good(a,b,c)} cnt[a][b][s]
   b == c : all a ;  b != c : a >= max(b,c).
Cross-checked against the naive DP of mylib on k<=40, m<=12 first."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mylib import *

T0 = time.time()
NPASS = NFAIL = 0


def rep(ok, cid, msg):
    global NPASS, NFAIL
    NPASS += ok
    NFAIL += (not ok)
    print(('PASS ' if ok else 'FAIL ') + cid + ' ' + msg, flush=True)


def dp_fast_refined(m, K):
    """returns T[k][s] = U_k(m,s), k=0..K"""
    S = K // 3 + 2
    T = [[0] * (S + 1) for _ in range(K + 1)]
    T[0][0] = 1
    if K >= 1:
        T[1][0] = m + 1
    if K < 2:
        return T
    n = m + 1
    # cnt[a][b][s]
    cnt = [[[0] * (S + 1) for _ in range(n)] for _ in range(n)]
    for a in range(n):
        for b in range(n):
            cnt[a][b][1 if a < b else 0] += 1
    for s in range(S + 1):
        T[2][s] = sum(cnt[a][b][s] for a in range(n) for b in range(n))
    for k in range(3, K + 1):
        new = [[[0] * (S + 1) for _ in range(n)] for _ in range(n)]
        for b in range(n):
            # suffix sums over a for fixed b: suf[t][s] = sum_{a>=t} cnt[a][b][s]
            suf = [[0] * (S + 1) for _ in range(n + 1)]
            for a in range(n - 1, -1, -1):
                ca = cnt[a][b]
                sa = suf[a + 1]
                suf[a] = [sa[s] + ca[s] for s in range(S + 1)]
            for c in range(n):
                src = suf[0] if c == b else suf[max(b, c)]
                inc = 1 if b < c else 0
                row = new[b][c]
                for s in range(S + 1 - inc):
                    row[s + inc] += src[s]
        cnt = new
        for s in range(S + 1):
            T[k][s] = sum(cnt[a][b][s] for a in range(n) for b in range(n))
    return T


# cross-check vs naive DP
bad = []
for m in range(0, 13):
    naive = dp_refined(m, 40)
    fast = dp_fast_refined(m, 40)
    for k in range(41):
        for s in range(len(fast[k])):
            nv = sum(v for key, v in naive[k].items() if key[1] == s)
            if nv != fast[k][s]:
                bad.append((m, k, s))
rep(not bad, 'ext.anchor', 'suffix-sum refined DP == naive refined DP (k<=40, m<=12); bad=%s' % bad[:3])

KX, MX = 80, 24
S2 = stirling2(200)
bad_l = []
bad_f = []
for m in range(0, MX + 1):
    T = dp_fast_refined(m, KX)
    SS = KX // 3 + 2

    def U(k, s, mm=None):
        return 0

    for k in range(1, KX + 1):
        for s in range(0, SS + 1):
            lhs = T[k][s]
            # report's conventions
            def Ur(kk, mm, ss, Tm):
                if kk == 0:
                    return 1 if ss == 0 else 0
                if kk < 0:
                    return 0
                if mm == -1:
                    return 0
                if ss < 0:
                    return 0
                return Tm[kk][ss] if ss < len(Tm[kk]) else 0
            Tprev = Tprev_store if m >= 1 else None
            a = Ur(k, m - 1, s, Tprev) if m >= 1 else 0
            rhs = a + Ur(k - 1, m, s, T) + m * Ur(k - 3, m, s - 1, T) + (m if (k == 2 and s == 1) else 0)
            if lhs != rhs:
                bad_l.append((k, m, s))
    for k in range(0, KX + 1):
        for s in range(0, SS + 1):
            f = S2[m + s][m] * C(k + m - 2 * s, k - 3 * s) + sum(
                j * h_complete(s - 1, j, m) * C(k + m - j - 2 * s, k + 1 - 3 * s) for j in range(1, m + 1))
            if f != T[k][s]:
                bad_f.append((k, m, s))
    Tprev_store = T
rep(not bad_l, 'ext.T2.2.refined_lemma', 'refined lemma 1 with the report conventions, 1<=k<=%d, 0<=m<=%d, all s; bad=%s' % (KX, MX, bad_l[:3]))
rep(not bad_f, 'ext.T2.4.refined', 'U_k(m,s) formula of T2.4 == DP, 0<=k<=%d, 0<=m<=%d, all s; bad=%s' % (KX, MX, bad_f[:3]))
print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY a1b pass=%d fail=%d' % (NPASS, NFAIL))
