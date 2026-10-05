# -*- coding: utf-8 -*-
"""final-audit / math-c1c2 / a3 : T2.8.
 (1) N(k,q) = sum_{i=1}^q (-1)^{q-i} C(q,i) U_k(i-1) (k>=1); k=0 with the i=0 term.
 (2) R(p,s) by direct enumeration of skeletons (s arcs (v_t,a_t), v_1>=...>=v_s, 0<=a_t<v_t,
     endpoint set exactly {0..p-1}) vs  sum_{i=0}^p (-1)^{p-i} C(p,i) S(i-1+s,i-1) with i=0 term [s=0];
     R(2s,s) = (2s-1)!!;
     N^c(k,q) = sum_s sum_{p<=2s} C(q,p) R(p,s) C(k-2s+p-1, s+q-1) vs brute force/DP on words with
     value set exactly {0..q-1} not ending in an ascent; the (k,q)=(0,0) exception.
No import of core/polylib."""
import sys, os, time, itertools
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mylib import *

T0 = time.time()
NPASS = NFAIL = 0


def rep(ok, cid, msg):
    global NPASS, NFAIL
    NPASS += bool(ok)
    NFAIL += (not ok)
    print(('PASS ' if ok else 'FAIL ') + cid + ' ' + msg, flush=True)


S = stirling2(80)


def S2(n, k):
    if n < 0 or k < 0:
        return None
    return S[n][k]


# ---------------- skeletons
def skeleton_counts(smax, pmax):
    """R[(p,s)] by enumeration. heads v in 0..pmax-1."""
    R = defaultdict(int)
    for s in range(0, smax + 1):
        # sequences of arcs with nonincreasing heads; heads <= pmax-1
        def rec(t, prev_v, arcs):
            if t == s:
                cov = set()
                for (v, a) in arcs:
                    cov.add(v); cov.add(a)
                p = len(cov)
                if cov == set(range(p)):
                    R[(p, s)] += 1
                return
            for v in range(1, prev_v + 1):
                for a in range(0, v):
                    arcs.append((v, a))
                    rec(t + 1, v, arcs)
                    arcs.pop()
        rec(0, pmax - 1, [])
    return R


SMAX = 5
Rb = skeleton_counts(SMAX, 2 * SMAX)


def R_formula(p, s):
    tot = 0
    for i in range(0, p + 1):
        if i == 0:
            term = 1 if s == 0 else 0
        else:
            term = S[i - 1 + s][i - 1]
        tot += (-1) ** (p - i) * C(p, i) * term
    return tot


bad = []
for s in range(0, SMAX + 1):
    for p in range(0, 2 * s + 3):
        if Rb.get((p, s), 0) != R_formula(p, s):
            bad.append((p, s, Rb.get((p, s), 0), R_formula(p, s)))
rep(not bad, 'T2.8.R', 'R(p,s) by skeleton enumeration == sum_i (-1)^{p-i}C(p,i)S(i-1+s,i-1) (i=0 term [s=0]); s<=%d, p<=2s+2; bad=%s' % (SMAX, bad[:3]))


def dfact(n):
    r = 1
    while n > 1:
        r *= n
        n -= 2
    return r


ok = all(R_formula(2 * s, s) == dfact(2 * s - 1) for s in range(0, 12)) and all(Rb[(2 * s, s)] == dfact(2 * s - 1) for s in range(0, SMAX + 1))
ok = ok and R_formula(0, 0) == 1 and all(R_formula(p, s) == 0 for s in range(0, 10) for p in range(2 * s + 1, 2 * s + 5))
rows = {s: [R_formula(p, s) for p in range(0, 2 * s + 1)] for s in (2, 3, 4)}
print('# R rows:', rows)
rep(ok and rows[2] == [0, 0, 1, 4, 3] and rows[3] == [0, 0, 1, 12, 36, 40, 15] and rows[4] == [0, 0, 1, 28, 183, 496, 655, 420, 105],
    'T2.8.R2s', 'R(2s,s)=(2s-1)!! (s<=11; enumeration s<=5), R(0,0)=1, R(p,s)=0 for p>2s; first rows as in notes/c2b.md')


# ---------------- surjective words, ending type
def Nsplit_brute(k):
    """dict (q, 'c'/'E') -> count, by DFS over legal words with values < k; value set must be {0..q-1}"""
    res = defaultdict(int)
    if k == 0:
        res[(0, 'c')] = 1
        return res
    seq = []

    def rec():
        if len(seq) == k:
            st = set(seq)
            q = len(st)
            if st == set(range(q)):
                typ = 'E' if (k >= 2 and seq[-2] < seq[-1]) else 'c'
                res[(q, typ)] += 1
            return
        for v in range(k):
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec()
            seq.pop()
    rec()
    return res


def Nsplit_dp(k, q):
    """N^c(k,q), N^E(k,q) by DP with state (last two values, bitmask of used values), values in 0..q-1"""
    if k == 0:
        return (1, 0) if q == 0 else (0, 0)
    if q == 0:
        return (0, 0)
    full = (1 << q) - 1
    if k == 1:
        return (1, 0) if q == 1 else (0, 0)
    cnt = defaultdict(int)
    for a in range(q):
        for b in range(q):
            cnt[(a, b, (1 << a) | (1 << b))] += 1
    for _ in range(3, k + 1):
        new = defaultdict(int)
        for (a, b, msk), v in cnt.items():
            for c in range(q):
                if good(a, b, c):
                    new[(b, c, msk | (1 << c))] += v
        cnt = new
    nc = sum(v for (a, b, msk), v in cnt.items() if msk == full and a >= b)
    ne = sum(v for (a, b, msk), v in cnt.items() if msk == full and a < b)
    return nc, ne


def Nc_formula(k, q):
    tot = 0
    for s in range(0, k + 2):
        for p in range(0, 2 * s + 1):
            tot += C(q, p) * R_formula(p, s) * C(k - 2 * s + p - 1, s + q - 1)
    return tot


bad = []
for k in range(0, 10):
    br = Nsplit_brute(k)
    for q in range(0, k + 2):
        nc_b = br.get((q, 'c'), 0)
        nc_d, ne_d = Nsplit_dp(k, q)
        if nc_b != nc_d or br.get((q, 'E'), 0) != ne_d:
            bad.append(('dp', k, q))
        f = Nc_formula(k, q)
        if (k, q) == (0, 0):
            if not (f == 0 and nc_b == 1):
                bad.append(('00', f, nc_b))
        elif f != nc_b:
            bad.append(('f', k, q, f, nc_b))
rep(not bad, 'T2.8.Nc_small', 'N^c formula == DFS brute force (k<=9, all q), except (k,q)=(0,0): formula 0, truth 1; DP==DFS; bad=%s' % bad[:3])

bad = []
for k in range(0, 23):
    for q in range(0, 9):
        nc_d, ne_d = Nsplit_dp(k, q)
        f = Nc_formula(k, q)
        if (k, q) == (0, 0):
            continue
        if f != nc_d:
            bad.append((k, q, f, nc_d))
rep(not bad, 'T2.8.Nc_dp', 'N^c formula == bitmask DP from good(), 0<=k<=22, 0<=q<=8 ((0,0) excluded); bad=%s' % bad[:3])

# ---------------- (1) inversion
bad = []
cols = {m: dp_total(m, 22) for m in range(0, 9)}
for k in range(0, 23):
    for q in range(0, 9):
        nc_d, ne_d = Nsplit_dp(k, q)
        if k >= 1:
            inv = sum((-1) ** (q - i) * C(q, i) * cols[i - 1][k] for i in range(1, q + 1))
        else:
            inv = sum((-1) ** (q - i) * C(q, i) * (1 if i == 0 else cols[i - 1][0]) for i in range(0, q + 1))
        if inv != nc_d + ne_d:
            bad.append((k, q))
rep(not bad, 'T2.8.inversion', 'N(k,q)=sum_{i=1}^q (-1)^{q-i}C(q,i)U_k(i-1) (k>=1; k=0 with i=0 term, U_0(-1)=1) == bitmask DP, k<=22, q<=8; bad=%s' % bad[:3])

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY a3 pass=%d fail=%d' % (NPASS, NFAIL))
