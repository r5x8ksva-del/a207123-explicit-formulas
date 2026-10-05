# -*- coding: utf-8 -*-
"""final-audit / math-c1c2 : self-written helpers (no import of core.py / polylib.py / c2a_lib / c2b code).

Ground truth comes only from the original definition
    good(a,b,c)  <=>  b == c  or  a >= max(b,c)
applied to height sequences h in {0..m}^k.
"""
from math import comb, factorial
from collections import defaultdict
import itertools


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def C(a, b):
    """combinatorial binomial: 0 unless 0 <= b <= a."""
    if b < 0 or a < 0 or b > a:
        return 0
    return comb(a, b)


def Cpoly(a, b):
    """polynomial binomial a(a-1)...(a-b+1)/b! (b>=0), 0 for b<0."""
    if b < 0:
        return 0
    num = 1
    for t in range(b):
        num *= (a - t)
    return num // factorial(b) if num % factorial(b) == 0 else None


# ---------------------------------------------------------------- brute force
def enum_full(m, k):
    """Enumerate all (m+1)^k sequences. Returns dict key -> count with keys
       ('c', s)        legal, not ending with an ascent, s ascents
       ('E', s, j)     legal, ending with an ascent h_{k-1} < h_k = j, s ascents."""
    res = defaultdict(int)
    for h in itertools.product(range(m + 1), repeat=k):
        if not all(good(h[i], h[i + 1], h[i + 2]) for i in range(k - 2)):
            continue
        s = sum(1 for i in range(k - 1) if h[i] < h[i + 1])
        if k >= 2 and h[-2] < h[-1]:
            res[('E', s, h[-1])] += 1
        else:
            res[('c', s)] += 1
    return dict(res)


def enum_dfs(m, k):
    """Same output as enum_full but by DFS over legal prefixes."""
    res = defaultdict(int)
    seq = []

    def rec():
        if len(seq) == k:
            s = sum(1 for i in range(k - 1) if seq[i] < seq[i + 1])
            if k >= 2 and seq[-2] < seq[-1]:
                res[('E', s, seq[-1])] += 1
            else:
                res[('c', s)] += 1
            return
        for v in range(m + 1):
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec()
            seq.pop()
    rec()
    return dict(res)


def dp_refined(m, K):
    """Transfer DP over (last two values, #ascents) straight from good().
    Returns list over k=0..K of dict key->count with the same keys as enum_full."""
    out = []
    out.append({('c', 0): 1})                       # k = 0
    if K >= 1:
        out.append({('c', 0): m + 1})               # k = 1
    if K < 2:
        return out
    cnt = defaultdict(int)                          # (a, b, s) -> number
    for a in range(m + 1):
        for b in range(m + 1):
            cnt[(a, b, 1 if a < b else 0)] += 1

    def summarize(cnt):
        r = defaultdict(int)
        for (a, b, s), v in cnt.items():
            if a < b:
                r[('E', s, b)] += v
            else:
                r[('c', s)] += v
        return dict(r)
    out.append(summarize(cnt))
    for k in range(3, K + 1):
        new = defaultdict(int)
        for (a, b, s), v in cnt.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c, s + (1 if b < c else 0))] += v
        cnt = new
        out.append(summarize(cnt))
    return out


def dp_total(m, K):
    """[U_0(m),...,U_K(m)] by plain transfer DP over last two values."""
    out = [1]
    if K >= 1:
        out.append(m + 1)
    if K < 2:
        return out
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    out.append((m + 1) ** 2)
    for k in range(3, K + 1):
        new = defaultdict(int)
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] += v
        cnt = new
        out.append(sum(cnt.values()))
    return out


def U_s(tab, k, m, s):
    """U_k(m,s) from a refined table dict-of-dicts tab[m][k]."""
    d = tab[m][k]
    tot = d.get(('c', s), 0)
    for key, v in d.items():
        if key[0] == 'E' and key[1] == s:
            tot += v
    return tot


# ---------------------------------------------------------------- numbers
def stirling2(nmax):
    S = [[0] * (nmax + 2) for _ in range(nmax + 2)]
    S[0][0] = 1
    for n in range(1, nmax + 1):
        for kk in range(1, n + 1):
            S[n][kk] = kk * S[n - 1][kk] + S[n - 1][kk - 1]
    return S


def h_complete(s, lo, hi):
    """complete homogeneous h_s(lo, lo+1, ..., hi); empty set -> [s==0]; s<0 -> 0"""
    if s < 0:
        return 0
    row = [1] + [0] * s
    for v in range(lo, hi + 1):
        for t in range(1, s + 1):
            row[t] += v * row[t - 1]
    return row[s]


def rgs_partitions(n):
    """all restricted growth strings of length n (set partitions of [n])."""
    if n == 0:
        yield ()
        return
    def rec(prefix, mx):
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for v in range(mx + 2):
            prefix.append(v)
            yield from rec(prefix, max(mx, v))
            prefix.pop()
    yield from rec([0], 0)


def r_stirling_brute(n, k, r):
    """# partitions of [n] into k blocks with 1..r in distinct blocks (brute force)."""
    cnt = 0
    for g in rgs_partitions(n):
        if (max(g) + 1 if g else 0) != k:
            continue
        if len(set(g[:r])) != min(r, n):
            continue
        cnt += 1
    return cnt


def falling(i, j):
    r = 1
    for t in range(j):
        r *= (i - t)
    return r


def c_series(i, N):
    """c_i(n) = [x^n] 1/(1-x-i x^3), n=0..N, by the recurrence c(n)=c(n-1)+i c(n-3)."""
    c = [0] * (N + 1)
    for n in range(N + 1):
        v = 1 if n == 0 else 0
        if n >= 1:
            v += c[n - 1]
        if n >= 3:
            v += i * c[n - 3]
        c[n] = v
    return c


def c_explicit(i, n):
    if n < 0:
        return 0
    return sum(C(n - 2 * j, j) * i ** j for j in range(n // 3 + 1))


# ---------------------------------------------------------------- univariate integer polys (lists, low->high)
def pmul(a, b, N=None):
    if not a or not b:
        return []
    n = len(a) + len(b) - 1
    if N is not None:
        n = min(n, N + 1)
    r = [0] * n
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if i + j >= n:
                break
            r[i + j] += ai * bj
    return r


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pscale(a, c):
    return [c * x for x in a]


def ptrim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def b_poly(v):
    return [1, -1, 0, -v]


def P_poly(m):
    r = [1]
    for v in range(m + 1):
        r = ptrim(pmul(r, ptrim(b_poly(v))))
    return r


def W_poly(m):
    """W_m = 1 + x^2 sum_{j=1}^m j P_{j-1}"""
    r = [1]
    for j in range(1, m + 1):
        r = padd(r, [0, 0] + pscale(P_poly(j - 1), j))
    return ptrim(r)


def series_inv(a, N):
    """1/a as power series to x^N; a[0] must be +-1."""
    assert a[0] in (1, -1)
    inv = [0] * (N + 1)
    inv[0] = a[0]
    for n in range(1, N + 1):
        s = 0
        for i in range(1, min(n, len(a) - 1) + 1):
            s += a[i] * inv[n - i]
        inv[n] = -s * a[0]
    return inv
