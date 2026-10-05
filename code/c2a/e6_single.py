# -*- coding: utf-8 -*-
"""探索 6：单个 U_k(m) 的计算耗时（不同 k/m 比例下各方法的优劣）。所有方法结果互相核对。"""
import os, sys, time
from math import comb, factorial
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c2a_lib import c_explicit, N_triangle
from polylib import P_poly


def single_H(k, m):
    S = k // 3 + 1
    # h_s(j..m), j = m..0
    rows = [None] * (m + 2)
    rows[m + 1] = [1] + [0] * S
    for j in range(m, -1, -1):
        nxt = rows[j + 1]
        row = [1] + [0] * S
        for s in range(1, S + 1):
            row[s] = nxt[s] + j * row[s - 1]
        rows[j] = row
    def cb(a, b):
        return comb(a, b) if 0 <= b <= a else 0
    tot = sum(rows[0][s] * cb(k + m - 2 * s, m + s) for s in range(k // 3 + 1))
    n = k - 2
    if n >= 0:
        for j in range(1, m + 1):
            tot += j * sum(rows[j][s] * cb(n + m - j - 2 * s, m - j + s) for s in range(n // 3 + 1))
    return tot


def single_Theta(k, m):
    cache = {}
    def c(i, n):
        if (i, n) not in cache:
            cache[(i, n)] = c_explicit(i, n)
        return cache[(i, n)]
    def Th(t, n):
        s = sum((-1) ** r * comb(t, r) * c(m - r, n) for r in range(t + 1))
        q, rem = divmod(s, factorial(t))
        assert rem == 0
        return q
    return Th(m, k + 1 + 3 * m) - sum(Th(t, k + 3 * t) for t in range(m))


def single_F4(k, m):
    tot = 0
    for i in range(m + 1):
        inner = c_explicit(i, k + 3 * m)
        ff = 1
        for j in range(1, i + 1):
            ff *= (i - j + 1)
            inner += j * ff * c_explicit(i, k + 3 * m - 3 * j - 2)
        tot += (-1) ** (m - i) * comb(m, i) * inner
    q, rem = divmod(tot, factorial(m))
    assert rem == 0
    return q


def single_lemma1(k, m):
    # 只保留 m 方向一行一行推进：T[k'][0..m]
    rows = {-2: None, -1: None}
    prev = [[1] * (m + 1)]           # k'=0
    hist = {0: [1] * (m + 1)}
    def get(kk, mm):
        if kk == 0 or kk == -1:
            return 1
        if kk == -2:
            return 0
        return hist[kk][mm]
    for kk in range(1, k + 1):
        row = [0] * (m + 1)
        for mm in range(m + 1):
            row[mm] = (row[mm - 1] if mm else 0) + get(kk - 1, mm) + mm * get(kk - 3, mm)
        hist[kk] = row
        hist.pop(kk - 4, None)
    return hist[k][m]


def single_Ntri(k, m):
    N = N_triangle(k)
    return sum(N[k][q] * comb(m + 1, q) for q in range(0, min(k, m + 1) + 1))


def single_linrec(k, m):
    # 用引理 1 生成前 3m+1 项（避免另写级数除法），然后用 P_m 的线性递推
    P = P_poly(m)
    L = len(P) - 1
    n0 = min(k + 1, 3 * m + 1)
    col = [single_lemma1(kk, m) for kk in range(n0)] if n0 <= 60 else None
    if col is None:
        return None
    for kk in range(n0, k + 1):
        col.append(-sum(P[l] * col[kk - l] for l in range(1, L + 1)))
    return col[k]


cases = [(3000, 3), (1500, 30), (300, 300), (40, 3000)]
methods = [('H form', single_H), ('Theta (C4)', single_Theta), ('F4', single_F4),
           ('Lemma 1 table', single_lemma1), ('N triangle', single_Ntri), ('lin. rec. (m<=19)', single_linrec)]
for (k, m) in cases:
    out = {}
    line = []
    for name, f in methods:
        if name.startswith('lin') and 3 * m + 1 > 60:
            continue
        if (name.startswith('Theta') or name.startswith('F4')) and m > 400:
            line.append('%s skipped (O(m^2) huge terms)' % name)
            continue
        if name.startswith('N tri') and k > 400:
            line.append('%s skipped (O(k^2) table of huge ints)' % name)
            continue
        t0 = time.perf_counter()
        v = f(k, m)
        dt = time.perf_counter() - t0
        out[name] = v
        line.append('%s %.3fs' % (name, dt))
    vals = set(out.values())
    print('k=%d m=%d  digits=%d  all_equal=%s' % (k, m, len(str(next(iter(vals)))), len(vals) == 1))
    print('   ' + ' | '.join(line))
