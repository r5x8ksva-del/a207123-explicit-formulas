# -*- coding: utf-8 -*-
"""r-c2a 复核脚本 3：单值计时的公平性检查。
c2a 的 e6_single.py 中：H 型的 r-Stirling 原子用递推表算（O(m*k/3) 次小乘法），
而 Θ / F4 的 c_i(n) 原子每个都用显式和 sum_l C(n-2l,l) i^l 重新算（O(m^2) 个 c 值、每个 O(n/3) 项大整数幂）。
这里把两边的原子都换成同一类算法再比：
  H_rec   : r-Stirling 用递推（同 c2a）
  H_expl  : r-Stirling 用显式交错式 (1/t!) sum_r (-1)^r C(t,r)(m-r)^p（与 c_i 显式和对等）
  Th_rec  : Θ 型，c_i(n) 用 1/(1-x-ix^3) 的三项递推（与 H_rec 对等）
  F4_rec  : F4，c_i(n) 用三项递推
  Th_expl : Θ 型，c_i 用显式和（同 c2a，带缓存）——只在较小规模上跑
用法：py -3.14 r3_timing_fair.py [k m]...
"""
import sys
import time
from math import comb, factorial


def C(a, b):
    if b < 0 or a < 0 or b > a:
        return 0
    return comb(a, b)


def H_rec(k, m):
    S = k // 3 + 1
    rows = [None] * (m + 2)
    rows[m + 1] = [1] + [0] * S
    for j in range(m, -1, -1):
        nxt = rows[j + 1]
        row = [1] + [0] * S
        for s in range(1, S + 1):
            row[s] = nxt[s] + j * row[s - 1]
        rows[j] = row
    tot = sum(rows[0][s] * C(k + m - 2 * s, m + s) for s in range(k // 3 + 1))
    n = k - 2
    if n >= 0:
        for j in range(1, m + 1):
            tot += j * sum(rows[j][s] * C(n + m - j - 2 * s, m - j + s) for s in range(n // 3 + 1))
    return tot


def rS_expl(s, j, m):
    """h_s(j..m) = (1/t!) sum_r (-1)^r C(t,r) (m-r)^{s+t}, t=m-j（定理 2）。"""
    t = m - j
    v = sum((-1) ** r * comb(t, r) * (m - r) ** (s + t) for r in range(t + 1))
    q, rr = divmod(v, factorial(t))
    assert rr == 0
    return q


def H_expl(k, m):
    tot = sum(rS_expl(s, 0, m) * C(k + m - 2 * s, m + s) for s in range(k // 3 + 1))
    n = k - 2
    if n >= 0:
        for j in range(1, m + 1):
            tot += j * sum(rS_expl(s, j, m) * C(n + m - j - 2 * s, m - j + s) for s in range(n // 3 + 1))
    return tot


def c_rec_rows(m, N):
    tab = []
    for i in range(m + 1):
        c = [0] * (N + 1)
        for n in range(N + 1):
            c[n] = (1 if n == 0 else 0) + (c[n - 1] if n >= 1 else 0) + (i * c[n - 3] if n >= 3 else 0)
        tab.append(c)
    return tab


def Th_rec(k, m):
    CT = c_rec_rows(m, k + 1 + 3 * m)

    def Th(t, n):
        s = sum((-1) ** r * comb(t, r) * CT[m - r][n] for r in range(t + 1))
        q, rr = divmod(s, factorial(t))
        assert rr == 0
        return q
    return Th(m, k + 1 + 3 * m) - sum(Th(t, k + 3 * t) for t in range(m))


def F4_rec(k, m):
    CT = c_rec_rows(m, k + 3 * m)
    tot = 0
    for i in range(m + 1):
        c = CT[i]
        inner = c[k + 3 * m]
        ff = 1
        for j in range(1, i + 1):
            ff *= (i - j + 1)
            nn = k + 3 * m - 3 * j - 2
            if nn >= 0:
                inner += j * ff * c[nn]
        tot += (-1) ** (m - i) * comb(m, i) * inner
    q, rr = divmod(tot, factorial(m))
    assert rr == 0
    return q


def c_expl(i, n):
    if n < 0:
        return 0
    return sum(C(n - 2 * l, l) * i ** l for l in range(n // 3 + 1))


def Th_expl(k, m):
    cache = {}

    def c(i, n):
        if (i, n) not in cache:
            cache[(i, n)] = c_expl(i, n)
        return cache[(i, n)]

    def Th(t, n):
        s = sum((-1) ** r * comb(t, r) * c(m - r, n) for r in range(t + 1))
        q, rr = divmod(s, factorial(t))
        assert rr == 0
        return q
    return Th(m, k + 1 + 3 * m) - sum(Th(t, k + 3 * t) for t in range(m))


def lemma1(k, m):
    hist = {0: [1] * (m + 1)}

    def get(kk, mm):
        if kk in (0, -1):
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


args = [int(a) for a in sys.argv[1:]]
cases = list(zip(args[0::2], args[1::2])) or [(300, 300), (1500, 30), (3000, 3), (150, 150)]
for (k, m) in cases:
    out, line = {}, []
    meths = [('lemma1', lemma1), ('H_rec', H_rec), ('H_expl', H_expl), ('Th_rec', Th_rec), ('F4_rec', F4_rec)]
    if m <= 160:
        meths.append(('Th_expl', Th_expl))
    for name, f in meths:
        t0 = time.perf_counter()
        v = f(k, m)
        dt = time.perf_counter() - t0
        out[name] = v
        line.append('%s %.3fs' % (name, dt))
    vals = set(out.values())
    print('k=%d m=%d digits=%d all_equal=%s :: %s' % (k, m, len(str(out['lemma1'])), len(vals) == 1, ' | '.join(line)), flush=True)
