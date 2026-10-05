# -*- coding: utf-8 -*-
"""x1-single-sum 复核脚本 r5：试图用更大的参数范围「打破」定理 S / 命题 S' / E 的单和不可能结论（精确线性代数）。

形状 V(k) = sum_{s} A(s) C(k+c-g s, e s + d)，s 取遍使下指标 >=0 的全部整数（含负 s），只要求 k0<=k<=KL 成立
（k0>0 对应「对充分大的 k 成立」的版本）。若任何一个方程组相容，就与已证明的结论矛盾。
求解：模 2^61-1 消元，若 [A|V] 列满秩（=> 有理数上不相容，严格）直接判否，否则 Fraction 精确消元。
对照组：A_m(k)（完整部分，(2,1) 形 c=d=m 可解）；E(k,1)（(2,1) 形 c=-2,d=0 可解）。
"""
import sys
import time
from fractions import Fraction as F
from math import comb

T0 = time.time()
FAILS = []


def log(s):
    print(s, flush=True)


def check(name, ok, desc):
    log(('PASS ' if ok else 'FAIL ') + name + ' ' + desc)
    if not ok:
        FAILS.append(name)


def C(n, r):
    if r < 0 or n < 0 or r > n:
        return 0
    return comb(n, r)


def tables(m, K):
    n = m + 1
    U = [1, n] + [0] * (K - 1)
    E = [0] * (K + 1)
    cnt = {(a, b): 1 for a in range(n) for b in range(n)}
    U[2] = n * n
    E[2] = sum(1 for a in range(n) for b in range(n) if a < b)
    for k in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in range(n):
                if b == c or (a >= b and a >= c):
                    new[(b, c)] = new.get((b, c), 0) + v
        cnt = new
        U[k] = sum(cnt.values())
        E[k] = sum(v for (b, c), v in cnt.items() if b < c)
    A = [u - e for u, e in zip(U, E)]
    return U, A, E


P1 = (1 << 61) - 1


def rank_modp(M, ncols):
    M = [[v % P1 for v in row] for row in M]
    r = 0
    for col in range(ncols):
        piv = next((i for i in range(r, len(M)) if M[i][col]), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][col], -1, P1)
        M[r] = [v * inv % P1 for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][col]:
                f = M[i][col]
                M[i] = [(x - f * y) % P1 for x, y in zip(M[i], M[r])]
        r += 1
    return r


def consistent(V, c, g, d, e, k0):
    K = len(V) - 1
    cols = []
    # e>0 时下指标 >=0 自动给出 s 的下界；e=0 时 s 无自然下界，取 s>=-3（等价于平移 c 后 s>=0 的形状）
    for s in range(-60 if e > 0 else -3, 200):
        r = d + e * s
        if r < 0:
            continue
        kmin = max(k0, r + g * s - c)
        if kmin <= K:
            cols.append(s)
        elif s > 0 and g + e > 0:
            break
    rows = [[C(k + c - g * s, d + e * s) for s in cols] for k in range(k0, K + 1)]
    # 去掉在 k0..K 上全零的列
    keep = [j for j in range(len(cols)) if any(row[j] for row in rows)]
    rows = [[row[j] for j in keep] for row in rows]
    n = len(keep)
    Vs = V[k0:K + 1]
    if n == 0:
        return all(v == 0 for v in Vs)
    aug = [row + [Vs[t]] for t, row in enumerate(rows)]
    if n + 1 <= len(rows) and rank_modp(aug, n + 1) == n + 1:
        return False
    M = [[F(v) for v in row] for row in aug]
    r = 0
    for col in range(n):
        piv = next((i for i in range(r, len(M)) if M[i][col] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][col]
        M[r] = [x / pv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][col] != 0:
                f = M[i][col]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        r += 1
    return all(M[i][-1] == 0 for i in range(r, len(M)))


KL = 70
TAB = {m: tables(m, KL) for m in range(0, 5)}

# (1) 定理 S：(2,1) 形，U, m=1..3；E, m=2..4
found = []
nsys = 0
for m in (1, 2, 3):
    U, A, E = TAB[m]
    for c in range(-15, 16):
        for d in range(-10, 16):
            for k0 in (0, 12, 24):
                nsys += 1
                if consistent(U, c, 2, d, 1, k0):
                    found.append(('U', m, c, d, k0))
for m in (2, 3, 4):
    U, A, E = TAB[m]
    for c in range(-15, 16):
        for d in range(-10, 16):
            for k0 in (0, 12, 24):
                nsys += 1
                if consistent(E, c, 2, d, 1, k0):
                    found.append(('E', m, c, d, k0))
ctrl = all(consistent(TAB[m][1], m, 2, m, 1, 0) for m in (1, 2, 3)) and consistent(TAB[1][2], -2, 2, 0, 1, 0)
check('r5.thmS_linsys', found == [] and ctrl,
      'exact: (2,1)-shape single sums for U (m=1..3) and E (m=2..4), c in [-15,15], d in [-10,15], s over all integers, valid on k0<=k<=70 with k0 in {0,12,24}: '
      'all %d systems inconsistent; controls A_m (c=d=m) and E(k,1) (c=-2,d=0) consistent' % nsys)

# (2) 命题 S'：(1,1),(2,0),(2,2),(1,3),(3,0) 形，U, m=1,2
found2 = []
nsys2 = 0
for m in (1, 2):
    U = TAB[m][0]
    for (g, e) in ((1, 1), (2, 0), (2, 2), (1, 3), (3, 0)):
        for c in range(-12, 13):
            for d in range(-6, 11):
                for k0 in (0, 15):
                    nsys2 += 1
                    if consistent(U, c, g, d, e, k0):
                        found2.append((m, g, e, c, d, k0))
check('r5.Sprime_linsys', found2 == [],
      "exact: S' shapes (1,1),(2,0),(2,2),(1,3),(3,0) for U, m=1,2, c in [-12,12], d in [-6,10], k0 in {0,15}, k<=70: all %d systems inconsistent" % nsys2)

log('# elapsed %.1fs' % (time.time() - T0))
log('SUMMARY r5 fail=%d' % len(FAILS))
sys.exit(1 if FAILS else 0)
