# -*- coding: utf-8 -*-
"""s7：扩大范围的三项检查。
 (a) U_k 在负整数处的全部零点：用 G_{-j-1}=(1-x+jx^3)G_{-j}+jx^2（截断到 x^K）扫 j<=JMAX，
     检查是否存在 j > floor((k+2)/3) 的额外零点（T15 的“⟺”按全局理解是否成立）。
 (b) h_k 实根且单根：自写整数 Sturm，k 从 KLO 到 KHI。
 (c) 相邻 h_k、h_{k+1} 的根是否交错：精确隔离（Sturm + 有理二分），2<=k<=KINT。
"""
import sys, os, time
from fractions import Fraction as Fr
from math import comb, gcd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rlib import U_rec_table, peval, trim

mode = sys.argv[1]
t0 = time.time()

if mode == 'zeros':
    K = int(sys.argv[2])
    JMAX = int(sys.argv[3])
    g = [1] + [0] * K           # G_{-1}
    found = []
    for j in range(1, JMAX + 1):
        # 现在 g = G_{-j} 截断；检查 j > s_k 的零点
        for k in range(1, K + 1):
            if g[k] == 0 and j > (k + 2) // 3:
                found.append((k, j))
        # G_{-j-1}
        new = [0] * (K + 1)
        for i in range(K + 1):
            v = g[i]
            if i >= 1:
                v -= g[i - 1]
            if i >= 3:
                v += j * g[i - 3]
            if i == 2:
                v += j
            new[i] = v
        g = new
    print('(a) extra zeros U_k(-j)=0 with j>floor((k+2)/3), 1<=k<=%d, 1<=j<=%d:' % (K, JMAX), found if found else 'none',
          '(%.1fs)' % (time.time() - t0))
    sys.exit(0)

K = 160
T = U_rec_table(K, K + 2)
H = {}
for k in range(K + 1):
    h = [sum((-1) ** (i - j) * comb(k + 1, i - j) * T[k][j] for j in range(i + 1)) for i in range(k + 1)]
    H[k] = trim(h)


def prim(p):
    p = trim(p)
    g = 0
    for c in p:
        g = gcd(g, c)
    return [c // g for c in p] if g > 1 else p


def ideriv(p):
    return trim([i * p[i] for i in range(1, len(p))])


def prem_pos(A, B):
    A = list(A)
    db = len(B) - 1
    delta = len(A) - 1 - db
    lb = B[-1]
    A = [c * abs(lb) ** (delta + 1) for c in A]
    while len(A) - 1 >= db and A:
        c = A[-1]
        q = c // lb
        assert q * lb == c
        sh = len(A) - 1 - db
        for i, b in enumerate(B):
            A[sh + i] -= q * b
        A = trim(A)
    return A


def sturm_seq(p):
    p = prim(p)
    seq = [p, prim(ideriv(p))]
    while len(seq[-1]) > 1:
        r = prem_pos(seq[-2], seq[-1])
        if not r:
            break
        seq.append(prim([-c for c in r]))
    return seq


def var(vals):
    v = [x for x in vals if x != 0]
    return sum(1 for a, b in zip(v, v[1:]) if (a > 0) != (b > 0))


def V_inf(seq, sign):
    return var([s[-1] * (sign ** (len(s) - 1)) for s in seq])


def V_at(seq, x):
    return var([peval(s, x) for s in seq])


if mode == 'rr':
    KLO, KHI = int(sys.argv[2]), int(sys.argv[3])
    bad = []
    for k in range(KLO, KHI + 1):
        t1 = time.time()
        seq = sturm_seq(H[k])
        d = len(H[k]) - 1
        nreal = V_inf(seq, -1) - V_inf(seq, 1)
        ok = (nreal == d) and len(seq[-1]) == 1 and (V_at(seq, 0) - V_at(seq, 1) == 0)
        if not ok:
            bad.append((k, nreal, d))
        print('  k=%d deg=%d distinct real roots=%d squarefree=%s (%.1fs)' % (k, d, nreal, len(seq[-1]) == 1, time.time() - t1))
        sys.stdout.flush()
    print('(b) h_k real-rooted, simple roots, none in [0,1], %d<=k<=%d:' % (KLO, KHI), 'all OK' if not bad else bad,
          '(%.1fs)' % (time.time() - t0))

if mode == 'interlace':
    KINT = int(sys.argv[2])

    def isolate(p, width):
        seq = sturm_seq(p)
        bound = 1 + max(abs(Fr(c, p[-1])) for c in p[:-1])
        stack = [(-bound - 1, bound + 1)]
        out = []
        while stack:
            a, b = stack.pop()
            n = V_at(seq, a) - V_at(seq, b)
            if n == 0:
                continue
            if n == 1 and b - a < width:
                out.append((a, b))
                continue
            mid = (a + b) / 2
            while peval(p, mid) == 0:
                mid += (b - a) / 7
            stack.append((a, mid))
            stack.append((mid, b))
        return sorted(out)

    res = {}
    for k in range(2, KINT + 1):
        ra = isolate(H[k], Fr(1, 10 ** 12))
        rb = isolate(H[k + 1], Fr(1, 10 ** 12))
        ivs = sorted([(a, b, 0) for a, b in ra] + [(a, b, 1) for a, b in rb])
        disjoint = all(ivs[i][1] < ivs[i + 1][0] for i in range(len(ivs) - 1))
        labs = [l for _, _, l in ivs]
        alternating = all(labs[i] != labs[i + 1] for i in range(len(labs) - 1))
        res[k] = (len(ra) == len(H[k]) - 1, len(rb) == len(H[k + 1]) - 1, disjoint, alternating)
    print('(c) interlacing h_k vs h_{k+1}, 2<=k<=%d: (all isolated, disjoint intervals, alternating?)' % KINT)
    print('    any alternating:', [k for k, v in res.items() if v[3]], '; all isolated & disjoint:',
          all(v[0] and v[1] and v[2] for v in res.values()), '(%.1fs)' % (time.time() - t0))
