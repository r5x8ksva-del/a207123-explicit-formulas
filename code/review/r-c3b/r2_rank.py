# -*- coding: utf-8 -*-
"""r-c3b 复核脚本 2：独立重做 c3b 的线性代数实验（E1/E2/E2S/E3A/E3B/E3S），并扩大参数尝试打破。

独立性：
  - U 表用任务说明里的参考实现 U_list 重建（r1 已证明与 core.U_fast_table 在 40x40 上逐项相等）；
  - N 表用容斥 N(k,q)=sum_i (-1)^{q-i}C(q,i)U_k(i-1) 自己算；
  - 模 p 消元、左倍式生成、精确核对都是本脚本重写的，不导入 c3b 的任何代码；
  - 素数换成 p1=1000000007、p2=998244353（c3b 用的是 2^31-1 和 2147483629）。
逻辑（与 c3b 相同，且严格）：模 p 列满秩 => Q 上列满秩；dim ker_Q <= dim ker_p；
若给出 dim ker_p 个精确成立、且模 p 线性无关的整数关系，则 ker_Q 恰为其张成。
额外：对几个小盒子做完全精确的有理数核计算（Bareiss 无除法消元，取部分方程即可上界核维数）。
"""
import sys, os, time
from math import comb
from collections import defaultdict
import numpy as np

T0 = time.time()
LOG = []


def out(s):
    print(s)
    sys.stdout.flush()
    LOG.append(s)


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def U_list(m, K):
    o = [1, m + 1]
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    o.append(sum(cnt.values()))
    for k in range(3, K + 1):
        new = defaultdict(int)
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] += v
        cnt = new
        o.append(sum(cnt.values()))
    return o


K = M = 40
cols = [U_list(m, K) for m in range(M + 1)]
U = [[cols[m][k] for m in range(M + 1)] for k in range(K + 1)]


def Nval(k, q):
    s = 0
    for i in range(q + 1):
        u = (1 if k == 0 else 0) if i == 0 else U[k][i - 1]
        s += (-1) ** (q - i) * comb(q, i) * u
    return s


N = [[Nval(k, q) for q in range(M + 1)] for k in range(K + 1)]
out('tables built %.1fs' % (time.time() - T0))

P1, P2 = 1000000007, 998244353


def rank_p(mat, p):
    """mat: numpy int64 (entries in [0,p)), p < 2^30 => products < 2^60. Plain column-pivot elimination."""
    A = mat.copy()
    nr, nc = A.shape
    rk = 0
    for c in range(nc):
        if rk >= nr:
            break
        piv = None
        nzs = np.flatnonzero(A[rk:, c])
        if nzs.size == 0:
            continue
        piv = rk + int(nzs[0])
        if piv != rk:
            tmp = A[rk].copy()
            A[rk] = A[piv]
            A[piv] = tmp
        inv = pow(int(A[rk, c]), -1, p)
        A[rk] = (A[rk] * inv) % p
        below = np.flatnonzero(A[rk + 1:, c]) + rk + 1
        if below.size:
            f = A[below, c].reshape(-1, 1)
            A[below] = (A[below] - (f * A[rk].reshape(1, -1)) % p) % p
        rk += 1
    return rk


def build(tab, unk, k0, m0, p):
    rows = []
    for k in range(k0, K + 1):
        for m in range(m0, M + 1):
            rows.append([(tab[k - a][m - b] * pow(k, i, p) * pow(m, j, p)) % p for (a, b, i, j) in unk])
    return np.array(rows, dtype=np.int64)


def unk_list(A, B, monos):
    return [(a, b, i, j) for a in range(A + 1) for b in range(B + 1) for (i, j) in monos]


# ---- 左倍式：k^i m^j X^al E^-be * G，G = {(a,b): {(ii,jj): c}}，系数多项式要做 (k,m)->(k-al, m-be) ----
def shift_poly(poly, al, be):
    res = defaultdict(int)
    for (ii, jj), c in poly.items():
        for s in range(ii + 1):
            for t in range(jj + 1):
                res[(s, t)] += c * comb(ii, s) * (-al) ** (ii - s) * comb(jj, t) * (-be) ** (jj - t)
    return {k_: v for k_, v in res.items() if v}


def lmul(G, al, be, i, j):
    res = defaultdict(int)
    for (a, b), poly in G.items():
        for (s, t), c in shift_poly(poly, al, be).items():
            res[(a + al, b + be, s + i, t + j)] += c
    return {k_: v for k_, v in res.items() if v}


L1 = {(0, 0): {(0, 0): 1}, (0, 1): {(0, 0): -1}, (1, 0): {(0, 0): -1}, (3, 0): {(0, 1): -1}}
# L_N = 1 - X - XY - (q-1) X^3 (1+Y)^2
LN = {(0, 0): {(0, 0): 1}, (1, 0): {(0, 0): -1}, (1, 1): {(0, 0): -1},
      (3, 0): {(0, 1): -1, (0, 0): 1}, (3, 1): {(0, 1): -2, (0, 0): 2}, (3, 2): {(0, 1): -1, (0, 0): 1}}


def gens(G, A, B, okmono, maxdeg=12):
    res = []
    for al in range(A + 1):
        for be in range(B + 1):
            for i in range(maxdeg + 1):
                for j in range(maxdeg + 1 - i):
                    op = lmul(G, al, be, i, j)
                    if all(a <= A and b <= B and okmono(ii, jj) for (a, b, ii, jj) in op):
                        res.append(op)
    return res


def exact_holds(tab, op, k0, m0):
    for k in range(k0, K + 1):
        for m in range(m0, M + 1):
            if sum(c * k ** ii * m ** jj * tab[k - a][m - b] for (a, b, ii, jj), c in op.items()) != 0:
                return False
    return True


RES = []


def konly(tab, name, A, B, D, k0=None, m0=None, primes=(P1, P2)):
    k0 = A if k0 is None else k0
    m0 = B if m0 is None else m0
    unk = unk_list(A, B, [(i, 0) for i in range(D + 1)])
    rks = []
    for p in primes:
        rks.append(rank_p(build(tab, unk, k0, m0, p), p))
    full = all(r == len(unk) for r in rks)
    neq = (K + 1 - k0) * (M + 1 - m0)
    out('%s %s k-only (A,B,deg)=(%d,%d,%d) quadrant [%d..40]x[%d..40]: %d unknowns/%d eqs, ranks mod %s = %s -> %s'
        % ('PASS' if full else 'FAIL', name, A, B, D, k0, m0, len(unk), neq, primes, rks,
           'no relation' if full else 'KERNEL FOUND'))
    RES.append(full)


def kmexp(tab, name, G, gbox, A, B, D=None, Dk=None, Dm=None, k0=None, m0=None, pred=None, primes=(P1, P2)):
    k0 = A if k0 is None else k0
    m0 = B if m0 is None else m0
    if D is not None:
        monos = [(i, j) for i in range(D + 1) for j in range(D + 1 - i)]
        okm = (lambda ii, jj: ii + jj <= D)
        tag = 'totdeg<=%d' % D
    else:
        monos = [(i, j) for i in range(Dk + 1) for j in range(Dm + 1)]
        okm = (lambda ii, jj: ii <= Dk and jj <= Dm)
        tag = 'deg_k<=%d,deg_2<=%d' % (Dk, Dm)
    unk = unk_list(A, B, monos)
    idx = {u: t for t, u in enumerate(unk)}
    kds = []
    for p in primes:
        kds.append(len(unk) - rank_p(build(tab, unk, k0, m0, p), p))
    gs = gens(G, A, B, okm)
    vecs = []
    for g in gs:
        v = [0] * len(unk)
        for key, c in g.items():
            v[idx[key]] += c
        vecs.append(v)
    grs = [rank_p(np.array([[c % p for c in v] for v in vecs], dtype=np.int64), p) if vecs else 0 for p in primes]
    ex = all(exact_holds(tab, g, k0, m0) for g in gs)
    pv = pred
    ok = ex and all(kd == len(gs) for kd in kds) and all(gr == len(gs) for gr in grs) and (pv is None or pv == len(gs))
    neq = (K + 1 - k0) * (M + 1 - m0)
    out('%s %s (A,B)=(%d,%d) %s quadrant [%d..40]x[%d..40]: %d unknowns/%d eqs; ker_p=%s; left multiples=%d (rank_p %s, exact=%s); formula=%s'
        % ('PASS' if ok else 'FAIL', name, A, B, tag, k0, m0, len(unk), neq, kds, len(gs), grs, ex, pv))
    RES.append(ok)


def predU(A, B, D):
    return (A - 2) * B * D * (D + 1) // 2 if (A >= 3 and B >= 1 and D >= 1) else 0


def predUs(A, B, Dk, Dm):
    return (A - 2) * B * (Dk + 1) * Dm if (A >= 3 and B >= 1 and Dm >= 1) else 0


def predN(A, B, D):
    return (A - 2) * (B - 1) * D * (D + 1) // 2 if (A >= 3 and B >= 2 and D >= 1) else 0


def predNs(A, B, Dk, Dm):
    return (A - 2) * (B - 1) * (Dk + 1) * Dm if (A >= 3 and B >= 2 and Dm >= 1) else 0


out('=== R-E1: U, k-only coefficients: re-run of c3b check-module parameter sets with two new primes ===')
for (A, B, D) in [(6, 6, 6), (10, 3, 6), (3, 10, 6), (4, 4, 12), (15, 1, 8), (1, 15, 8)]:
    konly(U, 'U', A, B, D)
out('=== R-E1+: U, k-only, NEW parameter sets / later quadrants (attempt to break) ===')
for (A, B, D) in [(30, 1, 3), (1, 30, 3), (8, 8, 4), (20, 4, 2), (4, 20, 2), (35, 0, 5), (0, 35, 5)]:
    konly(U, 'U', A, B, D)
konly(U, 'U', 6, 6, 6, k0=16, m0=16)
konly(U, 'U', 3, 3, 10, k0=20, m0=20)

out('=== R-E2: U, (k,m)-coefficients, total degree: re-run + new boxes + later quadrants ===')
for (A, B, D) in [(3, 1, 1), (3, 1, 3), (5, 2, 2), (6, 2, 3), (4, 3, 4), (6, 4, 2), (2, 6, 4), (6, 0, 4),
                  (10, 2, 2), (6, 6, 2), (3, 8, 2), (8, 4, 3), (12, 1, 2), (3, 1, 5)]:
    kmexp(U, 'U', L1, (3, 1), A, B, D=D, pred=predU(A, B, D))
kmexp(U, 'U', L1, (3, 1), 5, 2, D=2, k0=12, m0=9, pred=predU(5, 2, 2))
kmexp(U, 'U', L1, (3, 1), 6, 4, D=2, k0=14, m0=12, pred=predU(6, 4, 2))
kmexp(U, 'U', L1, (3, 1), 4, 3, D=3, k0=20, m0=20, pred=predU(4, 3, 3))
out('=== R-E2S: U, graded degrees ===')
for (A, B, Dk, Dm) in [(4, 2, 3, 2), (5, 3, 1, 3), (3, 2, 5, 0), (5, 2, 2, 1), (4, 3, 0, 2), (6, 2, 1, 1), (3, 1, 0, 1)]:
    kmexp(U, 'U', L1, (3, 1), A, B, Dk=Dk, Dm=Dm, pred=predUs(A, B, Dk, Dm))

out('=== R-E3A: N, k-only ===')
for (A, B, D) in [(6, 6, 6), (10, 3, 6), (3, 10, 6), (4, 4, 12), (15, 1, 8), (1, 15, 8),
                  (30, 1, 3), (1, 30, 3), (8, 8, 4)]:
    konly(N, 'N', A, B, D)
konly(N, 'N', 6, 6, 6, k0=16, m0=16)
out('=== R-E3B: N, (k,q)-coefficients ===')
for (A, B, D) in [(3, 2, 1), (3, 2, 3), (5, 3, 2), (6, 3, 3), (4, 4, 4), (6, 4, 2), (3, 1, 3), (2, 4, 3),
                  (10, 3, 2), (6, 6, 2), (3, 8, 2), (8, 4, 3), (3, 2, 5)]:
    kmexp(N, 'N', LN, (3, 2), A, B, D=D, pred=predN(A, B, D))
kmexp(N, 'N', LN, (3, 2), 5, 3, D=2, k0=12, m0=10, pred=predN(5, 3, 2))
kmexp(N, 'N', LN, (3, 2), 4, 4, D=3, k0=18, m0=18, pred=predN(4, 4, 3))
out('=== R-E3S: N, graded ===')
for (A, B, Dk, Dm) in [(4, 3, 3, 2), (5, 4, 1, 3), (3, 3, 5, 0), (5, 3, 2, 1), (4, 4, 0, 2), (3, 2, 0, 1)]:
    kmexp(N, 'N', LN, (3, 2), A, B, Dk=Dk, Dm=Dm, pred=predNs(A, B, Dk, Dm))

out('elapsed %.1fs' % (time.time() - T0))
out('SUMMARY r2 pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
