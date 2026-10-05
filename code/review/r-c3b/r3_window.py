# -*- coding: utf-8 -*-
"""r-c3b 复核脚本 3：判定 r2 中两个 FAIL（N 在晚起点象限上出现额外核）是否为有限窗口伪关系。

做法：在 [k0..40]x[q0..40] 上求模 p 核的一组基，然后把方程扩展到 k in [41..KX]（q 仍 <= 40，N 表用参考实现
U_list 算到 k=KX 再容斥），看这些核向量是否仍是关系。若扩展后核维数降回理论值，则多出来的是窗口伪关系，
与定理 4 / 定理 3′（对象限 k>=k0, q>=q0 的一切点成立的关系）不矛盾。
同时统计窗口里有多少行是“非平凡行”（N(k,q)=0 当 q>k 造成整行为 0）。
"""
import sys, time
from math import comb
from collections import defaultdict
import numpy as np

T0 = time.time()


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


KX, M = 100, 40
cols = [U_list(m, KX) for m in range(M + 1)]
U = [[cols[m][k] for m in range(M + 1)] for k in range(KX + 1)]


def Nval(k, q):
    s = 0
    for i in range(q + 1):
        u = (1 if k == 0 else 0) if i == 0 else U[k][i - 1]
        s += (-1) ** (q - i) * comb(q, i) * u
    return s


N = [[Nval(k, q) for q in range(M + 1)] for k in range(KX + 1)]
print('tables k<=%d, q<=%d built %.1fs' % (KX, M, time.time() - T0))
P = 1000000007


def rref(mat, p):
    A = mat.copy() % p
    nr, nc = A.shape
    piv = []
    r = 0
    for c in range(nc):
        if r >= nr:
            break
        nz = np.flatnonzero(A[r:, c])
        if nz.size == 0:
            continue
        i = r + int(nz[0])
        if i != r:
            t = A[r].copy(); A[r] = A[i]; A[i] = t
        A[r] = (A[r] * pow(int(A[r, c]), -1, p)) % p
        oth = np.flatnonzero(A[:, c]); oth = oth[oth != r]
        if oth.size:
            f = A[oth, c].reshape(-1, 1)
            A[oth] = (A[oth] - (f * A[r].reshape(1, -1)) % p) % p
        piv.append(c)
        r += 1
    return r, piv, A[:r]


def kernel_basis(mat, p):
    r, piv, R = rref(mat, p)
    nc = mat.shape[1]
    ps = set(piv)
    free = [c for c in range(nc) if c not in ps]
    basis = []
    for f in free:
        v = np.zeros(nc, dtype=np.int64)
        v[f] = 1
        for row, c in enumerate(piv):
            v[c] = (-int(R[row, f])) % p
        basis.append(v)
    return basis


def build(tab, unk, krange, qrange, p):
    rows = []
    for k in krange:
        for q in qrange:
            rows.append([(tab[k - a][q - b] * pow(k, i, p) * pow(q, j, p)) % p for (a, b, i, j) in unk])
    return np.array(rows, dtype=np.int64)


def analyse(name, A, B, monos, k0, q0, Kwin=40, Kext=KX):
    unk = [(a, b, i, j) for a in range(A + 1) for b in range(B + 1) for (i, j) in monos]
    Mw = build(N, unk, range(k0, Kwin + 1), range(q0, M + 1), P)
    nontriv = int(np.count_nonzero(np.any(Mw != 0, axis=1)))
    basis = kernel_basis(Mw, P)
    print('%s: window [%d..%d]x[%d..%d]: %d unknowns, %d rows (%d non-zero rows), kernel dim mod p = %d'
          % (name, k0, Kwin, q0, M, len(unk), Mw.shape[0], nontriv, len(basis)))
    Mx = build(N, unk, range(k0, Kext + 1), range(q0, M + 1), P)
    rk, _, _ = rref(Mx, P)
    print('   extended window [%d..%d]x[%d..%d]: %d rows, kernel dim mod p = %d'
          % (k0, Kext, q0, M, Mx.shape[0], len(unk) - rk))
    # how many of the window-kernel basis vectors survive on the extension rows?
    Me = build(N, unk, range(Kwin + 1, Kext + 1), range(q0, M + 1), P).astype(object)
    surv = 0
    for v in basis:
        res = Me.dot(v.astype(object))
        if all(int(x) % P == 0 for x in res):
            surv += 1
    print('   window-kernel basis vectors still relations on rows k in [41..%d]: %d of %d' % (Kext, surv, len(basis)))
    return len(basis), len(unk) - rk


# FAIL 1: N, k-only coefficients, (A,B,deg)=(6,6,6) on [16..40]^2 ; theory (Thm 4): no relation on any quadrant
analyse('N k-only (6,6,6)', 6, 6, [(i, 0) for i in range(7)], 16, 16)
# FAIL 2: N, (k,q) coefficients total degree <=3, box (4,4) on [18..40]^2 ; theory (Thm 3'): 36
analyse('N (k,q)-coef (4,4,3)', 4, 4, [(i, j) for i in range(4) for j in range(4 - i)], 18, 18)
# control: same as c3b parameters (quadrant starts at (A,B))
analyse('N k-only (6,6,6) control', 6, 6, [(i, 0) for i in range(7)], 6, 6)
print('elapsed %.1fs' % (time.time() - T0))
