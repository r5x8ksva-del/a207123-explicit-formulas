# -*- coding: utf-8 -*-
"""审计 a1-formulas：T3.8 的关系空间维数公式（模素数精确线性代数，若干盒子抽查）。

U 的关系：R=Σ_{a<=A,b<=B} r_ab(k,m) X^a E^{-b}，r_ab 为 (k,m) 的多项式；在 k∈[A,40]、m∈[B,40] 上零化 U。
报告：总次数<=D 时维数 (A-2)·B·D(D+1)/2；分次 (deg_k<=Dk, deg_m<=Dm) 时 (A-2)·B·(Dk+1)·Dm；
系数只依赖 k 时无关系。N 的关系：(A-2)(B-1)D(D+1)/2（L_N=1-X-XY-(q-1)X^3(1+Y)^2）。
"""
import time
import numpy as np
from common import *  # noqa

t0 = time.time()
P = 2147483647
KM = 40
TU = core.U_fast_table(KM, KM)
NT = N_table_from_U(TU, KM)

def rank_mod(Mat):
    A = np.array(Mat, dtype=np.int64) % P
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0:
            continue
        piv = r + nz[0]
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        col = A[:, c].copy()
        col[r] = 0
        nzr = np.nonzero(col)[0]
        if nzr.size:
            # A[i] -= col[i]*A[r]，分块避免溢出：col<P, A[r]<P，乘积 < 2^62
            A[nzr] = (A[nzr] - (col[nzr, None] * A[r][None, :]) % P) % P
        r += 1
    return r

def nullity_U(A, B, monos, val):
    unknowns = [(a, b, i, j) for a in range(A + 1) for b in range(B + 1) for (i, j) in monos]
    rows = []
    for k in range(A, KM + 1):
        for m in range(B, KM + 1):
            rows.append([pow(k, i, P) * pow(m, j, P) % P * (val(k - a, m - b) % P) % P for (a, b, i, j) in unknowns])
    return len(unknowns) - rank_mod(rows), len(unknowns), len(rows)

def Uv(k, m):
    return TU[k][m]
def Nv(k, q):
    return NT[k][q] if 0 <= q <= KM else 0

res = []
ok = True
# 总次数 <= D
for (A, B, D) in [(3, 1, 1), (4, 1, 2), (4, 2, 2), (5, 2, 2), (5, 3, 2), (6, 2, 3), (4, 3, 3), (6, 3, 2)]:
    monos = [(i, j) for i in range(D + 1) for j in range(D + 1 - i)]
    nl, nu, nr = nullity_U(A, B, monos, Uv)
    want = (A - 2) * B * D * (D + 1) // 2
    res.append('U(A=%d,B=%d,D=%d): %d/%d' % (A, B, D, nl, want))
    if nl != want:
        ok = False
# 分次
for (A, B, Dk, Dm) in [(5, 2, 1, 2), (4, 2, 2, 1), (5, 1, 0, 3)]:
    monos = [(i, j) for i in range(Dk + 1) for j in range(Dm + 1)]
    nl, nu, nr = nullity_U(A, B, monos, Uv)
    want = (A - 2) * B * (Dk + 1) * Dm
    res.append('U分次(A=%d,B=%d,Dk=%d,Dm=%d): %d/%d' % (A, B, Dk, Dm, nl, want))
    if nl != want:
        ok = False
report(ok, 'T3.8.dim-U', '关系空间维数 = (A-2)B·D(D+1)/2（分次 (A-2)B(Dk+1)Dm）：' + '; '.join(res))
# 只依赖 k
res = []
ok = True
for (A, B, D) in [(6, 6, 6), (10, 3, 6), (3, 10, 6), (4, 4, 12), (15, 1, 8), (1, 15, 8)]:
    monos = [(i, 0) for i in range(D + 1)]
    nl, nu, nr = nullity_U(A, B, monos, Uv)
    res.append('(%d,%d,%d):%d' % (A, B, D, nl))
    if nl != 0:
        ok = False
report(ok, 'T3.8.k-only', '系数只依赖 k 时无关系（核维数）：' + ', '.join(res))
# N
res = []
ok = True
for (A, B, D) in [(3, 2, 1), (4, 2, 2), (4, 3, 2), (5, 3, 2), (5, 4, 2), (6, 3, 3)]:
    monos = [(i, j) for i in range(D + 1) for j in range(D + 1 - i)]
    nl, nu, nr = nullity_U(A, B, monos, Nv)
    want = (A - 2) * (B - 1) * D * (D + 1) // 2
    res.append('N(A=%d,B=%d,D=%d): %d/%d' % (A, B, D, nl, want))
    if nl != want:
        ok = False
report(ok, 'T3.8.dim-N', 'N 的关系空间维数 = (A-2)(B-1)D(D+1)/2：' + '; '.join(res))

summary('audit_c3b')
print('elapsed %.1fs' % (time.time() - t0))
