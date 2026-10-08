# -*- coding: utf-8 -*-
"""s12-b5 复核 r8：§5 骨架型搜索在「不截断 s」时的结论（补充分析，不是作者的断言）。

对作者的 1440 组参数 (a,b,c,d,e,f)，取 S = S_needed(K)：在 1<=q<=k<=K 的窗口内仍有非零项的最大 s，
于是截断方程组恰等价于「无穷族限制在窗口上」。模素数 P1（命中再用 P2 复核）判定 N^E、N 的相容性，
并统计「系数矩阵秩 = 方程数」（任何数据都相容、检验失效）的参数组数。
  r8-needed   S_needed(21)>7 的参数组数
  r8-proper   K=21、S=S_needed：N^E、N 相容的参数组数；检验失效（满行秩）的组数
  r8-K27      对 K=21 相容（或失效）的参数组，在 K=27（378 个方程）上重判
"""
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s12b5_common import report, summary, ie_tables  # noqa: E402

t0 = time.time()
KMAX = 27
IN, INc, INE = ie_tables(KMAX, KMAX)
P1, P2 = 2147483647, 2147483629
SHAPES = ((-2, 1), (-2, 0), (-1, 1), (-1, 0), (-3, 1), (-2, 2))
EFS = ((0, 0), (1, 0), (-1, 0), (0, 1), (1, 1), (0, -1))
NB = 200


def btable(P):
    T = np.zeros((NB + 1, NB + 1), dtype=np.int64)
    row = [1]
    for n in range(NB + 1):
        if n > 0:
            row = [1] + [(row[i - 1] + row[i]) % P for i in range(1, n)] + [1]
        T[n, :n + 1] = row
    return T


BT = {P1: btable(P1), P2: btable(P2)}


def binom_arr(Nn, Rr, P):
    valid = (Rr >= 0) & (Rr <= Nn) & (Nn >= 0)
    assert Nn.max() <= NB
    return np.where(valid, BT[P][np.clip(Nn, 0, NB), np.clip(Rr, 0, NB)], 0)


def pts(K):
    return [(k, q) for k in range(1, K + 1) for q in range(1, k + 1)]


def s_needed(a, b, c, d, e, f, K, smax=80):
    P = pts(K)
    ks = np.array([k for k, _ in P])
    qs = np.array([q for _, q in P])
    best = -1
    for s in range(smax + 1):
        p = np.arange(0, 2 * s + 3)
        n1 = qs[:, None] + e
        r1 = p[None, :] + f
        ok1 = (r1 >= 0) & (r1 <= n1)
        nn = ks[:, None] + a * s + b * p[None, :] + c
        rr = (s + qs + d)[:, None] + 0 * p[None, :]
        ok2 = (rr >= 0) & (rr <= nn)
        if np.any(ok1 & ok2):
            best = s
    return best


def build(a, b, c, d, e, f, K, S, P):
    Pt = pts(K)
    ks = np.array([k for k, _ in Pt])[:, None]
    qs = np.array([q for _, q in Pt])[:, None]
    vs = [(p, s) for s in range(S + 1) for p in range(2 * s + 3)]
    ps = np.array([p for p, _ in vs])[None, :]
    ss = np.array([s for _, s in vs])[None, :]
    B1 = binom_arr(qs + e + 0 * ps, ps + f + 0 * qs, P)
    B2 = binom_arr(ks + a * ss + b * ps + c, ss + qs + d, P)
    M = (B1 * B2) % P
    keep = np.any(M != 0, axis=0)
    return M[:, keep]


def rank_mod(A, P):
    A = A.copy() % P
    m, n = A.shape
    r = 0
    for c in range(n):
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
        idx = np.nonzero(col)[0]
        if idx.size:
            A[idx] = (A[idx] - (col[idx, None] * A[r][None, :]) % P) % P
        r += 1
        if r == m:
            break
    return r


def yvec(tab, K, P):
    return np.array([tab[k][q] % P for (k, q) in pts(K)], dtype=np.int64)[:, None]


def judge(params, K, P):
    a, b, c, d, e, f = params
    S = s_needed(a, b, c, d, e, f, K)
    M = build(a, b, c, d, e, f, K, S, P)
    neq = M.shape[0]
    if M.shape[1] == 0:
        rk = 0
    else:
        rk = rank_mod(M, P)
    out = {'S': S, 'unk': M.shape[1], 'rank': rk, 'neq': neq}
    for name, tab in (('NE', INE), ('N', IN)):
        y = yvec(tab, K, P)
        rk2 = rank_mod(np.hstack([M, y]), P) if M.shape[1] else (1 if np.any(y % P) else 0)
        out[name] = (rk2 == rk)
    return out


ALL = [(a, b, c, d, e, f) for (a, b) in SHAPES for c in range(-5, 3) for d in range(-3, 2) for (e, f) in EFS]
need = {pr: s_needed(*pr, 21) for pr in ALL}
over7 = sum(1 for v in need.values() if v > 7)
report(True, 'r8-needed', '（信息）1440 组参数中 S_needed(21)>7 的有 %d 组；S_needed 的最大值 %d' % (over7, max(need.values())))

hitsNE, hitsN, vacuous = [], [], []
for pr in ALL:
    if need[pr] <= 7:
        continue                      # 与作者的截断等价，r7 已重跑
    res = judge(pr, 21, P1)
    if res['rank'] == res['neq']:
        vacuous.append(pr)
    if res['NE']:
        hitsNE.append(pr)
    if res['N']:
        hitsN.append(pr)
print('  K=21 用时 %.0fs' % (time.time() - t0), flush=True)
report(True, 'r8-proper', '（信息）K=21、S=S_needed（%d 组 S_needed>7 的参数）：N^E 相容 %d 组，N 相容 %d 组，检验失效（满行秩）%d 组；例 %s'
       % (over7, len(hitsNE), len(hitsN), len(vacuous), (hitsNE + hitsN)[:4]))

recheck = sorted(set(hitsNE + hitsN))
still = []
for pr in recheck:
    res = judge(pr, KMAX, P1)
    if res['NE'] or res['N']:
        res2 = judge(pr, KMAX, P2)
        still.append((pr, res['NE'], res['N'], res2['NE'], res2['N'], res['rank'], res['neq']))
report(True, 'r8-K27', '（信息）K=21 相容的 %d 组在 K=27 上仍相容的：%s' % (len(recheck), still[:6]))

print('time %.1fs' % (time.time() - t0))
sys.exit(1 if summary('r8') else 0)
