# -*- coding: utf-8 -*-
"""s8：笔记 §4.9–§4.11 的附带数据复核 + h_k(-1) 递推的扩大搜索（模素数秩判定）。

模 p 判定的逻辑：若系数矩阵模 p 列满秩，则在 Q 上也列满秩（模 p 秩 <= Q 上秩），从而该形状下
确实不存在非零递推。若模 p 有零空间，才需要回到 Q 上确认。
"""
import sys, os, time, math
from math import comb, gcd, log
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rlib import U_rec_table, peval, trim

t0 = time.time()
K = 160
T = U_rec_table(K, K + 2)
H = {}
for k in range(K + 1):
    H[k] = trim([sum((-1) ** (i - j) * comb(k + 1, i - j) * T[k][j] for j in range(i + 1)) for i in range(k + 1)])


def signs(p):
    return ''.join('+' if c > 0 else '-' for c in p if c != 0)


claimed = {12: '+++--+--+', 30: '+++++--++-++-++-++--+', 60: '+++++++++--++-++-++--+--+--+--+--+--++--+'}
print('sign strings k=12,30,60 match notes:', all(signs(H[k]) == s for k, s in claimed.items()))
h2 = [peval(H[k], 2) for k in range(13)]
print('h_k(2), k<=12 matches notes:', h2 == [1, 1, 3, 1, -3, -19, -31, -17, 139, 481, 807, -589, -7029])
hm1 = {k: peval(H[k], -1) for k in range(K + 1)}
print('log|h_k(-1)|/k at k=20,30,40,50,60:', [round(log(abs(hm1[k])) / k, 3) for k in (20, 30, 40, 50, 60)],
      ' (notes: 0.737, 0.855, 0.968, 1.035, 1.082); at k=100,130,160:',
      [round(log(abs(hm1[k])) / k, 3) for k in (100, 130, 160)])


# k=60 根分布：Sturm 计数
def prim(p):
    p = trim(p)
    g = 0
    for c in p:
        g = gcd(g, c)
    return [c // g for c in p] if g > 1 else p


def prem_pos(A, B):
    A = list(A)
    db = len(B) - 1
    delta = len(A) - 1 - db
    lb = B[-1]
    A = [c * abs(lb) ** (delta + 1) for c in A]
    while len(A) - 1 >= db and A:
        q = A[-1] // lb
        sh = len(A) - 1 - db
        for i, b in enumerate(B):
            A[sh + i] -= q * b
        A = trim(A)
    return A


def sturm_seq(p):
    p = prim(p)
    seq = [p, prim(trim([i * p[i] for i in range(1, len(p))]))]
    while len(seq[-1]) > 1:
        r = prem_pos(seq[-2], seq[-1])
        if not r:
            break
        seq.append(prim([-c for c in r]))
    return seq


def var(vals):
    v = [x for x in vals if x != 0]
    return sum(1 for a, b in zip(v, v[1:]) if (a > 0) != (b > 0))


seq = sturm_seq(H[60])
Vm = var([s[-1] * ((-1) ** (len(s) - 1)) for s in seq])
Vp = var([s[-1] for s in seq])
V = lambda x: var([peval(s, x) for s in seq])
print('k=60: negative roots=%d, in (-1,0)=%d, roots>1=%d, deg=%d'
      % (Vm - V(0), V(-1) - V(0), V(1) - Vp, len(H[60]) - 1))

# h_k(-1) 递推搜索（模 p）
P = (1 << 61) - 1


def rank_mod(rows, ncols):
    A = [[x % P for x in r] for r in rows]
    rank = 0
    for c in range(ncols):
        piv = next((i for i in range(rank, len(A)) if A[i][c]), None)
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        inv = pow(A[rank][c], P - 2, P)
        A[rank] = [x * inv % P for x in A[rank]]
        for i in range(len(A)):
            if i != rank and A[i][c]:
                f = A[i][c]
                A[i] = [(x - f * y) % P for x, y in zip(A[i], A[rank])]
        rank += 1
    return rank


seqv = [hm1[k] for k in range(K + 1)]
found = []
tested = 0
for order in range(1, 13):
    for deg in range(0, 13):
        ncols = (order + 1) * (deg + 1)
        rows = [[(k ** d) * seqv[k - i] for i in range(order + 1) for d in range(deg + 1)] for k in range(order + 2, K + 1)]
        if len(rows) < ncols + 10:
            continue
        tested += 1
        if rank_mod(rows, ncols) < ncols:
            found.append((order, deg))
print('h_k(-1), k<=160: polynomial-coefficient recurrences with order<=12, degree<=12 (>=10 surplus equations), '
      'shapes tested=%d, shapes with a mod-p kernel: %s' % (tested, found if found else 'none'))
print('elapsed %.1fs' % (time.time() - t0))
