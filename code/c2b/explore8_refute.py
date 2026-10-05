# -*- coding: utf-8 -*-
"""探索 8：对每个「有信息」参数族（gamma+eps>=2），找出能反驳它的最小 m（或 q），统计分布。
若全部族都能被 m<=4 反驳，check 模块只需计算 m<=4 的形状即可完整复现「盒内无存活族」。"""
import sys, os, time
from math import comb
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import core
from formulas import refined_dp
from search import test_shape

K, MM = 30, 12
t0 = time.time()
T = core.U_fast_table(K, MM)
E = {}; U = {}; A = {}
for m in range(0, MM + 1):
    tot, asc = refined_dp(K, m)
    U[m] = [T[k][m] for k in range(K + 1)]
    E[m] = [sum(asc[k]) for k in range(K + 1)]
    A[m] = [U[m][k] - E[m][k] for k in range(K + 1)]

def ie(tab, k, q, base):
    return sum((-1) ** (q - i) * comb(q, i) * ((base if k == 0 else 0) if i == 0 else tab[i - 1][k]) for i in range(q + 1))

N = {q: [ie(U, k, q, 1) for k in range(K + 1)] for q in range(1, MM + 1)}
Nc = {q: [ie(A, k, q, 1) for k in range(K + 1)] for q in range(1, MM + 1)}
NE = {q: [ie(E, k, q, 0) for k in range(K + 1)] for q in range(1, MM + 1)}

ALPHA = range(-1, 3); BETA = range(-3, 4); GAMMA = range(0, 4)
DELTA = range(0, 3); EPS = range(-1, 4); ZETA = range(-3, 4)

for target, name in [(A, 'A'), (E, 'E'), (U, 'U'), (N, 'N'), (Nc, 'Nc'), (NE, 'NE')]:
    t1 = time.time()
    cache = {}
    dist = Counter()
    survivors = []
    for a in ALPHA:
        for b in BETA:
            for g in GAMMA:
                for dl in DELTA:
                    for e in EPS:
                        if g + e < 2:
                            continue
                        for z in ZETA:
                            ref = None
                            for m in range(1, MM + 1):
                                key = (m, a * m + b, g, dl * m + z, e)
                                if key not in cache:
                                    cache[key] = test_shape(target[m], a * m + b, g, dl * m + z, e)[0]
                                if not cache[key]:
                                    ref = m
                                    break
                            if ref is None:
                                survivors.append((a, b, g, dl, e, z))
                            else:
                                dist[ref] += 1
    print('%-3s informative families: refuted-at-m distribution %s, survivors %s (%.1fs)'
          % (name, dict(sorted(dist.items())), survivors, time.time() - t1))
print('total %.1fs' % (time.time() - t0))
