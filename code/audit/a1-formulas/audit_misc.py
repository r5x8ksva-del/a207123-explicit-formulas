# -*- coding: utf-8 -*-
"""审计 a1-formulas：杂项——T1.4(3) 合法排列的形状；④.6 相邻 h_k 根不交错（numpy 数值，仅 INFO）。"""
from itertools import permutations
import numpy as np
from common import *  # noqa
ok = True
for k in range(1, 9):
    legal = [p for p in permutations(range(1, k + 1)) if all(good(p[i], p[i + 1], p[i + 2]) for i in range(k - 2))]
    shape = [p for p in permutations(range(1, k + 1)) if all(p[i] > p[i + 1] for i in range(k - 2)) and p[-1] in (1, 2)] if k >= 2 else [(1,)]
    if sorted(legal) != sorted(shape):
        ok = False
report(ok, 'T1.4.3-perm', '合法排列恰为 w_1>…>w_{k-1} 且 w_k∈{1,2}（k<=8，暴力）')
TH = lemma1_table(37, 38)
def hp(k):
    return trim([sum((-1) ** (i - j) * comb(k + 1, i - j) * TH[k][j] for j in range(0, i + 1)) for i in range(0, k + 1)])
inter = []
for k in range(2, 36):
    a = np.sort(np.roots([float(c) for c in reversed(hp(k))]).real)
    b = np.sort(np.roots([float(c) for c in reversed(hp(k + 1))]).real)
    merged = sorted([(v, 0) for v in a] + [(v, 1) for v in b])
    labels = [l for _, l in merged]
    alt = all(labels[i] != labels[i + 1] for i in range(len(labels) - 1))
    inter.append((k, alt))
print('INFO 相邻 h_k,h_{k+1} 根是否交错（numpy 数值）:', [k for k, a_ in inter if a_])
report(not any(a_ for _, a_ in inter), 'T5.3.6-nointerlace-num', '数值上 k=2..35 相邻 h_k 根均不交错（numpy，非严格）')
summary('audit_misc')
