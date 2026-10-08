# -*- coding: utf-8 -*-
"""B5 探索：N(k,q)、N^c、N^E、骨架数 R(p,s) 的表（只依赖 core 的原始定义）。"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from core import U_fast_table, binom, stirling2_table
from collections import defaultdict


def legal_words(k, vals):
    """长度 k、取值在 vals（有序整数列表）的合法词（DFS）。"""
    out = []
    seq = []
    def dfs():
        if len(seq) == k:
            out.append(tuple(seq)); return
        for v in vals:
            if len(seq) >= 2:
                a, b = seq[-2], seq[-1]
                if not (b == v or (a >= b and a >= v)):
                    continue
            seq.append(v); dfs(); seq.pop()
    dfs()
    return out


def N_split_brute(k):
    """返回 dict q -> (N, Nc, NE)，按定义枚举（值域恰为 {1..q}）。"""
    res = defaultdict(lambda: [0, 0, 0])
    for w in legal_words(k, list(range(1, k + 1))):
        s = set(w); q = len(s)
        if s != set(range(1, q + 1)):
            continue
        ends_asc = k >= 2 and w[-2] < w[-1]
        res[q][0] += 1
        res[q][2 if ends_asc else 1] += 1
    return {q: tuple(v) for q, v in res.items()}


if __name__ == '__main__':
    S = stirling2_table(40)
    def R(p, s):
        tot = 0
        for i in range(p + 1):
            if i == 0:
                val = 1 if s == 0 else 0
            else:
                val = S[i - 1 + s][i - 1]
            tot += (-1) ** (p - i) * binom(p, i) * val
        return tot
    print('R(p,s) rows s=0..7, p=0..2s')
    for s in range(8):
        print(s, [R(p, s) for p in range(0, 2 * s + 1)])
    for k in range(1, 9):
        d = N_split_brute(k)
        print('k=%d' % k, [d.get(q, (0, 0, 0)) for q in range(1, k + 1)])
