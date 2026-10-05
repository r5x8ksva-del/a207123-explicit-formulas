# -*- coding: utf-8 -*-
"""探索 9：按定义暴力枚举「全特殊」模式（合法满射词 + 块分解 + 平凡值判定），与模式 DP 对照。"""
import time
from collections import defaultdict
from c4lib import *
from explore4_patterns import pattern_counts


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def decompose(w):
    """块分解：反复取后缀最大值 M；后缀首位==M -> S；长度2 -> E；否则 T（此时 w[i+1]==w[i+2]==M）。"""
    blocks = []
    i = 0
    n = len(w)
    while i < n:
        M = max(w[i:])
        if w[i] == M:
            blocks.append(('S', M, None)); i += 1
        elif n - i == 2:
            assert w[i + 1] == M
            blocks.append(('E', M, w[i])); i += 2
        else:
            assert w[i + 1] == M and w[i + 2] == M, w
            blocks.append(('T', M, w[i])); i += 3
    return blocks


def brute_patterns(d):
    res = defaultdict(int)
    for sigma in range(1, 2 * d + 3):
        L = sigma + d
        seq = []
        used = [0] * (sigma + 1)

        def dfs():
            missing = sum(1 for v in range(1, sigma + 1) if used[v] == 0)
            if missing > L - len(seq):
                return
            if len(seq) == L:
                bl = decompose(seq)
                mu = defaultdict(int)
                for x in seq:
                    mu[x] += 1
                plain = set()
                for t, v, a in bl:
                    if t == 'S' and mu[v] == 1:
                        plain.add(v)
                # a 值出现在 mu 里；若 S 块的值又是某个 a，则 mu>=2，不会被判平凡
                if plain:
                    return
                beta = 0
                if bl and bl[-1][0] == 'E':
                    beta = bl[-1][1]
                res[(sigma, beta)] += 1
                return
            for v in range(1, sigma + 1):
                if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                    continue
                seq.append(v); used[v] += 1
                dfs()
                seq.pop(); used[v] -= 1
        dfs()
    if d == 0:
        res[(0, 0)] += 1
    return dict(res)


if __name__ == "__main__":
  for d in range(0, 4):
    t0 = time.time()
    B = brute_patterns(d)
    P = pattern_counts(d)
    print('d=%d brute==DP: %s  (#=%d, %.1fs)' % (d, B == P, sum(B.values()), time.time() - t0))
