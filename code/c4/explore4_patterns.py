# -*- coding: utf-8 -*-
"""探索 4：「全特殊值模式」计数 M(d; sigma, beta) 与展开 D(k,d) = sum M * C+(q-beta, sigma-beta)。

模式 = 合法满射词（值域 {1..sigma}），块分解里每个值都「特殊」：
  值 x 平凡 :<=> x 恰出现一次且这次出现是一个 S 块 [x]（不是 T/E 块的层，也不是任何块的 a 值）。
beta = E 块的层值（模式里即它的秩）；无 E 块时 beta = 0。
DP：从大到小处理值 x=sigma..1，状态 (p 待分配 a 值的块数, e 已用超额, closed 是否已放 E, beta)。
"""
from math import comb
from collections import defaultdict
from c4lib import *


def pattern_counts(d):
    """返回 dict (sigma, beta) -> M(d; sigma, beta)。"""
    res = defaultdict(int)
    if d == 0:
        res[(0, 0)] += 1          # 空模式
    for sigma in range(1, 2 * d + 3):
        st = defaultdict(int)
        st[(0, 0, 0, 0)] = 1
        for x in range(sigma, 0, -1):
            new = defaultdict(int)
            for (p, e, closed, beta), w in st.items():
                room = d - e
                for j in range(0, p + 1):
                    wj = w * comb(p, j)
                    if closed:
                        opts = [(0, 0, 0)]
                    else:
                        opts = []
                        for t in range(0, room + 2):
                            for s in range(0, room + 2):
                                for E in (0, 1):
                                    opts.append((s, t, E))
                    for (s, t, E) in opts:
                        mu = s + 2 * t + E + j
                        if mu < 1:
                            continue
                        if s == 1 and t == 0 and E == 0 and j == 0:
                            continue          # 平凡值，不允许出现在模式里
                        e2 = e + mu - 1
                        if e2 > d:
                            continue
                        p2 = p - j + t + E
                        c2 = 1 if (closed or E) else 0
                        b2 = x if E else beta
                        new[(p2, e2, c2, b2)] += wj * comb(s + t, s)
            st = new
        for (p, e, closed, beta), w in st.items():
            if p == 0 and e == d:
                res[(sigma, beta)] += w
    return dict(res)


def Cplus(n, r):
    if n < 0 or r < 0 or r > n:
        return 0
    return comb(n, r)


if __name__ == '__main__':
    KD = 60
    ND, _ = N_table_dp(KD)
    for d in range(0, 7):
        M = pattern_counts(d)
        ok = True
        for k in range(0, KD + 1):
            q = k - d
            if q < 0:
                continue
            val = sum(w * Cplus(q - b, s - b) for (s, b), w in M.items())
            if val != Dval(ND, k, d) and not (k == 0 and d == 0 and val == 1):
                ok = False
                print('  mismatch d=%d k=%d: pattern=%d D=%d' % (d, k, val, Dval(ND, k, d)))
        tot = sum(M.values())
        print('d=%d  #patterns=%d  check vs DP (k<=%d): %s' % (d, tot, KD, ok))
        sig = sorted(set(s for s, b in M))
        bet = sorted(set(b for s, b in M))
        print('   beta values:', bet, ' sigma range:', sig[0], '..', sig[-1])
        for b in bet:
            row = [M.get((s, b), 0) for s in range(0, 2 * d + 3)]
            print('   beta=%d: M(sigma=0..%d) =' % (b, 2 * d + 2), row)
