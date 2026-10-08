# -*- coding: utf-8 -*-
"""B9 探索：h_k 扫到 k<=K（滚动保存三项），检查零系数、变号次数=floor(k/3)、初始正段、
末端符号，以及 h_k(-1) 的符号与大小（写到 logs/explore_b9_hm1.tsv）。"""
import sys
import time
from math import lgamma, log, pi, atan2


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def step(hk1, hk3, k):
    g = hk3
    d = [i * g[i] for i in range(1, len(g))]
    a = padd(d, [-x for x in ([0] + d)])
    a = padd(a, [(k - 2) * x for x in g])
    b = padd([0] + a, [-x for x in ([0, 0] + a)])
    h = padd(hk1, b)
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


if __name__ == '__main__':
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    out = open(sys.argv[2] if len(sys.argv) > 2 else 'logs/explore_b9_hm1.tsv', 'w', encoding='utf-8', newline='\n')
    out.write('k\tsign_h(-1)\tlog10|h(-1)|\tinitial_run\ttop6_signs\n')
    win = {0: [1], 1: [1], 2: [1, 1]}
    t0 = time.time()
    zeros = []
    badchg = []
    for k in range(0, K + 1):
        if k >= 3:
            win[k] = step(win[k - 1], win[k - 3], k)
            del win[k - 3]
        h = win[k]
        if any(c == 0 for c in h):
            zeros.append(k)
        sg = ['+' if c > 0 else '-' for c in h]
        chg = sum(1 for i in range(len(sg) - 1) if sg[i] != sg[i + 1])
        if chg != k // 3:
            badchg.append(k)
        run = 0
        while run < len(h) and h[run] > 0:
            run += 1
        v = sum(c if i % 2 == 0 else -c for i, c in enumerate(h))
        s = '+' if v > 0 else ('-' if v < 0 else '0')
        lg = (len(str(abs(v))) - 1 + log(int(str(abs(v))[:15]) / 10 ** (min(15, len(str(abs(v)))) - 1), 10)) if v else float('-inf')
        out.write('%d\t%s\t%.6f\t%d\t%s\n' % (k, s, lg, run, ''.join(sg[-6:])))
        if k % 200 == 0:
            print('k=%d deg=%d (%.1fs)' % (k, len(h) - 1, time.time() - t0), flush=True)
    out.close()
    print('zero coefficients at k:', zeros[:10], 'count', len(zeros))
    print('k with #sign changes != floor(k/3):', badchg[:10])
