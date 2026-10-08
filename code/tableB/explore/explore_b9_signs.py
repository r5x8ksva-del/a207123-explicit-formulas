# -*- coding: utf-8 -*-
"""B9 探索：h_k 的系数符号串、固定位置转正门槛 tau_i、初始正段长度、零系数、h_k(-1)。
h_k 由 T1.7 的递推 h_k = h_{k-1} + t(1-t)[(1-t)h'_{k-3} + (k-2)h_{k-3}]（初值 1, 1, 1+t）计算，
k<=40 与 U 的 DP 经 h_{k,i}=sum_j (-1)^{i-j}C(k+1,i-j)U_k(j) 核对。"""
import sys
from math import comb, lgamma, log, pi, atan2, hypot
sys.path.insert(0, __file__.rsplit('code', 1)[0] + 'code')
from core import U_fast_table  # noqa: E402


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def h_table(K):
    H = [[1], [1], [1, 1]]
    for k in range(3, K + 1):
        g = H[k - 3]
        d = [i * g[i] for i in range(1, len(g))]          # h'_{k-3}
        a = padd(d, [-x for x in ([0] + d)])                # (1-t)h'
        a = padd(a, [(k - 2) * x for x in g])               # + (k-2)h
        b = padd([0] + a, [-x for x in ([0, 0] + a)])       # t(1-t)[...]
        h = padd(H[k - 1], b)
        while len(h) > 1 and h[-1] == 0:
            h.pop()
        H.append(h)
    return H


def check(H, K=40):
    T = U_fast_table(K, K + 1)
    for k in range(0, K + 1):
        for i in range(len(H[k]) + 2):
            v = sum((-1) ** (i - j) * comb(k + 1, i - j) * T[k][j] for j in range(0, i + 1))
            hv = H[k][i] if i < len(H[k]) else 0
            assert v == hv, (k, i, v, hv)


if __name__ == '__main__':
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    H = h_table(K)
    check(H, 40)
    print('check vs DP k<=40 ok')
    # 零系数
    zeros = [(k, i) for k in range(K + 1) for i in range(len(H[k])) if H[k][i] == 0]
    print('zero coefficients (k,i):', zeros[:20], 'count', len(zeros))
    # 符号串
    for k in [30, 60, 90, 120, 150, 210, 300]:
        if k <= K:
            s = ''.join('+' if c > 0 else ('-' if c < 0 else '0') for c in H[k])
            print('k=%d deg=%d changes=%d floor(k/3)=%d' % (k, len(H[k]) - 1,
                  sum(1 for i in range(len(s) - 1) if s[i] != s[i + 1]), k // 3))
            print('   ', s)
    # 门槛 tau_i：最小的 K0 使 k>=K0 (<=K) 时 h_{k,i}>0
    taus = []
    for i in range(1, 60):
        last_bad = None
        for k in range(0, K + 1):
            v = H[k][i] if i < len(H[k]) else 0
            if v <= 0:
                last_bad = k
        if last_bad is None or last_bad >= K - 5:
            break
        taus.append(last_bad + 1)
    print('tau_i (i=1..):', taus)
    print('diffs:', [taus[i + 1] - taus[i] for i in range(len(taus) - 1)])
    # 初始正段长度
    runs = []
    for k in range(0, K + 1, 30):
        h = H[k]
        r = 0
        while r < len(h) and h[r] > 0:
            r += 1
        runs.append((k, r))
    print('initial positive run (k, length):', runs)
    # h_k(-1)
    hm1 = [sum(c * (-1) ** i for i, c in enumerate(h)) for h in H]
    print('h_k(-1), k<=25:', hm1[:26])
    w0 = complex(-2, pi)
    print('|w0|=%.6f arg=%.6f' % (abs(w0), atan2(w0.imag, w0.real)))
    for k in range(30, K + 1, 30):
        v = hm1[k]
        if v != 0:
            # log|h_k(-1)| - log Gamma(k/3+1) - (k+1)log2 , 再除以 k
            r = (log(abs(v)) - lgamma(k / 3 + 1) - (k + 1) * log(2)) / k
            print('k=%d  (log|h|-lgamma(k/3+1)-(k+1)log2)/k = %.5f   -log|w0|/3 = %.5f' % (k, r, -log(abs(w0)) / 3))
