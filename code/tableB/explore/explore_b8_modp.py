# -*- coding: utf-8 -*-
"""B8 探索：U_k(-j) 模小素数。统计三角 1<=k<=3j-3（j<=J）里，对素数集 S 全部整除的格点。"""
import sys
sys.path.insert(0, __file__.rsplit('explore', 1)[0] + 'explore')
from explore_b8_negzeros import Gneg_table  # noqa: E402


def vp(n, p):
    if n == 0:
        return 99
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c


if __name__ == '__main__':
    J = int(sys.argv[1]) if len(sys.argv) > 1 else 80
    G = Gneg_table(J)
    pts = [(k, j) for j in range(2, J + 1) for k in range(0, 3 * j - 2)]
    print('lattice points:', len(pts))
    primes = [2, 3, 5, 7, 11, 13]
    for t in range(1, len(primes) + 1):
        S = primes[:t]
        bad = [(k, j) for (k, j) in pts if all(G[j][k] % p == 0 for p in S)]
        print('S=%s: points divisible by all: %d; first few: %s' % (S, len(bad), bad[:8]))
    # 只看奇数：U_k(-j) 为奇数的比例
    odd = sum(1 for (k, j) in pts if G[j][k] % 2)
    print('odd fraction %.3f' % (odd / len(pts)))
    # 每个 j 的列：v_2 的最小值
    for j in [10, 20, 40, 64, 80]:
        if j <= J:
            v2 = [vp(G[j][k], 2) for k in range(3 * j - 2)]
            v3 = [vp(G[j][k], 3) for k in range(3 * j - 2)]
            print('j=%d v2=%s' % (j, ''.join(str(min(x, 9)) for x in v2)))
            print('j=%d v3=%s' % (j, ''.join(str(min(x, 9)) for x in v3)))
