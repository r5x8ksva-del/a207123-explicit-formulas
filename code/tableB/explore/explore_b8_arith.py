# -*- coding: utf-8 -*-
"""B8 探索：U_k(-j) 的算术结构（因子、模小素数），重点看根离整数很近的 (k,j)。"""
import sys
from math import gcd, factorial
sys.path.insert(0, __file__.rsplit('code', 1)[0] + 'code')
sys.path.insert(0, __file__.rsplit('explore', 1)[0] + 'explore')
from explore_b8_negzeros import Gneg_table  # noqa: E402


def small_factor(n, B=10**5):
    n = abs(n)
    f = {}
    p = 2
    while p <= B and n > 1:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1 if p == 2 else 2
    return f, n


if __name__ == '__main__':
    J = int(sys.argv[1]) if len(sys.argv) > 1 else 70
    G = Gneg_table(J)
    for (k, j) in [(30, 60), (30, 61), (30, 59), (10, 9), (10, 10), (17, 4), (14, 3), (25, 33), (20, 16)]:
        if j > J:
            continue
        g = G[j]
        v = g[k] if k < len(g) else 0
        f, rest = small_factor(v)
        print('U_%d(-%d) = %d  (digits %d)  small factors %s  cofactor digits %d' % (k, j, v, len(str(abs(v))), f, len(str(rest))))
