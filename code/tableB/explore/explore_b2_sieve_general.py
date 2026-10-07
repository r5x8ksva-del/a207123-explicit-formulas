# -*- coding: utf-8 -*-
"""表 B 的 B2 探索（推广）：纤维 i 上 eta 为 b_i = 1 - x - i x^3 的根，K_i=Q(eta)。
留数元（去掉有理常数与 eta^{-3m-3}）：U 部分为 Wt_i(eta)，E 部分为 Wt_i(eta) - 1，
Wt_i(x) = 1 + sum_{j=1}^{i} j * i^(j) * x^(3j+2)（i^(j) 为下降阶乘）。
条件 (Fi)：1, eta^b, Wt eta^n 在 Q 上线性相关（同一个 (n,b) 对所有纤维）。
用法：explore_b2_sieve_general.py U|E T PLIM fibers(如 1,2 或 1,2,3)
"""
import sys
import numpy as np
sys.path.insert(0, __file__.rsplit('explore', 1)[0] + 'explore')
from explore_b2_periods import order_of_x, primes_upto, disc_cubic  # noqa: E402
from explore_b2_sieve import red_consts, mulmod, powmod  # noqa: E402


def falling(i, j):
    r = 1
    for t in range(j):
        r *= (i - t)
    return r


def elem_mod(kind, i, c, mod):
    """返回 Wt_i 或 Wt_i - 1 在 (Z/mod)[x]/f_i 中的坐标。"""
    acc = [1, 0, 0] if kind == 'U' else [0, 0, 0]
    x = [0, 1, 0]
    for j in range(1, i + 1):
        v = powmod(x, 3 * j + 2, c, mod)
        cf = j * falling(i, j)
        acc = [(acc[t] + cf * v[t]) % mod for t in range(3)]
    return acc


def main():
    kind = sys.argv[1]
    T = int(sys.argv[2])
    PLIM = int(sys.argv[3])
    fibers = [int(s) for s in sys.argv[4].split(',')]
    primes = {}
    for i in fibers:
        f = (i, 0, 1, -1)
        D = disc_cubic(*f)
        primes[i] = []
        for p in primes_upto(PLIM):
            if p == 2 or D % p == 0 or i % p == 0:
                continue
            c = red_consts(f, p)
            if powmod([0, 1, 0], T, c, p) != [1, 0, 0]:
                continue
            primes[i].append((p, order_of_x(f, p)))
        print('fiber', i, 'primes (l, period):', primes[i])
    tabs, mus = {}, {}
    for i in fibers:
        f = (i, 0, 1, -1)
        for (l, P) in primes[i]:
            c = red_consts(f, l)
            W = elem_mod(kind, i, c, l)
            beta = np.zeros((P, 2), dtype=np.int64)
            gamma = np.zeros((P, 2), dtype=np.int64)
            cur, curW = [1, 0, 0], W[:]
            for e in range(P):
                beta[e] = (cur[1], cur[2])
                gamma[e] = (curW[1], curW[2])
                cur = mulmod(cur, [0, 1, 0], c, l)
                curW = mulmod(curW, [0, 1, 0], c, l)
            assert cur == [1, 0, 0]
            tabs[(i, l)] = (P, beta, gamma)
            L2 = l * l
            c2 = red_consts(f, L2)
            y = powmod([0, 1, 0], P, c2, L2)
            assert y[0] % l == 1 and y[1] % l == 0 and y[2] % l == 0
            mus[(i, l)] = ((y[1] // l) % l, (y[2] // l) % l)
    n_idx = np.arange(T)
    survivors = []
    for b0 in range(T):
        alive = np.ones(T, dtype=bool)
        for i in fibers:
            for (l, P) in primes[i]:
                _, beta, gamma = tabs[(i, l)]
                bb = beta[b0 % P]
                g = gamma[n_idx % P]
                alive &= ((bb[0] * g[:, 1] - bb[1] * g[:, 0]) % l == 0)
                if not alive.any():
                    break
            if not alive.any():
                break
        survivors.extend((int(n0), b0) for n0 in np.nonzero(alive)[0])
    nz = [s for s in survivors if s[1] != 0]
    print('survivors:', len(survivors), ' with b0 != 0:', len(nz), nz[:40])
    unresolved = []
    for (n0, b0) in survivors:
        ok = False
        for i in fibers:
            for (l, P) in primes[i]:
                if b0 % P:
                    continue
                m1, m2 = mus[(i, l)]
                gg = tabs[(i, l)][2][n0 % P]
                if (m1 * gg[1] - m2 * gg[0]) % l:
                    ok = True
                    break
            if ok:
                break
        if not ok:
            unresolved.append((n0, b0))
    print('unresolved:', len(unresolved), unresolved[:60])


if __name__ == '__main__':
    main()
