# -*- coding: utf-8 -*-
"""表 B 的 B2 探索：模素数筛法 + l 进导数检验，排除纤维条件 (F1)∧(F2)（U 部分）的一切 b≠0 的解。

记号（与 explore_b2_fibers.py 相同）：K_i=Q(eta_i)，eta_1 = xi（x^3+x-1 的根），eta_2（2x^3+x-1 的根）。
条件 (Fi)：1, eta^b, What_i(eta) eta^n 在 Q 上线性相关 ⇔ D_i(n,b) := pi(eta^b) ∧ pi(What_i eta^n) = 0，
pi = 基 (1,eta,eta^2) 下后两个坐标，∧ 为 2x2 行列式。
筛法：对素数 l（周期 P = eta 模 l 的阶，P | T），D_i(n,b) ≡ 0 (mod l) 只依赖 (n mod P, b mod P)。
l 进导数检验：若 P | b、b≠0，令 eta^P = 1 + l*mu，则 D_i(n,b)/(b' l) ≡ E(n) := pi(mu) ∧ pi(What_i eta^n) (mod l)
（b = P b'，l>=3），所以 E(n) ≢ 0 (mod l) 时 D_i(n,b) ≠ 0。
只做探索；正式核对另写。
"""
import sys
import numpy as np
sys.path.insert(0, __file__.rsplit('explore', 1)[0] + 'explore')
from explore_b2_periods import order_of_x  # noqa: E402

FIELDS = {
    1: {'f': (1, 0, 1, -1), 'W': ((1, 1), (-1, 1), (1, 1))},              # What_1 = 1 - x + x^2
    2: {'f': (2, 0, 1, -1), 'W': ((3, 4), (-5, 4), (2, 1))},              # What_2 = 3/4 - 5/4 x + 2 x^2
}


def red_consts(f, mod):
    a3, a2, a1, a0 = f
    inv = pow(a3, -1, mod)
    return ((-a0 * inv) % mod, (-a1 * inv) % mod, (-a2 * inv) % mod)


def mulmod(a, b, c, mod):
    c0, c1, c2 = c
    r = [0] * 5
    for i in range(3):
        if a[i]:
            for j in range(3):
                r[i + j] += a[i] * b[j]
    for d in (4, 3):
        v = r[d] % mod
        if v:
            r[d - 3] += v * c0
            r[d - 2] += v * c1
            r[d - 1] += v * c2
    return [r[0] % mod, r[1] % mod, r[2] % mod]


def powmod(a, e, c, mod):
    res = [1, 0, 0]
    base = a[:]
    while e:
        if e & 1:
            res = mulmod(res, base, c, mod)
        base = mulmod(base, base, c, mod)
        e >>= 1
    return res


def W_mod(field, mod):
    return [(num * pow(den, -1, mod)) % mod for (num, den) in FIELDS[field]['W']]


def tables(field, l, P):
    """返回 beta[b]=pi(eta^b) mod l，gamma[n]=pi(W eta^n) mod l，b,n in [0,P)。"""
    c = red_consts(FIELDS[field]['f'], l)
    x = [0, 1, 0]
    W = W_mod(field, l)
    beta = np.zeros((P, 2), dtype=np.int64)
    gamma = np.zeros((P, 2), dtype=np.int64)
    cur = [1, 0, 0]
    curW = W[:]
    for e in range(P):
        beta[e] = (cur[1], cur[2])
        gamma[e] = (curW[1], curW[2])
        cur = mulmod(cur, x, c, l)
        curW = mulmod(curW, x, c, l)
    assert cur == [1, 0, 0], (field, l, P)
    return beta, gamma


def mu_mod(field, l, P):
    """eta^P = 1 + l*mu（在 Z_l[eta] 中），返回 pi(mu) mod l。"""
    L2 = l * l
    c = red_consts(FIELDS[field]['f'], L2)
    y = powmod([0, 1, 0], P, c, L2)
    assert y[0] % l == 1 and y[1] % l == 0 and y[2] % l == 0
    return ((y[1] // l) % l, (y[2] // l) % l)


def main():
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 5040
    PLIM = int(sys.argv[2]) if len(sys.argv) > 2 else 30000
    from explore_b2_periods import primes_upto, disc_cubic
    primes = {1: [], 2: []}
    for fi in (1, 2):
        f = FIELDS[fi]['f']
        D = disc_cubic(*f)
        for p in primes_upto(PLIM):
            if p == 2 or D % p == 0 or f[0] % p == 0:
                continue
            # 快速排除：阶必须整除 T，即 x^T == 1
            c = red_consts(f, p)
            if powmod([0, 1, 0], T, c, p) != [1, 0, 0]:
                continue
            P = order_of_x(f, p)
            primes[fi].append((p, P))
    print('T =', T)
    print('field-1 primes (l, period):', primes[1])
    print('field-2 primes (l, period):', primes[2])
    # 预算每个素数的 (beta, gamma)
    tabs = {}
    for fi in (1, 2):
        for (l, P) in primes[fi]:
            tabs[(fi, l)] = (P,) + tables(fi, l, P)
    survivors = []
    n_idx = np.arange(T)
    for b0 in range(T):
        alive = np.ones(T, dtype=bool)
        for fi in (1, 2):
            for (l, P) in primes[fi]:
                Pp, beta, gamma = tabs[(fi, l)]
                bb = beta[b0 % P]
                g = gamma[n_idx % P]
                Dv = (bb[0] * g[:, 1] - bb[1] * g[:, 0]) % l
                alive &= (Dv == 0)
                if not alive.any():
                    break
            if not alive.any():
                break
        for n0 in np.nonzero(alive)[0]:
            survivors.append((int(n0), b0))
    print('survivors after sieve:', len(survivors))
    nz = [s for s in survivors if s[1] != 0]
    print('  with b0 != 0 mod T:', len(nz), nz[:40])
    # l 进导数检验
    mus = {}
    for fi in (1, 2):
        for (l, P) in primes[fi]:
            mus[(fi, l)] = mu_mod(fi, l, P)
    unresolved = []
    for (n0, b0) in survivors:
        ok = False
        g0 = b0 % T
        for fi in (1, 2):
            for (l, P) in primes[fi]:
                if g0 % P != 0:
                    continue
                m1, m2 = mus[(fi, l)]
                Pp, beta, gamma = tabs[(fi, l)]
                gg = gamma[n0 % P]
                E = (m1 * gg[1] - m2 * gg[0]) % l
                if E != 0:
                    ok = True
                    break
            if ok:
                break
        if not ok:
            unresolved.append((n0, b0))
    print('unresolved after l-adic step:', len(unresolved), unresolved[:60])


if __name__ == '__main__':
    main()
