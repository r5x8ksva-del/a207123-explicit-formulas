# -*- coding: utf-8 -*-
"""表 B 的 B2 探索：对素数 l，求 xi（x^3+x-1 的根）与 eta（2x^3+x-1 的根）在 (F_l[x]/f)^x 中的阶，
挑出阶为光滑小数的素数，供筛法用。只做观察。"""
import sys


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def mulmod(a, b, c0, c1, c2, p):
    """a,b in F_p[x]/(x^3 - c2 x^2 - c1 x - c0)，长度 3。"""
    r = [0] * 5
    for i in range(3):
        ai = a[i]
        if ai:
            for j in range(3):
                r[i + j] += ai * b[j]
    for d in (4, 3):
        v = r[d] % p
        if v:
            r[d - 3] += v * c0
            r[d - 2] += v * c1
            r[d - 1] += v * c2
    return [r[0] % p, r[1] % p, r[2] % p]


def powmod(a, e, c, p):
    res = [1, 0, 0]
    base = a[:]
    while e:
        if e & 1:
            res = mulmod(res, base, *c, p)
        base = mulmod(base, base, *c, p)
        e >>= 1
    return res


def disc_cubic(a, b, c, d):
    return b * b * c * c - 4 * a * c ** 3 - 4 * b ** 3 * d - 27 * a * a * d * d + 18 * a * b * c * d


def order_of_x(field, p):
    """field: (a3,a2,a1,a0) 整系数 a3 x^3 + a2 x^2 + a1 x + a0。返回 x 的阶（p 不整除判别式与首项）。"""
    a3, a2, a1, a0 = field
    inv = pow(a3, p - 2, p)
    # x^3 = -(a2 x^2 + a1 x + a0)/a3
    c0, c1, c2 = (-a0 * inv) % p, (-a1 * inv) % p, (-a2 * inv) % p
    c = (c0, c1, c2)
    N = (p - 1) * (p + 1) * (p * p + p + 1)   # 群阶的公倍数：lcm(p-1, p^2-1, p^3-1) 的倍数
    x = [0, 1, 0]
    assert powmod(x, N, c, p) == [1, 0, 0]
    T = N
    for q in factor(N):
        while T % q == 0 and powmod(x, T // q, c, p) == [1, 0, 0]:
            T //= q
    return T


def main():
    LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    SMOOTH = int(sys.argv[2]) if len(sys.argv) > 2 else 13
    fields = {'F1': (1, 0, 1, -1), 'F2': (2, 0, 1, -1)}
    for name, f in fields.items():
        D = disc_cubic(*f)
        out = []
        for p in primes_upto(LIM):
            if p == 2 or D % p == 0 or f[0] % p == 0:
                continue
            T = order_of_x(f, p)
            fac = factor(T)
            if max(fac) <= SMOOTH:
                out.append((T, p))
        out.sort()
        print(name, 'disc', D, 'smooth-period primes:', len(out))
        print('  ', out[:120])


if __name__ == '__main__':
    main()
