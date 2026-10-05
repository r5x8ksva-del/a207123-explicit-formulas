# -*- coding: utf-8 -*-
"""探索 5：u 型单和的严格不存在性判据（留数 + 范数）。

命题：若对所有 k>=0 有 V(k) = sum_{s>=0} A_s C(k+c-2s, d+s)（A_s 有理，c,d 任意整数，组合约定的二项式），
则 V(x) = x^{d-c}(1-x)^{-d-1} F(u) - L(x)，F ∈ Q((u))，L ∈ x^{-1}Q[x^{-1}]，u = x^3/(1-x)。
于是 x^{c+2d+3}(V + L) ∈ Q((u))。Q((x)) = Q((u)) ⊕ xQ((u)) ⊕ x^2 Q((u))（X^3+uX-u 在 Q[[u]] 上 Eisenstein）。
V 的坐标是 u 的有理函数，在 u = 1/i 处至多一阶极点，留数向量对应 K_i = Q[x]/(x^3 + x/i - 1/i) 中的元素 ν_i；
L 的坐标是 u 的 Laurent 多项式，不能抵消极点；x^N 的坐标矩阵在 u=1/i 处正则。
故必须 x^N ν_i ∈ Q（常数），即 ν_i ∈ Q^* x^{-N}。K_i 为域（i ≠ q^2(q-1)）且 ν_i ≠ 0 时取范数：
N(ν_i) = c^3 · i^N（N(x) = 1/i）。所以若 N(ν_i) 去掉 i 的素因子后不是有理立方，则这样的 (c,d,A_s) 不存在。
"""
import sys, os
from fractions import Fraction
from math import gcd
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))


def make_field(i):
    ii = Fraction(i)

    def red(p):
        p = list(p) + [Fraction(0)] * max(0, 3 - len(p))
        p = [Fraction(a) for a in p]
        # x^3 = (1 - x)/i
        for d in range(len(p) - 1, 2, -1):
            c = p[d]
            if c:
                p[d] = Fraction(0)
                p[d - 3] += c / ii
                p[d - 2] -= c / ii
        return p[:3]

    def mul(a, b):
        r = [Fraction(0)] * 5
        for s in range(3):
            for t in range(3):
                r[s + t] += a[s] * b[t]
        return red(r)

    one = [Fraction(1), Fraction(0), Fraction(0)]
    X = [Fraction(0), Fraction(1), Fraction(0)]
    Xinv = [Fraction(1), Fraction(0), ii]          # x^{-1} = i x^2 + 1

    def xpow(n):
        base = X if n >= 0 else Xinv
        r = one
        for _ in range(abs(n)):
            r = mul(r, base)
        return r

    def norm(a):
        cols = [a, mul(a, X), mul(mul(a, X), X)]
        M = [[cols[c][r] for c in range(3)] for r in range(3)]
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
                - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))

    return red, mul, xpow, norm


def is_field(i):
    # i x^3 + x - 1 无有理根 ⇔ i ≠ q^2(q-1)
    q = 2
    while q * q * (q - 1) <= i:
        if q * q * (q - 1) == i:
            return False
        q += 1
    return True


def residue(i, m, which):
    """V 在 u=1/i 处的留数元 ν_i ∈ K_i。which ∈ {'U','E','A'}。
    G_m = sum_{j=0}^m c_j x^{2[j>=1]} (1-x)^{-(m-j+1)} prod_{i'=j}^m (1-i'u)^{-1}，c_0=1，c_j=j；
    E 部分取 j>=1，A 部分取 j=0。K_i 中 1-x = i x^3。"""
    red, mul, xpow, norm = make_field(i)
    tot = [Fraction(0)] * 3
    js = {'U': range(0, i + 1), 'E': range(1, i + 1), 'A': range(0, 1)}[which]
    for j in js:
        if j > i:
            continue
        cj = 1 if j == 0 else j
        e = 0 if j == 0 else 2
        n = m - j + 1
        coef = Fraction(cj) / Fraction(i) ** n
        for ip in range(j, m + 1):
            if ip != i:
                coef *= Fraction(i, i - ip)
        term = xpow(e - 3 * n)
        tot = [tot[r] + coef * term[r] for r in range(3)]
    return tot, norm(tot)


def strip_primes(n, ps):
    for p in ps:
        while n % p == 0:
            n //= p
    return n


def icbrt(n):
    if n < 0:
        return -icbrt(-n)
    lo, hi = 0, 1
    while hi ** 3 <= n:
        hi *= 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** 3 <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo


def is_cube(n):
    r = icbrt(n)
    return r ** 3 == n


def prime_factors_small(n):
    ps = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        ps.append(n)
    return ps


def obstruction(m, which):
    """返回 (True, i, N) 若找到阻碍；否则 (False, details)。"""
    details = []
    for i in range(m, 0, -1):
        if not is_field(i):
            details.append((i, 'not a field'))
            continue
        nu, N = residue(i, m, which)
        if N == 0:
            details.append((i, 'residue zero'))
            continue
        ps = prime_factors_small(i)
        num = strip_primes(abs(N.numerator), ps)
        den = strip_primes(N.denominator, ps)
        if not (is_cube(num) and is_cube(den)):
            return True, i, N
        details.append((i, 'i-free part is a cube', N))
    return False, details


if __name__ == '__main__':
    MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    for which in ['A', 'E', 'U']:
        print('target', which)
        for m in range(1, MMAX + 1):
            res = obstruction(m, which)
            if res[0]:
                N = res[2]
                print('   m=%2d: OBSTRUCTION at pole u=1/%d, norm N(nu) = %s' % (m, res[1], N if len(str(N)) < 80 else str(N)[:80] + '...'))
            else:
                print('   m=%2d: no obstruction found (%s)' % (m, res[1]))
