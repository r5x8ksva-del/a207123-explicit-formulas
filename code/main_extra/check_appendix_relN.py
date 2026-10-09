# -*- coding: utf-8 -*-
"""Exact checks of the operator identities used in Appendix B of paper/main.tex (the annihilator of N), 2026-10-10.

Operators act on arrays f(k, m), 0 <= k < K, 0 <= m < M, with zeros at negative indices. X, Y (= E^{-1}),
multiplication by polynomials in (k, m) and the binomial transform (Pf)(k, m) = sum_{q<=m} C(m, q) f(k, q) only
look at smaller or equal indices, so every identity can be checked exactly on a finite window. Ground truth for U
and N comes from code/core.py. Each identity is tested on random integer arrays (and random polynomial
coefficients where the identity involves them).

Usage (task C root):  py -3.14 code/main_extra/check_appendix_relN.py     (exit code 1 on any FAIL)
"""
import os
import random
import sys
from math import comb

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import core  # noqa: E402

K, M = 12, 12
rng = random.Random(20261010)
FAILS = []


def check(name, ok):
    print('%s %s' % ('PASS' if ok else 'FAIL', name))
    if not ok:
        FAILS.append(name)


def arr(fn):
    return [[fn(k, m) for m in range(M)] for k in range(K)]


def rand_arr():
    return arr(lambda k, m: rng.randint(-9, 9))


def get(f, k, m):
    return f[k][m] if k >= 0 and m >= 0 else 0


def X(f, p=1):
    return arr(lambda k, m: get(f, k - p, m))


def Y(f, p=1):
    return arr(lambda k, m: get(f, k, m - p))


def add(*fs):
    return arr(lambda k, m: sum(f[k][m] for f in fs))


def sc(c, f):
    return arr(lambda k, m: c * f[k][m])


def mul(poly, f):          # multiplication by a polynomial function of (k, m)
    return arr(lambda k, m: poly(k, m) * f[k][m])


def P(f):
    return arr(lambda k, m: sum(comb(m, q) * f[k][q] for q in range(m + 1)))


def D(f, p=1):             # Delta = 1 - Y
    for _ in range(p):
        f = add(f, sc(-1, Y(f)))
    return f


def one_plus_Y(f, p=1):
    for _ in range(p):
        f = add(f, Y(f))
    return f


def eq(f, g, kmin=0, mmin=0):
    return all(f[k][m] == g[k][m] for k in range(kmin, K) for m in range(mmin, M))


def rand_poly(deg=2):
    cs = {(i, j): rng.randint(-4, 4) for i in range(deg + 1) for j in range(deg + 1 - i)}
    return lambda k, m: sum(c * k ** i * m ** j for (i, j), c in cs.items())


mvar = lambda k, m: m


def LN(f):                 # 1 - X - XY - (m-1) X^3 (1+Y)^2, second variable written m
    return add(f, sc(-1, X(f)), sc(-1, X(Y(f))), sc(-1, mul(lambda k, m: m - 1, X(one_plus_Y(f, 2), 3))))


def L1(f):                 # 1 - E^{-1} - X - m X^3
    return add(f, sc(-1, Y(f)), sc(-1, X(f)), sc(-1, mul(mvar, X(f, 3))))


def L1V(f):                # 1 - Y - X - (m-1) X^3
    return add(f, sc(-1, Y(f)), sc(-1, X(f)), sc(-1, mul(lambda k, m: m - 1, X(f, 3))))


def main():
    T = core.U_fast_table(K, M)
    U = arr(lambda k, m: T[k][m])
    Narr = arr(lambda k, q: core.N_from_U(T, k, q) if q <= k else 0)
    trials = [rand_arr() for _ in range(6)]

    check('B-a  Delta P Y = Y P', all(eq(D(P(Y(f))), Y(P(f))) for f in trials))
    check('B-b  P m = m Delta P', all(eq(P(mul(mvar, f)), mul(mvar, D(P(f)))) for f in trials))
    check('B-c  Delta^n P (1+Y)^n = P (n <= 4)',
          all(eq(D(P(one_plus_Y(f, n)), n), P(f)) for f in trials for n in range(5)))
    check('B-d  Delta m = (m-1) Delta + 1',
          all(eq(D(mul(mvar, f)), add(mul(lambda k, m: m - 1, D(f)), f)) for f in trials))
    check('B-e  Delta^c m Delta = ((m-c) Delta + c) Delta^c (c <= 4)',
          all(eq(D(mul(mvar, D(f)), c), add(mul(lambda k, m, c=c: m - c, D(D(f, c))), sc(c, D(f, c))))
              for f in trials for c in range(5)))
    check('B-f  m Delta^a P = Delta^a P (m(1+Y) - aY) (a <= 4)',
          all(eq(mul(mvar, D(P(f), a)), D(P(add(mul(mvar, one_plus_Y(f)), sc(-a, Y(f)))), a))
              for f in trials for a in range(5)))
    check('B-g  Y L1 = L1V Y', all(eq(Y(L1(f)), L1V(Y(f))) for f in trials))
    check('B-h  L1V P = Delta P L_N (transport identity)', all(eq(L1V(P(f)), D(P(LN(f)))) for f in trials))

    V = P(Narr)
    e0 = arr(lambda k, m: 1 if k == 0 and m == 0 else 0)
    check('B-i  V = P N = Y U + e0', eq(V, add(Y(U), e0)))
    check('B-j  L_N N = 0 for k >= 3, q >= 1', eq(LN(Narr), arr(lambda k, m: 0), 3, 1))
    check('B-k  L1V V = 0 for k >= 3, m >= 2', eq(L1V(V), arr(lambda k, m: 0), 3, 2))

    ok = True
    for _ in range(20):
        n, k0 = rng.randint(1, 5), rng.randint(0, 5)
        g = arr(lambda k, q: 0 if (k >= k0 and q >= n) else rng.randint(-9, 9))
        ok &= eq(D(P(g), n), arr(lambda k, m: 0), k0, n)
    check('B-l  g = 0 on {k>=k0, q>=n}  =>  Delta^n P g = 0 on {k>=k0, m>=n}', ok)

    # Normal form of Q L_N: r(a,b) = q(a,b) - q(a-1,b) - q(a-1,b-1) - sum_j C(2,j) (m-1-(b-j)) q(a-3,b-j)
    ok = True
    for _ in range(4):
        Q = {(a, b): rand_poly(1) for a in range(3) for b in range(3) if rng.random() < 0.7}

        def applyQ(f, Q=Q):
            return add(arr(lambda k, m: 0), *[mul(c, X(Y(f, b), a)) for (a, b), c in Q.items()])

        def qq(a, b, Q=Q):
            return Q.get((a, b), lambda k, m: 0)

        def r(a, b):
            terms = [(qq(a, b), 0), (qq(a - 1, b), 1), (qq(a - 1, b - 1), 1)]
            def rr(k, m):
                s = qq(a, b)(k, m) - qq(a - 1, b)(k, m) - qq(a - 1, b - 1)(k, m)
                for j in range(3):
                    s -= comb(2, j) * (m - 1 - (b - j)) * qq(a - 3, b - j)(k, m)
                return s
            return rr

        for f in trials[:3]:
            lhs = applyQ(LN(f))
            rhs = add(arr(lambda k, m: 0), *[mul(r(a, b), X(Y(f, b), a)) for a in range(6) for b in range(5)])
            ok &= eq(lhs, rhs)
    check('B-m  coefficients of Q L_N in normal form', ok)

    # Division by 1+Y from the left: c Y^d = (1+Y) M_d + (-1)^d tau^{-d}(c), M_d = sum_{i=1}^d (-1)^{i-1} tau^{-i}(c) Y^{d-i}
    ok = True
    for _ in range(4):
        c = rand_poly(2)
        for d in range(1, 5):
            for f in trials[:2]:
                lhs = mul(c, Y(f, d))
                Md = add(arr(lambda k, m: 0), *[sc((-1) ** (i - 1), mul(lambda k, m, i=i: c(k, m + i), Y(f, d - i)))
                                                for i in range(1, d + 1)])
                rhs = add(one_plus_Y(Md), sc((-1) ** d, mul(lambda k, m: c(k, m + d), f)))
                ok &= eq(lhs, rhs)
    check('B-n  c Y^d = (1+Y) M_d + (-1)^d tau^{-d}(c)', ok)

    print('%d PASS, %d FAIL' % (14 - len(FAILS), len(FAILS)))
    return 1 if FAILS else 0


if __name__ == '__main__':
    sys.exit(main())
