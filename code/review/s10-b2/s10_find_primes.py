# -*- coding: utf-8 -*-
"""s10-b2 exploration: catalogue of primes l (fibres i = 1,2,3) for which eta mod l has a smooth order.

Vectorised over all primes l < LMAX: eta^N0 mod l in F_l[x]/(b_i) with N0 a large smooth number;
for the primes with eta^N0 = 1 the exact order is computed (pure Python) by removing prime factors.
Output: lines 'CAT i l P factorisation'.  Also prints, for candidate moduli T, which primes (outside
the 13 primes of note 08) have period dividing T, and the lcm of those periods per fibre.
"""
import sys
import numpy as np
from math import lcm
sys.path.insert(0, __file__.rsplit('\\', 1)[0] if '\\' in __file__ else '.')
from s10lib import Kmod, prime_factors

LMAX = 2_000_000
N0 = 2 ** 8 * 3 ** 5 * 5 ** 3 * 7 ** 3 * 11 ** 2 * 13 ** 2 * 17 * 19 * 23
NOTE_PRIMES = {1: {3, 11, 13, 29, 2521}, 2: {7, 17, 19, 41, 71, 127}, 3: {13, 71}}

sieve = np.ones(LMAX, dtype=bool)
sieve[:2] = False
for p in range(2, int(LMAX ** 0.5) + 1):
    if sieve[p]:
        sieve[p * p::p] = False
primes = np.nonzero(sieve)[0].astype(np.int64)
primes = primes[primes >= 3]


def vmul(a, b, L, ii):
    a0, a1, a2 = a
    b0, b1, b2 = b
    p0 = (a0 * b0) % L
    p1 = ((a0 * b1) % L + (a1 * b0) % L) % L
    p2 = ((a0 * b2) % L + (a1 * b1) % L + (a2 * b0) % L) % L
    p3 = ((a1 * b2) % L + (a2 * b1) % L) % L
    p4 = (a2 * b2) % L
    t3 = (p3 * ii) % L
    t4 = (p4 * ii) % L
    return ((p0 + t3) % L, (p1 - t3 + t4) % L, (p2 - t4) % L)


catalog = []
for i in (1, 2, 3):
    L = primes[primes % i != 0] if i > 1 else primes
    ii = np.array([pow(i, -1, int(l)) for l in L], dtype=np.int64)
    one = np.ones_like(L)
    zero = np.zeros_like(L)
    base = (zero.copy(), one.copy(), zero.copy())
    res = (one.copy(), zero.copy(), zero.copy())
    e = N0
    while e:
        if e & 1:
            res = vmul(res, base, L, ii)
        base = vmul(base, base, L, ii)
        e >>= 1
    ok = (res[0] == 1) & (res[1] == 0) & (res[2] == 0)
    for l in L[ok]:
        l = int(l)
        K = Kmod(i, l)
        P = N0
        for q in prime_factors(N0):
            while P % q == 0 and K.pow(K.eta(), P // q) == (1, 0, 0):
                P //= q
        assert K.pow(K.eta(), P) == (1, 0, 0)
        catalog.append((i, l, P))
        print('CAT %d %d %d %s' % (i, l, P, prime_factors(P)), flush=True)

print('catalogue size', len(catalog))
for T in (2520, 5040, 7560, 10080, 15120, 20160, 25200, 27720, 30240, 32760, 35280, 37800, 40320, 50400, 65520):
    sel = [(i, l, P) for (i, l, P) in catalog if T % P == 0 and l not in NOTE_PRIMES[i]]
    per = {}
    for i in (1, 2, 3):
        Ps = [P for (j, l, P) in sel if j == i]
        per[i] = (len(Ps), lcm(*Ps) if Ps else 1)
    print('T=%6d  fibre1 %s  fibre2 %s  fibre3 %s' % (T, per[1], per[2], per[3]))
    print('        ', [(i, l, P) for (i, l, P) in sel])
