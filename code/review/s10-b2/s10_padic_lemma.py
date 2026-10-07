# -*- coding: utf-8 -*-
"""s10-b2 check (c): the conclusion of Lemma 9, tested without its proof (no binomial series).

For a certificate (i, l, P) and b = P*b' (b' != 0), Lemma 9 says
    D_i(n, b) = b' l (Delta_l(n) + l kappa),   Delta_l(n) = pi(mu) ^ pi(W eta^n),  eta^P = 1 + l mu.
Consequences tested here, for random n and b' (negative b', l | b', l^2 | b' included):
    v_l(D) = 1 + v_l(b')  whenever Delta_l(n) != 0 mod l,   and   D / l^{1+v_l(b')} = (b'/l^{v_l(b')}) Delta_l(n) mod l.
D is computed exactly modulo l^K, K = v_l(b') + 3 (D lies in Z_(l)), by plain powering in (Z/l^K)[x]/(b_i);
for small P also exactly in Q (Fractions) as a cross-check of the modular computation.
"""
import sys
import random
from fractions import Fraction as Fr
sys.path.insert(0, __file__.rsplit('\\', 1)[0] if '\\' in __file__ else '.')
from s10lib import Kmod, Ki
from s10sieve import Cert, W_for

FAIL = 0
PASS = 0


def report(name, ok, info=''):
    global FAIL, PASS
    if ok:
        PASS += 1
    else:
        FAIL += 1
    print(('PASS ' if ok else 'FAIL ') + name + (' | ' + info if info else ''), flush=True)


def vl(x, l):
    v = 0
    while x % l == 0:
        x //= l
        v += 1
    return v


def eta_pow_mod(K, e):
    if e >= 0:
        return K.pow(K.eta(), e)
    inv = (1 % K.M, 0, K.i % K.M)                # eta^{-1} = 1 + i eta^2
    return K.pow(inv, -e)


def D_mod(i, l, K_exp, wpoly, n, b):
    M = l ** K_exp
    K = Kmod(i, M)
    p = eta_pow_mod(K, b)
    q = K.mul(K.ev(wpoly), eta_pow_mod(K, n))
    return (p[1] * q[2] - p[2] * q[1]) % M


def D_exact(i, wpoly, n, b, KK):
    p = KK.eta_pow(b)
    q = KK.mul(KK.ev(wpoly), KK.eta_pow(n))
    return p[1] * q[2] - p[2] * q[1]


random.seed(1008)
CERTS = {1: [(3, 8), (11, 60), (13, 168), (29, 840), (2521, 2520), (53, 468), (131, 130)],
         2: [(7, 48), (17, 72), (19, 18), (41, 280), (71, 5040), (127, 126), (3, 26), (1093, 1092)],
         3: [(13, 84), (71, 70), (5, 20)]}
tests = 0
bad = []
nzero_delta = 0
for part in ('U', 'E'):
    for i, lst in CERTS.items():
        for (l, P) in lst:
            c = Cert(i, l, P, part)
            mu = c.mu_modular()
            w = W_for(part, i)
            good = c.delta_good(mu)
            delta_vals = (mu[1] * c.qn[:, 1] - mu[2] * c.qn[:, 0]) % l
            ntest = 40 if P <= 1100 else 12
            for _ in range(ntest):
                n = random.randint(-3000, 3000)
                bp = random.choice([random.randint(-12, 12) or 1, l * random.choice([-2, -1, 1, 2]),
                                    l * l * random.choice([-1, 1]), -random.randint(1, 6)])
                v = vl(abs(bp), l)
                Kexp = v + 3
                D = D_mod(i, l, Kexp, w, n, P * bp)
                dl = int(delta_vals[n % P])        # Delta_l(n) = mu1 q2 - mu2 q1 mod l (same orientation as D below)
                tests += 1
                if dl % l == 0:
                    nzero_delta += 1
                    if D % (l ** (v + 2)) != 0:
                        bad.append(('Delta=0 but v_l(D) < v+2', part, i, l, n, bp))
                    continue
                if D % (l ** (v + 1)) != 0 or D % (l ** (v + 2)) == 0:
                    bad.append(('valuation', part, i, l, n, bp))
                    continue
                lhs = (D // l ** (v + 1)) % l
                bpu = (bp // l ** v) % l
                # D = p1 q2 - p2 q1 and Delta = mu1 q2 - mu2 q1: same orientation
                if lhs != (bpu * dl) % l:
                    bad.append(('residue', part, i, l, n, bp, lhs, (bpu * dl) % l))
report('Lemma 9 conclusion: v_l(D_i(n,Pb\')) = 1 + v_l(b\') and D/(l^{1+v} ) = (b\'/l^v) Delta mod l  (%d random tests; %d with Delta = 0 mod l only checked for v_l >= v+2)'
       % (tests, nzero_delta), not bad, str(bad[:5]))

# exact cross-check of the modular D for small periods
okx = True
cnt = 0
for part in ('U', 'E'):
    for (i, l, P) in [(1, 3, 8), (2, 19, 18), (2, 3, 26), (3, 5, 20), (1, 11, 60), (2, 7, 48)]:
        KK = Ki(i)
        w = W_for(part, i)
        for _ in range(8):
            n = random.randint(-60, 60)
            bp = random.choice([-3, -2, -1, 1, 2, 3, l, -l])
            De = D_exact(i, w, n, P * bp, KK)
            num, den = De.numerator, De.denominator
            M = l ** 6
            Dm = D_mod(i, l, 6, w, n, P * bp)
            if (num * pow(den, -1, M)) % M != Dm:
                okx = False
            cnt += 1
report('exact D (Fractions) agrees with D mod l^6 (%d cases, small periods incl. l=3, l=5 | disc(b_3))' % cnt, okx)

print('SUMMARY s10_padic_lemma: PASS=%d FAIL=%d' % (PASS, FAIL))
sys.exit(1 if FAIL else 0)
