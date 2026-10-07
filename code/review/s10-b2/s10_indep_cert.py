# -*- coding: utf-8 -*-
"""s10-b2 checks (b)(c): an independent certificate with a different modulus and other primes.

T' = 32760 = 2^3 3^2 5 7 13  (note 08 uses 5040; reviewer s9-b2 reported 83160 and 55440).
Primes from the catalogue of s10_find_primes.py (eta-order dividing 32760), none of them a
certificate prime of the same fibre in note 08:
  fibre 1: (53,468) (131,130) (181,32760) (521,520) (937,936) (2341,585)
  fibre 2: (3,26) (131,130) (937,936) (1093,1092)
  fibre 3: (5,20) (131,65) (181,32760)          [5 divides disc(b_3) = -255: allowed by Lemma 8/9]
Claims checked: sieve U (fibres 1,2) and E (fibres 1,2,3) exclude every class (n0,b0) in (Z/T')^2 with
b0 != 0; l-adic coverage of every n0 in Z/T'.  Variants without the prime 3 (fibre 2) and without 5
(fibre 3).  The sparse sieve is first cross-validated against the dense sieve on cases with survivors.
"""
import sys
import time
from math import lcm
sys.path.insert(0, __file__.rsplit('\\', 1)[0] if '\\' in __file__ else '.')
from s10sieve import Cert, verify_cert_static, sieve, sieve_sparse, padic_cover

FAIL = 0
PASS = 0


def report(name, ok, info=''):
    global FAIL, PASS
    if ok:
        PASS += 1
    else:
        FAIL += 1
    print(('PASS ' if ok else 'FAIL ') + name + (' | ' + info if info else ''), flush=True)


t0 = time.time()
# ------------------------------------------------------------- cross-validation of the two sieves
NOTE = {1: [(3, 8), (11, 60), (13, 168), (29, 840), (2521, 2520)],
        2: [(7, 48), (17, 72), (19, 18), (41, 280), (71, 5040), (127, 126)],
        3: [(13, 84), (71, 70)]}
for part, fibres in (('U', (1,)), ('E', (1, 2))):
    certs = [Cert(i, l, P, part) for i in fibres for (l, P) in NOTE[i]]
    a = sieve(5040, certs)[0]
    certs_s = sorted(certs, key=lambda c: -c.l)
    b = sieve_sparse(5040, certs_s)[0]
    report('cross-validation dense vs sparse sieve, T=5040, %s with fibres %s only: %d vs %d survivors' % (part, fibres, a, b),
           a == b and a > 0)

# ------------------------------------------------------------- the independent certificate
T = 32760
NEW = {1: [(53, 468), (131, 130), (181, 32760), (521, 520), (937, 936), (2341, 585)],
       2: [(3, 26), (131, 130), (937, 936), (1093, 1092)],
       3: [(5, 20), (131, 65), (181, 32760)]}
okst = True
for i, lst in NEW.items():
    for l, P in lst:
        f = verify_cert_static(i, l, P, T)
        print('   fibre %d  l=%-5d P=%-6d %s' % (i, l, P, f))
        if not (f['prime'] and f['odd'] and f['l_not_div_i'] and f['exact_order'] and f['P_div_T']):
            okst = False
        if l in dict(NOTE[i]):
            okst = False
report('static facts of the new certificate (prime, odd, l!|i, exact order, P|32760, not a note-08 prime of that fibre)', okst)
report('lcm of periods: U = %d, E = %d' % (lcm(*[P for i in (1, 2) for (l, P) in NEW[i]]), lcm(*[P for i in (1, 2, 3) for (l, P) in NEW[i]])),
       lcm(*[P for i in (1, 2) for (l, P) in NEW[i]]) == T)


def run(part, fibres, drop=()):
    certs = [Cert(i, l, P, part) for i in fibres for (l, P) in NEW[i] if (i, l) not in drop]
    assert all(c.period_ok for c in certs)
    certs_s = sorted(certs, key=lambda c: -c.l)
    t1 = time.time()
    nsurv, sample, after = sieve_sparse(T, certs_s)
    tag = '%s fibres %s%s' % (part, fibres, (' without ' + str(drop)) if drop else '')
    report('sieve %s: every (n0,b0), b0 != 0 mod %d, excluded' % (tag, T), nsurv == 0,
           'survivors=%d sample=%s (after dense phase %d) %.0fs' % (nsurv, sample[:8], after, time.time() - t1))
    mus = []
    agree = True
    for c in certs:
        m1 = c.mu_modular()
        m2 = c.mu_exact() if c.P <= 40000 else m1
        if m1 is None or m1 != m2:
            agree = False
        mus.append(m1)
    report('l-adic %s: mu (mod l^2 route) == mu (exact eta^P route)' % tag, agree)
    unc, counts, first = padic_cover(T, certs, mus)
    report('l-adic %s: every n0 in Z/%d covered' % (tag, T), len(unc) == 0,
           'uncovered=%s first-hits=%s' % (unc[:10], [(c.i, c.l, k) for c, k in zip(certs, counts)]))
    return nsurv, unc


run('U', (1, 2))
run('E', (1, 2, 3))
run('U', (1, 2), drop=((2, 3),))
run('E', (1, 2, 3), drop=((2, 3), (3, 5)))
print('time %.0fs' % (time.time() - t0))
print('SUMMARY s10_indep_cert: PASS=%d FAIL=%d' % (PASS, FAIL))
sys.exit(1 if FAIL else 0)
