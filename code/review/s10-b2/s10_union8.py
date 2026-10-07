# -*- coding: utf-8 -*-
"""s10-b2 small follow-up checks for the report:
  1. the 8-prime table (union of the greedy-minimal certificates) is complete for U and for E (T = 5040);
  2. R1: list all sieve survivors when W~_2 is replaced by 1 + x^5 (expected: the classes of (0,5),
     (-5,-5), (-9,-5), (-4,5));
  3. with the sums starting at s = 0, G_1 = x^-7 u^2/(1-u) - x^-3 u/(1-u) - x^-1 (exact, random rational points).
"""
import sys
import random
from fractions import Fraction as Fr
sys.path.insert(0, __file__.rsplit('\\', 1)[0] if '\\' in __file__ else '.')
from s10sieve import Cert, sieve, padic_cover

FAIL = 0
PASS = 0


def report(name, ok, info=''):
    global FAIL, PASS
    if ok:
        PASS += 1
    else:
        FAIL += 1
    print(('PASS ' if ok else 'FAIL ') + name + (' | ' + info if info else ''), flush=True)


T = 5040
U8 = {1: [(3, 8), (11, 60), (29, 840), (2521, 2520)], 2: [(7, 48), (17, 72), (71, 5040)], 3: [(13, 84)]}
for part, fibres in (('U', (1, 2)), ('E', (1, 2, 3))):
    certs = [Cert(i, l, P, part) for i in fibres for (l, P) in U8[i]]
    ns = sieve(T, certs)[0]
    unc = padic_cover(T, certs, [c.mu_modular() for c in certs])[0]
    report('8-prime table, %s: sieve survivors = 0 and l-adic coverage complete' % part, ns == 0 and not unc,
           'survivors=%d uncovered=%s' % (ns, unc[:10]))

NOTE = {1: [(3, 8), (11, 60), (13, 168), (29, 840), (2521, 2520)],
        2: [(7, 48), (17, 72), (19, 18), (41, 280), (71, 5040), (127, 126)]}
certs = [Cert(1, l, P, 'U') for (l, P) in NOTE[1]] + [Cert(2, l, P, 'U', Wpoly=[1, 0, 0, 0, 0, 1]) for (l, P) in NOTE[2]]
ns, sample, _ = sieve(T, certs, want_list=10 ** 6)
expected = sorted(((n % T), (b % T)) for (n, b) in [(0, 5), (-5, -5), (-9, -5), (-4, 5)])
report('R1 survivors are exactly the classes of (0,5), (-5,-5), (-9,-5), (-4,5)', sorted(sample) == expected,
       'survivors=%s' % sorted(sample))

random.seed(7)
ok = True
for _ in range(20):
    x = Fr(random.randint(-50, 50), random.randint(51, 97))
    if x == 0:
        continue
    u = x ** 3 / (1 - x)
    P1 = (1 - x) * (1 - x - x ** 3)
    W1 = 1 + x ** 2 * (1 - x)
    G1 = W1 / P1
    rhs = x ** -7 * u ** 2 / (1 - u) - x ** -3 * u / (1 - u) - 1 / x
    if G1 != rhs:
        ok = False
report('G_1 = x^-7 u^2/(1-u) - x^-3 u/(1-u) - x^-1 at 20 random rational points', ok)

print('SUMMARY s10_union8: PASS=%d FAIL=%d' % (PASS, FAIL))
sys.exit(1 if FAIL else 0)
