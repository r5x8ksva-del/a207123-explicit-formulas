# -*- coding: utf-8 -*-
"""s10-b2 checks (b)(c) on the certificate printed in note 08 (T = 5040, 13 primes), with my own code.

  * static facts: l prime, odd, l does not divide i, eta has exact order P mod l, P | 5040,
    and (claimed in the note, not needed) l does not divide disc(b_i);
  * sieve U (fibres 1,2) and E (fibres 1,2,3): every (n0,b0) in (Z/5040)^2 with b0 != 0 excluded;
  * l-adic: mu mod l by two routes (eta^P mod l^2, and exact eta^P in Z[1/i][eta]); every n0 in Z/5040
    covered; first-hit counts in the note's order (U: 3780, 1176, 72, 6, 6); for E, the n0 not covered by
    fibre 1 (note: {2515, 5035}) and who covers them (note: l = 7, 17 of fibre 2).
"""
import sys
import time
sys.path.insert(0, __file__.rsplit('\\', 1)[0] if '\\' in __file__ else '.')
from s10sieve import Cert, verify_cert_static, sieve, padic_cover

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
NOTE = {1: [(3, 8), (11, 60), (13, 168), (29, 840), (2521, 2520)],
        2: [(7, 48), (17, 72), (19, 18), (41, 280), (71, 5040), (127, 126)],
        3: [(13, 84), (71, 70)]}

t0 = time.time()
allstatic = True
for i, lst in NOTE.items():
    for l, P in lst:
        f = verify_cert_static(i, l, P, T)
        print('   fibre %d  l=%-5d P=%-5d %s' % (i, l, P, f))
        if not all(f.values()):
            allstatic = False
report('static facts of the 13 certificate primes (prime, odd, l!|i, exact order P, P|5040, l!|disc)', allstatic)

for part, fibres in (('U', (1, 2)), ('E', (1, 2, 3))):
    certs = [Cert(i, l, P, part) for i in fibres for (l, P) in NOTE[i]]
    report('%s: eta^P == 1 recomputed while tabulating' % part, all(c.period_ok for c in certs))
    nsurv, sample, kills = sieve(T, certs)
    labels = ['f%d:l=%d' % (c.i, c.l) for c in certs]
    print('   %s sieve first-kill counts: %s' % (part, list(zip(labels, kills))))
    report('%s sieve: all %d classes (n0,b0), b0 != 0 mod %d, excluded' % (part, T * (T - 1), T), nsurv == 0,
           'survivors=%d sample=%s' % (nsurv, sample[:10]))
    report('%s sieve: kill counts add up to %d' % (part, T * (T - 1)), sum(kills) == T * (T - 1), str(sum(kills)))
    # l-adic
    mus = []
    agree = True
    for c in certs:
        m1, m2 = c.mu_modular(), c.mu_exact()
        if m1 is None or m1 != m2:
            agree = False
        mus.append(m1)
    report('%s: mu mod l from eta^P mod l^2 equals mu from exact eta^P (all certs)' % part, agree)
    unc, counts, first = padic_cover(T, certs, mus)
    print('   %s l-adic first-hit counts: %s' % (part, list(zip(labels, counts))))
    report('%s l-adic: every n0 in Z/%d has a cert with Delta_l(n0) != 0 mod l' % (part, T), len(unc) == 0, str(unc[:20]))
    if part == 'U':
        fib1 = [counts[k] for k, c in enumerate(certs) if c.i == 1]
        report('U l-adic first-hit counts of fibre 1 = [3780, 1176, 72, 6, 6] (note)', fib1 == [3780, 1176, 72, 6, 6], str(fib1))
        report('U l-adic: fibre 1 alone suffices', all(certs[first[n]].i == 1 for n in range(T)))
    else:
        f1 = [c for c in certs if c.i == 1]
        unc1, _, _ = padic_cover(T, f1, [mus[k] for k, c in enumerate(certs) if c.i == 1])
        report('E l-adic: n0 not covered by fibre 1 = {2515, 5035} (note)', sorted(unc1) == [2515, 5035], str(unc1))
        who = {n: 'f%d:l=%d' % (certs[first[n]].i, certs[first[n]].l) for n in unc1}
        print('   E: these are covered by', who)
        # also: which fibre-2/3 certs cover them at all
        for n in unc1:
            cov = ['f%d:l=%d' % (c.i, c.l) for c, mu in zip(certs, mus) if c.i != 1 and c.delta_good(mu)[n % c.P]]
            print('   E: n0=%d covered by %s' % (n, cov))

print('time %.1fs' % (time.time() - t0))
print('SUMMARY s10_note_cert: PASS=%d FAIL=%d' % (PASS, FAIL))
sys.exit(1 if FAIL else 0)
