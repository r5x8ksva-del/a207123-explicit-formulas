# -*- coding: utf-8 -*-
"""s10-b2 (presentation): which primes of the note-08 certificate (T = 5040) are actually needed?
Greedy removal: a prime is dropped if the sieve (b0 != 0) and the l-adic coverage stay complete without it."""
import sys
sys.path.insert(0, __file__.rsplit('\\', 1)[0] if '\\' in __file__ else '.')
from s10sieve import Cert, sieve, padic_cover

T = 5040
NOTE = {1: [(3, 8), (11, 60), (13, 168), (29, 840), (2521, 2520)],
        2: [(7, 48), (17, 72), (19, 18), (41, 280), (71, 5040), (127, 126)],
        3: [(13, 84), (71, 70)]}


def complete(certs):
    if not certs:
        return False
    ns = sieve(T, certs)[0]
    if ns:
        return False
    unc = padic_cover(T, certs, [c.mu_modular() for c in certs])[0]
    return len(unc) == 0


for part, fibres in (('U', (1, 2)), ('E', (1, 2, 3))):
    certs = [Cert(i, l, P, part) for i in fibres for (l, P) in NOTE[i]]
    assert complete(certs)
    # try to drop large-l primes last (they are cheap to keep in a table? no: try in table order reversed)
    kept = list(certs)
    for c in list(reversed(certs)):
        trial = [d for d in kept if d is not c]
        if complete(trial):
            kept = trial
            print('%s: dropped fibre %d l=%d' % (part, c.i, c.l), flush=True)
    print('%s: minimal (greedy, reverse table order) certificate: %s' % (part, [(c.i, c.l, c.P) for c in kept]), flush=True)
    # each kept prime is necessary
    nec = all(not complete([d for d in kept if d is not c]) for c in kept)
    print('%s: every kept prime necessary: %s' % (part, nec), flush=True)
