# -*- coding: utf-8 -*-
"""s10-b2 reverse checks: corrupt one key quantity at a time and confirm that the corresponding
check of my scripts reports failure (so the PASS results are not vacuous).

  R1  sieve must keep a planted true solution: replace the fibre-2 element W~_2 by 1 + x^5, so that
      (n,b) = (0,5) is a genuine common solution of (true) fibre 1 and (corrupted) fibre 2.
      Expected: the note-08 sieve (T=5040) leaves survivors, among them the class (0,5).
  R2  l-adic test must fail at a planted solution with b = 0 mod T: elements 1 + x^5040 on both fibres,
      so (0, 5040) is a genuine common solution.  Expected: n0 = 0 uncovered.
  R3  wrong exponent in the residue element (eta^{-3m-2} instead of eta^{-3m-3}) or wrong constant:
      the exact identity det[e_g1, e_g2, R] = (1/i)^g1 c D_i(n,b) must break.
  R4  a wrong period (P/2 or 2P) must fail the exact-order test; a prime dividing i must be rejected.
  R5  dropping fibre 2 for U (fibre 1 only) leaves sieve survivors; E with fibre 1 only leaves the
      l-adic classes n0 = 2515, 5035 uncovered.
  R6  small window: with W~_2 replaced by 1 + x^5 the common-zero search finds (0,5).
"""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, __file__.rsplit('\\', 1)[0] if '\\' in __file__ else '.')
from s10sieve import Cert, sieve, padic_cover
from s10lib import Ki, Wtilde_poly, P_poly, W_poly, pderiv, const_c, exact_order_check, cols_det

GOOD = 0
BAD = 0


def expect_failure(name, failed, info=''):
    """failed = True means the corrupted input was detected (reverse check succeeded)"""
    global GOOD, BAD
    if failed:
        GOOD += 1
        print('REVERSE-OK   ' + name + (' | ' + info if info else ''), flush=True)
    else:
        BAD += 1
        print('REVERSE-MISS ' + name + (' | ' + info if info else ''), flush=True)


T = 5040
NOTE = {1: [(3, 8), (11, 60), (13, 168), (29, 840), (2521, 2520)],
        2: [(7, 48), (17, 72), (19, 18), (41, 280), (71, 5040), (127, 126)],
        3: [(13, 84), (71, 70)]}

# R1
W5 = [1, 0, 0, 0, 0, 1]
certs = [Cert(1, l, P, 'U') for (l, P) in NOTE[1]] + [Cert(2, l, P, 'U', Wpoly=W5) for (l, P) in NOTE[2]]
ns, sample, kills = sieve(T, certs, want_list=10 ** 6)
expect_failure('R1 planted solution (0,5) on corrupted fibre 2: sieve leaves survivors', ns > 0 and (0, 5) in sample,
               'survivors=%d, (0,5) kept: %s, (-5,-5) kept: %s' % (ns, (0, 5) in sample, (5035, 5035) in sample))

# R2
Wbig = [1] + [0] * 5039 + [1]
certs = [Cert(1, l, P, 'U', Wpoly=Wbig) for (l, P) in NOTE[1]] + [Cert(2, l, P, 'U', Wpoly=Wbig) for (l, P) in NOTE[2]]
mus = [c.mu_modular() for c in certs]
unc, counts, first = padic_cover(T, certs, mus)
expect_failure('R2 planted solution (0,5040): l-adic coverage fails at n0 = 0', 0 in unc, 'uncovered=%s' % unc[:10])

# R3
ok_break_exp = False
ok_break_const = False
for m in (2, 3, 4):
    for i in (1, 2):
        K = Ki(i)
        P, W = P_poly(m), W_poly(m)
        eta = K.eta_pow(1)
        one_m_eta = K.add((Fr(1), Fr(0), Fr(0)), K.scal(Fr(-1), eta))
        up = K.mul(K.mul(K.eta_pow(2), (Fr(3), Fr(-2), Fr(0))), K.inv(K.mul(one_m_eta, one_m_eta)))
        rho = K.mul(up, K.mul(K.ev(W), K.inv(K.ev(pderiv(P)))))
        wrong_exp = K.scal(const_c(i, m), K.ev(Wtilde_poly(i), shift=-3 * m - 2))
        wrong_const = K.scal(2 * const_c(i, m), K.ev(Wtilde_poly(i), shift=-3 * m - 3))
        if rho != wrong_exp:
            ok_break_exp = True
        if rho != wrong_const:
            ok_break_const = True
expect_failure('R3a residue element with eta^{-3m-2} differs from the definition', ok_break_exp)
expect_failure('R3b residue element with 2*c_{i,m} differs from the definition', ok_break_const)
# a shifted n in the joint condition really changes the zero set (fibre 2 shifted by one)
K1, K2 = Ki(1), Ki(2)
W1, W2 = K1.ev(Wtilde_poly(1)), K2.ev(Wtilde_poly(2))


def D(K, Wv, n, b):
    p = K.eta_pow(b)
    q = K.mul(Wv, K.eta_pow(n))
    return p[1] * q[2] - p[2] * q[1]


common_shift = [(n, b) for n in range(-30, 31) for b in range(-30, 31) if b != 0
                and D(K1, W1, n, b) == 0 and D(K2, W2, n + 1, b) == 0]
print('INFO R3c joint system with fibre 2 shifted by one (D_1(n,b)=D_2(n+1,b)=0), |n|,|b|<=30, b!=0: %s' % common_shift)

# R4
bad_period = (not exact_order_check(1, 2521, 1260)) and (not exact_order_check(2, 71, 2520)) \
    and (not exact_order_check(1, 29, 1680))
expect_failure('R4a wrong periods P/2 or 2P rejected by the exact-order test', bad_period)
try:
    Cert(2, 2, 3, 'U')
    rejected = False
except ValueError:
    rejected = True
expect_failure('R4b prime dividing i (l=2, i=2) rejected (i not invertible mod l)', rejected)

# R5
certs = [Cert(1, l, P, 'U') for (l, P) in NOTE[1]]
ns, sample, kills = sieve(T, certs)
expect_failure('R5a U with fibre 1 only: sieve leaves survivors', ns > 0, 'survivors=%d sample=%s' % (ns, sample[:5]))
certs = [Cert(1, l, P, 'E') for (l, P) in NOTE[1]]
unc, counts, first = padic_cover(T, certs, [c.mu_modular() for c in certs])
expect_failure('R5b E with fibre 1 only: l-adic coverage fails', sorted(unc) == [2515, 5035], 'uncovered=%s' % unc)

# R6
K2 = Ki(2)
W5v = K2.ev(W5)
found = [(n, b) for n in range(-20, 21) for b in range(-20, 21) if b != 0
         and D(K1, W1, n, b) == 0 and D(K2, W5v, n, b) == 0]
expect_failure('R6 small window with W~_2 -> 1 + x^5 finds a common zero', (0, 5) in found, str(found))

print('SUMMARY s10_reverse: REVERSE-OK=%d REVERSE-MISS=%d' % (GOOD, BAD))
sys.exit(1 if BAD else 0)
