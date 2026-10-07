# -*- coding: utf-8 -*-
"""Brute-force evidence for sections 5 and 6 of notes/Lean定义核对清单.md, computed from the definitions of
U and N by enumeration (not from Lean and not from the recurrences).

  * where (L1 U)(k,m) is nonzero, with U extended by 0 to negative indices (the Lean convention), and what
    happens if the coefficient m of X^3 is replaced by m-1;
  * that L_N N vanishes for k>=3, q>=1 when the coefficient q-1 is applied at the output point, as in
    `mulOp (cM - 1) * opX ^ 3 * (1 + opEinv) ^ 2`, and fails with the coefficient at the input points or
    with q in place of q-1;
  * the doubled areas det2 of the triangles in the support of L1, and of the Stirling recurrence.

Usage:  py -3.14 code/main_extra/sec5_6_bruteforce.py   (about a minute; exit code 1 if an expectation fails)
"""
import itertools
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')


def good(a, b, c):
    return b == c or (b <= a and c <= a)


def legal(h):
    return all(good(*h[j:j + 3]) for j in range(len(h) - 2))


K, M, KN = 8, 4, 7
U = {(k, m): sum(1 for h in itertools.product(range(m + 1), repeat=k) if legal(h))
     for k in range(K + 1) for m in range(M + 1)}
N = {(k, q): sum(1 for w in itertools.product(range(1, q + 1), repeat=k)
                 if len(set(w)) == q and legal(w))
     for k in range(KN + 1) for q in range(k + 1)}


def u(k, m):
    return U[(k, m)] if k >= 0 and m >= 0 else 0


def n(k, q):
    return N.get((k, q), 0) if k >= 0 and q >= 0 else 0


def L1U(k, m, coef):
    return u(k, m) - u(k, m - 1) - u(k - 1, m) - coef(m) * u(k - 3, m)


def LNN(k, q, mode):
    if mode == 'the coefficient at the output point':   # (q-1) X^3 (1+Y)^2, as in Lean
        tail = (q - 1) * (n(k - 3, q) + 2 * n(k - 3, q - 1) + n(k - 3, q - 2))
    elif mode == 'the coefficient at the input points':  # (1+Y)^2 X^3 (q-1)
        tail = (q - 1) * n(k - 3, q) + 2 * (q - 2) * n(k - 3, q - 1) + (q - 3) * n(k - 3, q - 2)
    else:                                           # q in place of q-1
        tail = q * (n(k - 3, q) + 2 * n(k - 3, q - 1) + n(k - 3, q - 2))
    return n(k, q) - n(k - 1, q) - n(k - 1, q - 1) - tail


def det2(p, q, r):
    return (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])


fails = 0


def expect(ok, text):
    global fails
    fails += not ok
    print('%s %s' % ('PASS' if ok else 'FAIL', text))


print('U_k(m), 0<=k<=%d, 0<=m<=%d; N(k,q), 0<=q<=k<=%d; both by enumeration' % (K, M, KN))
print('U rows m=0..%d:' % M, [[u(k, m) for k in range(K + 1)] for m in range(M + 1)])
print('N rows k=0..%d:' % KN, [[n(k, q) for q in range(k + 1)] for k in range(KN + 1)])

nz = {(k, m): L1U(k, m, lambda m: m) for k in range(K + 1) for m in range(M + 1) if L1U(k, m, lambda m: m)}
expect(nz == {(0, 0): 1, **{(2, m): m for m in range(1, M + 1)}},
       '(L1 U)(k,m) is nonzero exactly at (0,0) (value 1) and (2,m), m>=1 (value m): %s' % nz)
print('     (3,1): %d - %d - %d - 1*%d = %d;  (7,2): %d - %d - %d - 2*%d = %d'
      % (u(3, 1), u(3, 0), u(2, 1), u(0, 1), L1U(3, 1, lambda m: m),
         u(7, 2), u(7, 1), u(6, 2), u(4, 2), L1U(7, 2, lambda m: m)))
bad = [(k, m) for k in range(3, K + 1) for m in range(1, M + 1) if L1U(k, m, lambda m: m - 1)]
expect(len(bad) == (K - 2) * M, 'with m-1 in place of m, nonzero at all %d points of 3<=k<=%d, 1<=m<=%d'
       % (len(bad), K, M))

for mode in ('the coefficient at the output point', 'the coefficient at the input points', 'q in place of q-1'):
    z = {(k, q): LNN(k, q, mode) for k in range(3, KN + 1) for q in range(1, KN + 1) if LNN(k, q, mode)}
    expect((not z) == (mode == 'the coefficient at the output point'),
           'L_N N on 3<=k<=%d, 1<=q<=%d with %s: %d nonzero values %s'
           % (KN, KN, mode, len(z), dict(list(z.items())[:3])))

supp = [(0, 0), (0, 1), (1, 0), (3, 0)]
dets = {t: det2(*t) for t in itertools.combinations(supp, 3)}
expect(max(abs(d) for d in dets.values()) == 3 and dets[((0, 0), (0, 1), (3, 0))] == -3,
       'support of L1 as (X-degree, E^-1-degree) = %s; det2 of its triangles: %s' % (supp, dets))
expect(abs(det2((0, 0), (1, 1), (1, 0))) == 1,
       'S(n,k) = S(n-1,k-1) + k S(n-1,k): support (0,0),(1,1),(1,0), det2 = %d' % det2((0, 0), (1, 1), (1, 0)))
print('%d FAIL' % fails)
sys.exit(1 if fails else 0)
