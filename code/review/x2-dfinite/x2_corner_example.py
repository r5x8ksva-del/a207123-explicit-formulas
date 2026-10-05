# -*- coding: utf-8 -*-
"""x2-dfinite: explicit example for the corner argument of the N-dimension formula (Theorem 3', c3b notes 7.2).

The sketch says: "corner (alpha*+3, beta'+2) only receives -(q-1-b) q_ab" (same method as 6).
For L_N = 1 - X - XY - (q-1) X^3 (1+Y)^2 this is true only if beta' is the LARGEST b with q_{alpha* b} != 0.
Example: Q = 2(q-2) - (q-1) Y  (alpha* = 0).  With beta' = 0 the position (3,2) of Q*L_N receives two terms that
cancel exactly; with beta' = 1 (the maximal one) the position (3,3) receives the single term -(q-2) q_01 != 0.
Operators: dict (a,b) -> polynomial in q (dict exponent -> coefficient); (c X^a Y^b)(d X^a' Y^b') = c * d(q-b) ...
"""
from math import comb


def padd(p, r):
    out = dict(p)
    for e, c in r.items():
        out[e] = out.get(e, 0) + c
    return {e: c for e, c in out.items() if c}


def pmul(p, r):
    out = {}
    for e, c in p.items():
        for f, d in r.items():
            out[e + f] = out.get(e + f, 0) + c * d
    return {e: c for e, c in out.items() if c}


def pshift(p, s):
    """p(q) -> p(q - s)."""
    out = {}
    for e, c in p.items():
        for t in range(e + 1):
            out[t] = out.get(t, 0) + c * comb(e, t) * (-s) ** (e - t)
    return {e: c for e, c in out.items() if c}


def omul(A, B):
    out = {}
    for (a, b), c in A.items():
        for (a2, b2), d in B.items():
            key = (a + a2, b + b2)
            out[key] = padd(out.get(key, {}), pmul(c, pshift(d, b)))   # Y^b d(q) = d(q-b) Y^b ; X does not touch q
    return {k: v for k, v in out.items() if v}


qm1 = {1: 1, 0: -1}                      # q - 1
LN = {(0, 0): {0: 1}, (1, 0): {0: -1}, (1, 1): {0: -1},
      (3, 0): {1: -1, 0: 1}, (3, 1): {1: -2, 0: 2}, (3, 2): {1: -1, 0: 1}}
Q = {(0, 0): {1: 2, 0: -4}, (0, 1): {1: -1, 0: 1}}   # 2(q-2) - (q-1) Y
P = omul(Q, LN)
print('Q*L_N coefficient at (3,2) [corner for beta\'=0]:', P.get((3, 2), {}))
print('Q*L_N coefficient at (3,3) [corner for beta\'=max=1]:', P.get((3, 3), {}))
ok = ((3, 2) not in P) and P.get((3, 3)) == pmul({1: -1, 0: 2}, {1: -1, 0: 1})
print('expected: (3,2) absent (exact cancellation); (3,3) == -(q-2)*q01 = (q-2)(q-1):', ok)
print('PASS' if ok else 'FAIL', 'X2-CORNER')
