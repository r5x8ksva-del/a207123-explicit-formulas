# -*- coding: utf-8 -*-
"""Checks for Corollary cor:negzeros and Remark rem:chains of paper/main.tex (added 2026-10-09).

Ground truth from code/core.py: U_fast_table (height DP of the definition) with inclusion-exclusion over the
set of values (N_from_U), cross-checked against the DFS definition N_brute for k <= 8; allowed_rows (the binary
rows avoiding 001 and 010, i.e. the poset Lambda_k).
  C0  N_from_U = N_brute                                                                              (1<=k<=8)
  C1  N(k,q) = number of (q-1)-element chains in Lambda_k minus {0...0, 1...1}                     (1<=k<=12)
  C2  deg h_k = floor(2k/3); u_k(-j) = 0 for 1<=j<=ceil(k/3); u_k(-ceil(k/3)-1) = (-1)^k lc(h_k)     (1<=k<=30)
  C3  h_k has a negative coefficient                                                                (3<=k<=30)
  C4  Boolean lattice {0,1}^k: (q-1)-element chains of the proper part = q! S(k,q), and the numerator of
      sum_m (m+1)^k t^m is the descent polynomial sum_sigma t^des(sigma)                             (1<=k<=7)
  C5  good triples = triples avoiding the consecutive patterns 112, 121, 123, 132, 213, 231   (values 0..3)
Usage (task C root):  py -3.14 code/main_extra/check_chains_negzeros.py      (exit code 1 on any FAIL)
"""
import math
import os
import sys
from fractions import Fraction
from itertools import permutations, product

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import core  # noqa: E402

FAILS = []


def check(name, ok, extra=''):
    print('%s %s%s' % ('PASS' if ok else 'FAIL', name, ('  ' + extra) if extra else ''))
    if not ok:
        FAILS.append(name)


def chain_counts(elems):
    """c[j] = number of j-element chains in the poset (elems, componentwise order); c[0] = 1."""
    elems = sorted(elems, key=sum)
    leq = lambda x, y: all(a <= b for a, b in zip(x, y))
    top = [dict() for _ in elems]           # top[i][j]: j-element chains with largest element elems[i]
    for i, y in enumerate(elems):
        top[i][1] = 1
        for i2 in range(i):
            x = elems[i2]
            if x != y and leq(x, y):
                for j, c in top[i2].items():
                    top[i][j + 1] = top[i].get(j + 1, 0) + c
    out = {0: 1}
    for d in top:
        for j, c in d.items():
            out[j] = out.get(j, 0) + c
    return out


def poly_mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def h_from_row(k, row):
    """h(t) = sum_{q=1}^k row[q] t^(q-1) (1-t)^(k-q), as an integer coefficient list (trailing zeros removed)."""
    h = [0] * (k + 1)
    for q in range(1, k + 1):
        term = [0] * (q - 1) + [1]
        for _ in range(k - q):
            term = poly_mul(term, [1, -1])
        for i, c in enumerate(term):
            h[i] += row.get(q, 0) * c
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


def binom_poly(x, q):
    r = Fraction(1)
    for i in range(q):
        r *= Fraction(x - i, i + 1)
    return r


def main():
    # rows of N for k <= 30 from the U table by inclusion-exclusion over the set of values (as in
    # check_paper_numbers.py), cross-checked against the DFS definition N_brute for k <= 8
    K = 30
    T = core.U_fast_table(K, K)
    rows = {k: {q: core.N_from_U(T, k, q) for q in range(k + 1)} for k in range(1, K + 1)}
    check('C0 N from the U table agrees with the DFS definition (1<=k<=8)',
          all(rows[k][q] == core.N_brute(k).get(q, 0) for k in range(1, 9) for q in range(1, k + 1)))

    # C1
    ok, bad = True, []
    for k in range(1, 13):
        lam = [tuple(r) for r in core.allowed_rows(k)]
        zero, one = tuple([0] * k), tuple([1] * k)
        assert zero in lam and one in lam
        cc = chain_counts([w for w in lam if w not in (zero, one)])
        for q in range(1, k + 1):
            if rows[k][q] != cc.get(q - 1, 0):
                ok = False
                bad.append((k, q, rows[k][q], cc.get(q - 1, 0)))
        if any(j > k - 1 for j in cc):
            ok = False
    check('C1 N(k,q) = #(q-1)-chains in the proper part of Lambda_k, no chains longer than k-1 (1<=k<=12)',
          ok, str(bad[:3]))

    # C2, C3
    ok2, ok3, info = True, True, []
    for k in range(1, K + 1):
        h = h_from_row(k, rows[k])
        s = len(h) - 1
        c = math.ceil(k / 3)
        u = lambda m: sum(Fraction(rows[k][q]) * binom_poly(m + 1, q) for q in range(1, k + 1))
        zeros_ok = all(u(-j) == 0 for j in range(1, c + 1))
        next_ok = u(-c - 1) == (-1) ** k * h[-1] != 0
        # u_k agrees with U on m >= 0 (sanity)
        agree = all(u(m) == T[k][m] for m in range(0, 6))
        if not (s == (2 * k) // 3 and zeros_ok and next_ok and agree):
            ok2 = False
            info.append((k, s, zeros_ok, next_ok, agree))
        if k >= 3 and min(h) >= 0:
            ok3 = False
    check('C2 deg h_k = floor(2k/3), u_k(-j)=0 for j<=ceil(k/3), u_k(-ceil(k/3)-1) = (-1)^k lc(h_k) != 0 (1<=k<=30)',
          ok2, str(info[:3]))
    check('C3 h_k has a negative coefficient (3<=k<=30)', ok3)

    # C4
    S = core.stirling2_table(7)
    ok4 = True
    for k in range(1, 8):
        B = list(product((0, 1), repeat=k))
        zero, one = tuple([0] * k), tuple([1] * k)
        cc = chain_counts([w for w in B if w not in (zero, one)])
        if any(cc.get(q - 1, 0) != math.factorial(q) * S[k][q] for q in range(1, k + 1)):
            ok4 = False
        row = {q: math.factorial(q) * S[k][q] for q in range(1, k + 1)}
        A = h_from_row(k, row)
        des = [0] * k
        for p in permutations(range(k)):
            des[sum(1 for i in range(k - 1) if p[i] > p[i + 1])] += 1
        while len(des) > 1 and des[-1] == 0:
            des.pop()
        # the numerator of sum_m (m+1)^k t^m, from its first terms
        num = [0] * (k + 1)
        for m in range(k + 1):
            num[m] = sum((-1) ** i * math.comb(k + 1, i) * (m - i + 1) ** k for i in range(m + 1))
        while len(num) > 1 and num[-1] == 0:
            num.pop()
        if not (A == des == num):
            ok4 = False
    check('C4 Boolean lattice: chains = q! S(k,q); h-numerator = descent polynomial = numerator of sum (m+1)^k t^m (1<=k<=7)', ok4)

    # C5
    def pat(t):
        r = {v: i + 1 for i, v in enumerate(sorted(set(t)))}
        return ''.join(str(r[v]) for v in t)
    bad5 = {pat(t) for t in product(range(4), repeat=3) if not core.good(*t)}
    good5 = {pat(t) for t in product(range(4), repeat=3) if core.good(*t)}
    check('C5 bad triples are exactly the consecutive patterns 112,121,123,132,213,231',
          bad5 == {'112', '121', '123', '132', '213', '231'} and not (bad5 & good5), str(sorted(bad5)))

    print('%d PASS, %d FAIL' % (6 - len(FAILS), len(FAILS)))
    return 1 if FAILS else 0


if __name__ == '__main__':
    sys.exit(main())
