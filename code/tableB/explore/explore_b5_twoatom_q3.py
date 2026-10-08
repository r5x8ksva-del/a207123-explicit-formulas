# -*- coding: utf-8 -*-
"""探索（2026-10-08）：解出 N(k,3) 的两原子式（纤维 1 取 (-8,2)，纤维 2 取 (-3,2)），并核对 k<=60。"""
import os, sys
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE))))
from check_b4 import c_seq  # noqa: E402
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), ''))
from core import U_fast_table  # noqa: E402
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
K = 60
TU = U_fast_table(K, 3)
N3 = [None] + [3 - 3 * TU[k][1] + TU[k][2] for k in range(1, K + 1)]
c1, c2 = c_seq(1, K + 20), c_seq(2, K + 20)
cv = lambda cs, n: cs[n] if n >= 0 else 0
for (p1, p2) in [((-8, 2), (-3, 2)), ((-5, 14), (-1, 9))]:
    atoms = [lambda k: 1, lambda k, a=p1[0]: cv(c1, k - a), lambda k, a=p1[1]: cv(c1, k - a),
             lambda k, a=p2[0]: cv(c2, k - a), lambda k, a=p2[1]: cv(c2, k - a)]
    rows = [[Fr(f(k)) for f in atoms] + [Fr(N3[k])] for k in range(30, 40)]
    n = 5
    A = [r[:] for r in rows]
    piv = []
    r_ = 0
    for col in range(n):
        p = next((i for i in range(r_, len(A)) if A[i][col] != 0), None)
        if p is None: continue
        A[r_], A[p] = A[p], A[r_]
        pv = A[r_][col]; A[r_] = [x / pv for x in A[r_]]
        for i in range(len(A)):
            if i != r_ and A[i][col] != 0:
                f = A[i][col]; A[i] = [x - f * y for x, y in zip(A[i], A[r_])]
        piv.append(col); r_ += 1
    sol = [A[i][-1] for i in range(r_)]
    bad = [k for k in range(1, K + 1) if sum(s * f(k) for s, f in zip(sol, atoms)) != N3[k]]
    print('纤维 1 %s、纤维 2 %s：秩 %d，系数 %s；1<=k<=60 中不符的 k：%s' % (p1, p2, r_, [str(s) for s in sol], bad))
