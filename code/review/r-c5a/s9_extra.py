# -*- coding: utf-8 -*-
"""s9: notes §4.6 general g.f. for [t^i]h_k (i<=4,k<=60) and §4.9 root data at k=36."""
import sys, os
from fractions import Fraction as Fr
from math import comb, factorial
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rlib import U_rec_table, peval, trim
K = 60
T = U_rec_table(K + 5, K + 5)
H = {k: trim([sum((-1) ** (i - j) * comb(k + 1, i - j) * T[k][j] for j in range(i + 1)) for i in range(k + 1)]) for k in range(K + 1)}
# sum_k h_{k,i} x^k = sum_r (-1)^r x^{r-1}/r! (d/dx)^r [x G_{i-r}(x)] ; coefficient of x^k: sum_r (-1)^r C(k+1,r) U_k(i-r)
ok = True
for i in range(0, 5):
    for k in range(0, K + 1):
        # series side: [x^k] x^{r-1}/r! D^r (sum_n U_n(j) x^{n+1}) = C(k+1,r) U_k(j)
        s = sum((-1) ** r * comb(k + 1, r) * T[k][i - r] for r in range(0, i + 1))
        hk = H[k][i] if i < len(H[k]) else 0
        if s != hk:
            ok = False
print('notes 4.6 general g.f. for [t^i]h_k, i<=4, k<=60:', ok)
# k=36 roots via numpy (approximate, for the descriptive data only)
import numpy as np
h = H[36]
r = np.roots([float(c) for c in reversed(h)])
re = np.sort(r.real[np.abs(r.imag) < 1e-6])
neg = re[re < 0]
print('k=36 (numpy, descriptive): #real roots=%d of deg %d; max root=%.2f; min root=%.2f; root closest to 0 = %.3e; -1/h_{k,1} = %.3e'
      % (len(re), len(h) - 1, re.max(), re.min(), neg.max(), -1.0 / h[1]))
