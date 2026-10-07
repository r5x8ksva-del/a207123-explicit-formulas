# -*- coding: utf-8 -*-
"""表 B 的 B11 探索：缺陷 e_d(k)=D(k,d)-p_d(k) 在窗口 [d-1, 2d+1] 的值，与 2(2d-1)!! 比较。只做观察。"""
import sys
from fractions import Fraction
from math import factorial
sys.path.insert(0, __file__.rsplit('explore', 1)[0] + 'explore')
from explore_b11_variance import N_table, interp_coeffs  # noqa: E402
from explore_b11_hstar import peval  # noqa: E402

D = int(sys.argv[1]) if len(sys.argv) > 1 else 12
N = N_table(4 * D + 8)
for d in range(1, D + 1):
    xs = list(range(2 * d + 2, 4 * d + 3))
    c = interp_coeffs(xs, [N[k][k - d] for k in xs])
    H = 2
    for i in range(1, 2 * d, 2):
        H *= i
    row = []
    for k in range(d - 1, 3 * d):
        p = peval(c, k)
        Dk = N[k][k - d] if k - d >= 0 else 0
        e = Dk - p
        row.append((k, int(p), int(e)))
    sgn = ''.join('-' if p < 0 else ('L' if p <= H else 'H') for (k, p, e) in row)
    print('d=%2d H=2(2d-1)!!=%d  window[d-1,3d-1] p-class: %s' % (d, H, sgn))
    print('     e_d(2d+1-i)/((d+1)!) for i=0..d+2:', [str(Fraction(int(N[2*d+1-i][d+1-i]) - int(peval(c, 2*d+1-i)), factorial(d+1))) if d+1-i >= 0 else '-' for i in range(0, d + 3)])
