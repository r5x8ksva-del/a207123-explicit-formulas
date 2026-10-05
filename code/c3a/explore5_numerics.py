# -*- coding: utf-8 -*-
"""探索 5：解析版本的数值证据（decimal）。"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import getcontext, Decimal as D
from fractions import Fraction as Fr
from numerics import *

pts = [(Fr(3, 5), Fr(-1, 2)), (Fr(2, 5), Fr(-3, 10)), (Fr(3, 10), Fr(-1, 10)), (Fr(21, 100), Fr(-1, 20))]
for prec in (60,):
    getcontext().prec = prec
    PI = pi_dec()
    for (x, t) in pts:
        t0 = time.time()
        lam = (1 - x) / x ** 3
        I0, e0, l0 = I_val(x, t, with_g=False)
        S0, m0 = S_val(x, t, with_g=False)
        G1 = gamma_neg_reflect(dec(lam), PI)
        G2 = K_val(x, with_g=False)
        gap0 = predicted_gap(x, t, G1)
        I1, e1, l1 = I_val(x, t, with_g=True)
        S1, m1 = S_val(x, t, with_g=True)
        Kx = K_val(x, with_g=True)
        gap1 = predicted_gap(x, t, Kx)
        print('x=%s t=%s lambda=%.6f  (%.1fs)' % (x, t, float(lam), time.time() - t0))
        print('   I0      = %s  (quad err est %s, level %d)' % (I0, e0, l0))
        print('   S0      = %s  (terms %d)' % (S0, m0))
        print('   I0-S0   = %s' % (I0 - S0))
        print('   pred    = %s   [x^-3 Gamma(-lam) e^a a^lam]' % gap0)
        print('   Gamma(-lam) reflect = %s ; regularized = %s ; diff %s' % (G1, G2, G1 - G2))
        print('   I       = %s  (quad err est %s, level %d)' % (I1, e1, l1))
        print('   S       = %s  (terms %d)' % (S1, m1))
        print('   I-S     = %s' % (I1 - S1))
        print('   pred    = %s   [x^-3 K(x) e^a a^lam], K = %s' % (gap1, Kx))
        r0 = (I0 - S0 - gap0)
        r1 = (I1 - S1 - gap1)
        print('   residuals: const %s ; full %s' % (r0, r1))
