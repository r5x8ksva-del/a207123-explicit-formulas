# -*- coding: utf-8 -*-
"""探索：b_i 的复根模长 sqrt(rho_i/i) 与 G_{i-1} 的收敛半径 1/rho_{i-1} 的比较（说明正性论证为何用不上）。"""
from decimal import Decimal, getcontext
getcontext().prec = 40
def rho(i):
    if i == 0:
        return Decimal(1)
    z = Decimal(i + 2)
    for _ in range(300):
        zn = z - (z*z*z - z*z - i) / (3*z*z - 2*z)
        if zn == z:
            break
        z = zn
    return z
allout = True
for i in range(1, 61):
    cr = (rho(i) / i).sqrt()          # |x| of complex roots of b_i
    rad = 1 / rho(i - 1)              # radius of convergence of G_{i-1}
    if not cr > rad:
        allout = False
    if i in (1, 2, 3, 4, 10, 20, 40, 60):
        print('i=%2d  |complex root of b_i| = %.4f   1/rho_{i-1} = %.4f   outside: %s' % (i, cr, rad, cr > rad))
print('all 1<=i<=60 outside the disc of convergence of G_{i-1}:', allout)
