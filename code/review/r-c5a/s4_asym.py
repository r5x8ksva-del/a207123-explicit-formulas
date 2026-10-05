# -*- coding: utf-8 -*-
"""s4：V1、V2、V3 数值复算（自己的 DP + 自己的求根），并把 e_k<0 的范围扩大到 k<=2000。"""
import sys, os, time
from math import factorial
from decimal import Decimal, getcontext
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rlib import U_dp

getcontext().prec = 120
t0 = time.time()


def rho(j):
    if j == 0:
        return Decimal(1)
    y = Decimal(j) ** (Decimal(1) / 3) + Decimal('0.4')
    for _ in range(400):
        y2 = y - (y ** 3 - y ** 2 - j) / (3 * y * y - 2 * y)
        if abs(y2 - y) < Decimal(10) ** -115:
            break
        y = y2
    return y2


def cm(m):
    if m == 0:
        return Decimal(1)
    r = rho(m)
    e = sum(r ** (3 * i) / factorial(i) for i in range(m))
    return r * (r ** (3 * m + 1) / factorial(m) - e) / (3 * r - 2)


RH = {m: rho(m) for m in range(0, 20)}
CM = {m: cm(m) for m in range(0, 20)}

print('V1 recomputation (m<=8):')
allneg = True
for m in range(1, 9):
    K = 2000
    U = U_dp(m, K + 1)
    r, c = RH[m], CM[m]
    th = RH[m - 1] / r
    ka = CM[m - 1] * RH[m - 1] ** 3 / c
    e = [Decimal(U[k]) / (c * r ** k) - 1 for k in range(K + 2)]
    neg400 = all(x < 0 for x in e[:401])
    neg2000 = all(x < 0 for x in e[:K + 1])
    allneg = allneg and neg400 and neg2000
    r60 = e[61] / e[60]
    r400 = e[401] / e[400]
    two60 = (Decimal(U[60]) - c * r ** 60) / (-CM[m - 1] * RH[m - 1] ** 63)
    two400 = (Decimal(U[400]) - c * r ** 400) / (-CM[m - 1] * RH[m - 1] ** 403)
    print('  m=%d theta=%s kappa=%s e20=%s e40=%s e60=%s | rate60=%s rate400=%s |rate400-theta|=%s | two60=%s two400=%s | e<0 for k<=400:%s, k<=2000:%s'
          % (m, str(th)[:11], str(ka)[:6], str(+e[20])[:7] + str(e[20])[-4:], '%.3E' % e[40], '%.3E' % e[60],
             str(r60)[:8], str(r400)[:11], '%.2E' % abs(r400 - th), str(two60)[:8], str(two400)[:11], neg400, neg2000))

print('V2 recomputation (m=18):')
U = U_dp(18, 2001)
c18 = CM[18]
th = RH[17] / 3
ka = CM[17] * RH[17] ** 3 / c18
e = lambda k: Decimal(U[k]) / (c18 * Decimal(3) ** k) - 1
print('  rho_17=%s theta=%s kappa=%s e_1999=%.4E rate e2000/e1999=%s |rate-theta|=%.2E two-term=%s'
      % (str(RH[17])[:13], str(th)[:12], str(ka)[:7], e(1999), str(e(2000) / e(1999))[:12],
         abs(e(2000) / e(1999) - th), str(e(1999) / (-ka * th ** 1999))[:12]))

print('V3 recomputation (k=40):')
for m in (1, 2, 3):
    U = U_dp(m, 41)
    r = RH[m]
    th = RH[m - 1] / r
    ka = CM[m - 1] * RH[m - 1] ** 3 / CM[m]
    ratio = Decimal(U[41]) / Decimal(U[40]) / r - 1
    ratio40 = Decimal(U[40]) / Decimal(U[39]) / r - 1
    pred = ka * (1 - th) * th ** 40
    root = Decimal(U[40]) ** (Decimal(1) / 40) / r - 1
    lvl = Decimal(U[40]) / (CM[m] * r ** 40) - 1
    print('  m=%d: U41/U40/rho-1=%.4E (U40/U39: %.4E), theory kappa(1-theta)theta^40=%.4E, U40^(1/40)/rho-1=%.4E, U40/(c rho^40)-1=%.4E'
          % (m, ratio, ratio40, pred, root, lvl))

# 1-theta_m vs 1/(3m) 与 1/(3m+rho^2-1)
print('1-theta_m asymptotics:')
for m in (8, 100, 1000, 10000, 100000):
    r1, r0 = rho(m), rho(m - 1)
    d = 1 - r0 / r1
    print('  m=%d: (1-theta)*3m=%s ; (1-theta)*(3m+rho^2-1)=%s ; m^(-1/3)=%s'
          % (m, str(d * 3 * m)[:10], str(d * (3 * m + r1 * r1 - 1))[:10], str(Decimal(m) ** (Decimal(-1) / 3))[:8]))
print('elapsed %.1fs' % (time.time() - t0))
