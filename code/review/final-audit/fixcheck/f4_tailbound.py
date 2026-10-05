# -*- coding: utf-8 -*-
"""只读：按 c3a 尾项界引理（check_c3a.S_tail_bound 同式，自抄）计算 (x,t)=(3/5,-1/2)、M=400 的严格尾项界，
看是否为 3.529e-118；并给出精确部分和前 20 位。"""
from fractions import Fraction as F
from decimal import Decimal, getcontext
getcontext().prec = 40
x, t, M = F(3, 5), F(-1, 2), 400
G_prev, tot, tp, Gs = F(1), F(0), F(1), []
for m in range(M + 1):
    b = 1 - x - m * x ** 3
    G = (G_prev + m * x * x) / b
    Gs.append(G); tot += tp * G; G_prev = G; tp *= t
lam = (1 - x) / x ** 3
m0 = 0
while not (m0 > lam and x ** 3 * (m0 + 1 - lam) >= 2):
    m0 += 1
c1 = 1 / (x ** 3 * (m0 + 1 - lam))
c2 = (m0 + 1) / (x * (m0 + 1 - lam))
mx = max(abs(g) for g in Gs[m0:M + 1])
B = max(mx, c2 / (1 - c1))
tb = B * abs(t) ** (M + 1) / (1 - abs(t))
d = lambda q: Decimal(q.numerator) / Decimal(q.denominator)
print('lambda=', d(lam), 'm0=', m0, 'c1=', d(c1), 'c2=', d(c2), 'max|G_m| (m0..M)=', d(mx), 'B=', d(B))
print('tail bound =', '%.6e' % float(tb), ' (> 3.5e-118?)', tb > F(35, 10 ** 119), ' (<= 3.53e-118?)', tb <= F(353, 10 ** 120))
print('partial sum =', d(tot))
