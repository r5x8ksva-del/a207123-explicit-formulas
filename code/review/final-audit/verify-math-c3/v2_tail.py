# -*- coding: utf-8 -*-
"""verify-math-c3 / v2：独立重算 T3.4(3) 反例 (x,t)=(3/5,-1/2) 的部分和与尾项界（只读，不 import check 模块）。

G_m 按引理 1 推出的 (C2) 递推 G_m = (G_{m-1} + m x^2)/b_m（b_m = 1-x-m x^3，G_{-1}=1）精确计算，
并先用 core.U_fast_table 在小范围内对照 G_m 的 x 级数，确认递推本身与原始定义一致。
"""
import os, sys
from fractions import Fraction as Fr
from decimal import Decimal, getcontext

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_table

getcontext().prec = 40

# (a) 递推 G_m 的 x 级数 == 原始定义的 DP（k<=30, m<=8）
K, M = 30, 8
T = U_fast_table(K, M)
def series_div(num, den, K):
    out = [Fr(0)] * (K + 1)
    for k in range(K + 1):
        s = num[k] if k < len(num) else Fr(0)
        for i in range(1, min(k, len(den) - 1) + 1):
            s -= den[i] * out[k - i]
        out[k] = s / den[0]
    return out
Gs = [Fr(1)] + [Fr(0)] * K   # G_{-1} = 1
ok = True
for m in range(M + 1):
    num = Gs[:]
    if K >= 2:
        num[2] += m
    den = [Fr(1), Fr(-1), Fr(0), Fr(-m)]
    Gs = series_div(num, den, K)
    ok &= all(Gs[k] == T[k][m] for k in range(K + 1))
print('[a] recurrence G_m=(G_{m-1}+m x^2)/b_m reproduces U_fast_table, k<=30, m<=8:', ok)

# (b) 精确部分和 m<=400 at x=3/5, t=-1/2
x, t = Fr(3, 5), Fr(-1, 2)
lam = (1 - x) / x ** 3
G_prev = Fr(1)
tot = Fr(0)
tp = Fr(1)
G = []
for m in range(0, 401):
    b = 1 - x - m * x ** 3
    g = (G_prev + m * x * x) / b
    G.append(g)
    tot += tp * g
    G_prev = g
    tp *= t
print('[b] lambda =', lam, '=', float(lam))
print('[b] exact partial sum m<=400 =', Decimal(tot.numerator) / Decimal(tot.denominator))

# (c) check 模块（S_tail_bound）的界：m0、c1、c2、B 按同一公式独立复写
m0 = 0
while not (m0 > lam and x ** 3 * (m0 + 1 - lam) >= 2):
    m0 += 1
c1 = 1 / (x ** 3 * (m0 + 1 - lam))
c2 = Fr(m0 + 1) / (x * (m0 + 1 - lam))
maxG = max(abs(g) for g in G[m0:401])
B = max(maxG, c2 / (1 - c1))
at = abs(t)
bound = B * at ** 401 / (1 - at)
argmax = max(range(m0, 401), key=lambda m: abs(G[m]))
print('[c] m0=%d c1=%.6f c2=%.6f c2/(1-c1)=%.6f max|G_m| (m0..400)=%.6f at m=%d' %
      (m0, float(c1), float(c2), float(c2 / (1 - c1)), float(maxG), argmax))
bD = Decimal(bound.numerator) / Decimal(bound.denominator)
print('[c] check-style rigorous tail bound =', bD, ' ; %.1e formatting ->', '%.1e' % float(bound))
print('[c] bound <= 3.5e-118 ?', bound <= Fr(35, 10 ** 119), '; bound <= 3.53e-118 ?', bound <= Fr(353, 10 ** 120))

# (d) 更紧的界：对 m>400 用 m=401 处的 c1', c2'（单调性同上）
c1p = 1 / (x ** 3 * (401 - lam))
c2p = Fr(401) / (x * (401 - lam))
Bp = max(abs(G[400]), c2p / (1 - c1p))
bound2 = Bp * at ** 401 / (1 - at)
print('[d] |G_400|=%.6f, c2\'/(1-c1\')=%.6f, tighter bound = %.4e' % (float(abs(G[400])), float(c2p / (1 - c1p)), float(bound2)))

# (e) 直接把和推到 m<=700，看实际尾项大小
G_prev2 = G[400]
tail = Fr(0)
tp = t ** 401
for m in range(401, 701):
    b = 1 - x - m * x ** 3
    g = (G_prev2 + m * x * x) / b
    tail += tp * g
    G_prev2 = g
    tp *= t
print('[e] sum_{401<=m<=700} t^m G_m = %.6e (actual tail magnitude ~ this)' % float(tail))
print('[e] S < 0 conclusion holds with either bound:', tot + bound < 0, tot + bound2 < 0)
