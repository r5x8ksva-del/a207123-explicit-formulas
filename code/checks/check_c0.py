# -*- coding: utf-8 -*-
"""check_c0：主 Agent 自己的补充核对（基线数据、W_m、H 双和显式公式、c_m 闭式、U_3 单调三元组双射）。

所有「真值」都来自 core 里按原始定义实现的程序：
  U_fast_table / U_fast_column（高度 DP，第 1 节 (b) 的直接实现），U_multichain，a_direct（原题直接计数）。
"""
import os
import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import (U_fast_table, U_fast_column, U_height_table, U_multichain, a_direct, good,
                  PROMPT_TABLE, PROMPT_A3, binom, h_complete, stirling2_table)
from polylib import padd, pshift, pscale, P_poly, series_inv, series_mul, peval

results = []


def report(cid, ok, desc):
    results.append(ok)
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


t0 = time.time()
K, M = 60, 20
T = U_fast_table(K, M)

# c0-base-1：快速 DP 与第 1 节参考实现逐项一致
report('c0-base-ref', T == U_height_table(K, M), 'fast DP == 参考实现 U_list（k<=60, m<=20）')

# c0-base-2：第 2 节表、R_k、a_3(1..6)
ok = all(T[k][:7] == PROMPT_TABLE[k] for k in range(1, 11))
R = [T[k][1] for k in range(1, 11)]
ok = ok and R == [2, 4, 6, 9, 14, 21, 31, 46, 68, 100]
ok = ok and [a_direct(n, 3) for n in range(1, 7)] == PROMPT_A3
report('c0-base-data', ok, '第 2 节 U 表（k<=10,m<=6）、R_1..R_10、a_3(1..6) 与原始定义程序一致')

# c0-base-3：多重链定义与原题直接计数（小范围复核，主要范围见 check_c1）
ok = all(U_multichain(k, m) == T[k][m] for k in range(1, 8) for m in range(0, 6))
ok = ok and all(a_direct(n, k) == T[k][(n + 1) // 2] * T[k][n // 2] for k in range(1, 6) for n in range(0, 12))
report('c0-base-defs', ok, 'U_multichain==DP（k<=7,m<=5）；a_direct(n,k)==U(ceil)U(floor)（k<=5,n<=11）')

# c0-W：G_m = W_m / P_m，W_m = 1 + x^2 sum_{j=1}^m j P_{j-1}
ok = True
for m in range(0, M + 1):
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
    ser = series_mul(W, series_inv(P_poly(m), K + 1), K + 1)
    if [int(c) for c in ser] != [T[k][m] for k in range(K + 1)]:
        ok = False
report('c0-W', ok, 'G_m = W_m/P_m，W_m = 1 + x^2*sum_{j=1}^m j*P_{j-1}（展开到 x^60，m<=20）')


# c0-H：全正项双和显式公式
def U_H(k, m):
    tot = 0
    for s in range(0, k // 3 + 1):
        tot += h_complete(s, 0, m) * binom(k + m - 2 * s, k - 3 * s)
    n = k - 2
    if n >= 0:
        for j in range(1, m + 1):
            for s in range(0, n // 3 + 1):
                tot += j * h_complete(s, j, m) * binom(n + m - j - 2 * s, n - 3 * s)
    return tot


ok = all(U_H(k, m) == T[k][m] for k in range(0, K + 1) for m in range(0, M + 1))
report('c0-H', ok, 'U_k(m) = sum_s S(m+s,m)C(k+m-2s,k-3s) + sum_{j=1}^m j sum_s h_s(j..m) C(k-2+m-j-2s,k-2-3s)（k<=60,m<=20）')

S2 = stirling2_table(60)
ok = all(h_complete(s, 0, m) == S2[m + s][m] and h_complete(s, 1, m) == S2[m + s][m]
         for m in range(0, 20) for s in range(0, 40 - m + 1) if m + s <= 60)
report('c0-H-stirling', ok, 'h_s(0..m) = h_s(1..m) = S(m+s,m)（m<20, m+s<=60）')

# c0-H-broder：H(m,s,j) 的完全显式式（报告 ③ 中给出）
from math import factorial
ok = True
for m in range(0, 16):
    for j in range(0, m + 1):
        L = m - j
        for s in range(0, 20):
            num = sum((-1) ** (L - i) * binom(L, i) * (j + i) ** (s + L) for i in range(L + 1))
            if Fraction(num, factorial(L)) != h_complete(s, j, m):
                ok = False
report('c0-H-broder', ok, 'H(m,s,j) = (1/(m-j)!) sum_i (-1)^(m-j-i) C(m-j,i) (j+i)^(s+m-j)（m<=15, s<=19）')

# c0-H-rec：报告 ③ 中 H 的递推 H(m,s,j) = H(m,s,j+1) + j H(m,s-1,j)
ok = True
for m in range(0, 16):
    for s in range(0, 20):
        for j in range(0, m + 1):
            nxt = h_complete(s, j + 1, m) if j + 1 <= m else (1 if s == 0 else 0)
            prev = h_complete(s - 1, j, m) if s >= 1 else 0
            if h_complete(s, j, m) != nxt + j * prev:
                ok = False
report('c0-H-rec', ok, 'H(m,s,j) = H(m,s,j+1) + j*H(m,s-1,j)，H(m,s,m+1)=[s=0]（m<=15, s<=19）')

# c0-minorder：gcd(W_m,P_m)=1 的逐因子检验（W_m ≡ W_v mod b_v），v<=300
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'main_extra'))
from gcd_minimal_order import residue_W
from polylib import pgcd, b_poly
ok = True
for v in range(1, 301):
    r = residue_W(v)
    while r and r[-1] == 0:
        r.pop()
    if not r or len(pgcd(r, b_poly(v))) > 1:
        ok = False
report('c0-minorder', ok, '对 v=1..300：W_v mod b_v 非零且与 b_v 互素（配合 c1 的一般证明；最小递推阶 = 3m+1）')

# c0-cm：c_m 闭式（m=4 精确有理；其余高精度数值）
getcontext().prec = 80


def rho(m):
    y = Decimal(2)
    for _ in range(200):
        f = y * y * y - y * y - m
        y -= f / (3 * y * y - 2 * y)
    return y


def c_closed(m):
    r = rho(m)
    br = Decimal(1)
    fall = Decimal(1)
    for j in range(1, m + 1):
        fall *= (m - j + 1)
        br += j * fall / r ** (3 * j + 2)
    fact = Decimal(1)
    for i in range(2, m + 1):
        fact *= i
    return r ** (3 * m + 3) / (fact * (r * r + 3 * m)) * br


# m=4：rho=2，c_4 = 645/6，误差应随 (rho_3/2)^k 衰减
col4 = U_fast_column(4, 400)
err400 = abs(Fraction(col4[400], 2 ** 400) - Fraction(645, 6))
err300 = abs(Fraction(col4[300], 2 ** 300) - Fraction(645, 6))
report('c0-c4', err400 < Fraction(1, 10 ** 9) and err400 < err300 / 1000,
       'm=4：rho=2，|U_k(4)/2^k - 645/6| 在 k=300,400 为 %.2e, %.2e（单调衰减）' % (float(err300), float(err400)))

ok = True
worst = 0.0
for m in range(1, 9):
    col = U_fast_column(m, 600)
    r = rho(m)
    ratio = Decimal(col[600]) / r ** 600
    rel = abs(ratio / c_closed(m) - 1)
    worst = max(worst, float(rel))
    if rel > Decimal('1e-6'):
        ok = False
report('c0-cm', ok, 'c_m 闭式 vs U_600(m)/rho_m^600，m=1..8 最大相对误差 %.2e（数值检查，容差 1e-6）' % worst)

# c0-mono：U_3(m) = {0..m}^3 中单调三元组数，且给定映射是双射
ok = True
for m in range(0, 16):
    legal = [(a, b, c) for a in range(m + 1) for b in range(m + 1) for c in range(m + 1) if good(a, b, c)]
    mono = {(x, y, z) for x in range(m + 1) for y in range(m + 1) for z in range(m + 1)
            if (x <= y <= z) or (x >= y >= z)}

    def phi(t):
        a, b, c = t
        if b > c or (b == c and a >= b):
            return (a, b, c)
        if b == c and a < b:
            return (a, a, b)
        return (b, c, a)          # b < c <= a

    img = [phi(t) for t in legal]
    if len(legal) != T[3][m] or len(set(img)) != len(img) or set(img) != mono:
        ok = False
report('c0-mono', ok, 'U_3(m) = #单调三元组 = 2C(m+3,3)-(m+1)，且显式映射是双射（m<=15）')

ok = all(T[3][m] == 2 * binom(m + 3, 3) - (m + 1) and 3 * T[3][m] == (m + 1) * (m * m + 5 * m + 3) for m in range(0, M + 1))
report('c0-U3-poly', ok, 'U_3(m) = (m+1)(m^2+5m+3)/3（m<=20）')

npass = sum(results)
nfail = len(results) - npass
print('SUMMARY c0 pass=%d fail=%d (%.1fs)' % (npass, nfail, time.time() - t0))
sys.exit(0 if nfail == 0 else 1)
