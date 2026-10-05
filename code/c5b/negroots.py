# -*- coding: utf-8 -*-
"""c5b 探索：U_k 在负整数处的零点（解释 OEIS 偏移 n=m+1、n=m+2 的来源）与 mu_{P_k}(0,1)。"""
import os, sys
from math import factorial
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_fast_table, N_from_U, allowed_rows

K = 30
T = U_fast_table(K, K)
def gbinom(x, q):  # 广义二项式 C(x,q)，x 可为负整数
    r = 1
    for i in range(q):
        r = r * (x - i)
    return r // factorial(q)
def Uneg(k, m):  # 由二项式基在任意整数 m 处求多项式值
    if k == 0:
        return 1
    return sum(N_from_U(T, k, q) * gbinom(m + 1, q) for q in range(1, k + 1))
ok = True
for k in range(1, K + 1):
    J = (k + 2) // 3
    zs = [j for j in range(1, K + 2) if Uneg(k, -j) == 0]
    if zs != list(range(1, J + 1)):
        print('k=%d zeros at -j for j in %s ; predicted 1..%d' % (k, zs, J))
        ok = False
for j in range(1, 11):
    v = Uneg(3 * j, -j - 1)
    if v != factorial(j):
        print('U_%d(-%d) = %d != %d!' % (3 * j, j + 1, v, j)); ok = False
print('zeros exactly at m=-1..-floor((k+2)/3) for 1<=k<=30, and U_{3j}(-j-1)=j! for j<=10:', ok)
# Moebius mu_{P_k}(0,1) vs U_k(-2)
def mobius_bottom_top(k):
    E = sorted(allowed_rows(k), key=sum)
    le = lambda x, y: all(a <= b for a, b in zip(x, y))
    bot = E[0]; mu = {bot: 1}
    for x in E[1:]:
        mu[x] = -sum(mu[y] for y in mu if le(y, x) and y != x)
    return mu[tuple([1] * k)]
print('mu_{P_k}(0,1), k=1..9:', [mobius_bottom_top(k) for k in range(1, 10)])
print('U_k(-2),       k=1..9:', [Uneg(k, -2) for k in range(1, 10)])
