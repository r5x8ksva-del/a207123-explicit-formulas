# -*- coding: utf-8 -*-
"""第 1 步：主 Agent 自己先快速核对几条新推导（正式核对由各子任务与 verify_all.py 完成）。"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import *
from polylib import *

K, M = 40, 12
T = U_fast_table(K, M)

# (1) 块分解母函数 G_m = W_m / P_m，W_m = 1 + x^2 * sum_{j=1}^m j P_{j-1}
ok = True
for m in range(0, M + 1):
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
    ser = series_mul(W, series_inv(P_poly(m), K + 1), K + 1)
    if [int(c) for c in ser] != [T[k][m] for k in range(K + 1)]:
        ok = False; print('G_m=W_m/P_m fails at m=', m)
print('(1) G_m = W_m/P_m  k<=%d m<=%d:' % (K, M), 'PASS' if ok else 'FAIL')

# (2) 显式双和：U_k(m) = sum_s S(m+s,m) C(k+m-2s, k-3s) + sum_{j=1}^m j sum_s h_s(j..m) C(k-2+m-j-2s, k-2-3s)
def U_explicit(k, m):
    tot = 0
    for s in range(0, k // 3 + 1):
        tot += h_complete(s, 0, m) * binom(k + m - 2 * s, k - 3 * s)
    for j in range(1, m + 1):
        n = k - 2
        for s in range(0, max(n, -1) // 3 + 1 if n >= 0 else 0):
            tot += j * h_complete(s, j, m) * binom(n + m - j - 2 * s, n - 3 * s)
    return tot

ok = all(U_explicit(k, m) == T[k][m] for k in range(0, K + 1) for m in range(0, M + 1))
print('(2) explicit double sum  k<=%d m<=%d:' % (K, M), 'PASS' if ok else 'FAIL')

# (3) N(k,q)：DFS 定义 vs 容斥 vs 提示词三角
PROMPT_N = {1: [1], 2: [1, 2], 3: [1, 4, 2], 4: [1, 7, 8, 2], 5: [1, 12, 25, 16, 2],
            6: [1, 19, 59, 65, 26, 2], 7: [1, 29, 124, 199, 139, 38, 2],
            8: [1, 44, 253, 557, 574, 277, 52, 2], 9: [1, 66, 493, 1416, 1991, 1446, 509, 68, 2],
            10: [1, 98, 925, 3337, 6051, 6012, 3257, 871, 86, 2]}
ok = True
for k in range(1, 11):
    ie = [N_from_U(T, k, q) for q in range(1, k + 1)]
    if ie != PROMPT_N[k]:
        ok = False; print('N incl-excl vs prompt fails k=', k, ie)
for k in range(1, 9):
    br = N_brute(k)
    if [br.get(q, 0) for q in range(1, k + 1)] != PROMPT_N[k]:
        ok = False; print('N brute vs prompt fails k=', k)
print('(3) N triangle: brute(k<=8), incl-excl(k<=10) vs prompt:', 'PASS' if ok else 'FAIL')

# (4) (C7) 分子递推 Num_q = (x+2(q-1)x^3) Num_{q-1} + (q-1) x^3 b_{q-2} Num_{q-2}
def Nq_series(q, n):
    return [N_from_U(T, k, q) for k in range(n)]
Num = {}
ok = True
for q in range(1, 13):
    ser = Nq_series(q, K + 1)
    prod = series_mul(ser, P_poly(q - 1), K + 1)
    prod = trim(prod)
    if len(prod) > 3 * q - 1:   # 应为次数 3q-2 的多项式
        ok = False; print('not poly q=', q)
    Num[q] = prod
for q in range(3, 13):
    rhs = padd(pmul([0, 1, 0, 2 * (q - 1)], Num[q - 1]), pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), Num[q - 2]))
    if trim(rhs) != trim(Num[q]):
        ok = False; print('Num recurrence fails q=', q)
print('(4) (C7) numerators poly (q<=12) + 3-term recurrence (3<=q<=12):', 'PASS' if ok else 'FAIL')
print('    Num_5 =', Num[5])
