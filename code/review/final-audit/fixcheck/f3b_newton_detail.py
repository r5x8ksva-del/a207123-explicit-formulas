# -*- coding: utf-8 -*-
"""只读：打印 d=2 的基点 2d+2 Newton 系数（应为 65,74,64,30,6），以及 d=68,69,70,74 在基点 2d+1 的前几个 Newton 系数。"""
import sys
from math import factorial
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
sys.path.insert(0, ROOT + r'\code')
import core
DMAX = 80
K = 4 * DMAX + 4
N = [[0] * (K + 2) for _ in range(K + 1)]
N[0][0] = 1; N[1][1] = 1; N[2][1] = 1; N[2][2] = 2
for k in range(3, K + 1):
    for q in range(1, k + 1):
        r = q - 1
        v = N[k - 1][r] + N[k - 1][r + 1]
        if r >= 1:
            v += r * (N[k - 3][r - 1] + 2 * N[k - 3][r] + N[k - 3][r + 1])
        N[k][q] = v
D = lambda k, d: N[k][k - d] if 0 <= k - d <= k else 0
def newton(d):
    vals = [D(2 * d + 2 + j, d) for j in range(2 * d + 1)]
    T, cur = [], vals[:]
    for i in range(2 * d + 1):
        T.append(cur[0]); cur = [cur[j + 1] - cur[j] for j in range(len(cur) - 1)]
    Nn = [sum((-1) ** (j - i) * T[j] for j in range(i, 2 * d + 1)) for i in range(2 * d + 1)]
    return T, Nn
print('d=2 base 2d+2:', newton(2)[0])
print('d=1 p_1(k)=k^2-k-4 check D(4..8,1):', [D(k, 1) for k in range(4, 9)], [k*k-k-4 for k in range(4, 9)])
for d in (67, 68, 69, 70, 72, 74, 76):
    T, Nn = newton(d)
    print('d=%d base 2d+1: N_0=%.3e N_1=%.3e N_2=%.3e  (d+1)!=%.3e  D(2d+2,d)=%.3e' % (d, Nn[0], Nn[1], Nn[2], factorial(d + 1), D(2 * d + 2, d)))
