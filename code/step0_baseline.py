# -*- coding: utf-8 -*-
"""第 0 步：跑通参考实现，并用三种独立方法对照第 2 节数据。"""
import sys, time
sys.path.insert(0, __file__.rsplit('\\', 1)[0] if '\\' in __file__ else '.')
from core import *

t0 = time.time()
ok = True

# 1) 参考实现 vs 第 2 节表
T = U_height_table(10, 6)
for k, row in PROMPT_TABLE.items():
    if T[k] != row:
        ok = False
        print('MISMATCH height-DP vs prompt table, k=', k, T[k], row)
print('height DP vs prompt table (k<=10, m<=6):', 'PASS' if ok else 'FAIL')

# 2) 多重链定义 vs 高度 DP
ok2 = True
for k in range(1, 9):
    for m in range(0, 6):
        if U_multichain(k, m) != T[k][m] if k <= 10 else True:
            ok2 = False
            print('MISMATCH multichain', k, m)
print('multichain vs height DP (k<=8, m<=5):', 'PASS' if ok2 else 'FAIL')

# 3) 原题定义直接数 a_k(n) vs U 的乘积公式
TT = U_height_table(8, 7)
ok3 = True
for k in range(1, 7):
    for n in range(0, 13):
        lhs = a_direct(n, k)
        rhs = TT[k][(n + 1) // 2] * TT[k][n // 2]
        if lhs != rhs:
            ok3 = False
            print('MISMATCH a_direct', k, n, lhs, rhs)
print('a_direct vs U(ceil)U(floor) (k<=6, n<=12):', 'PASS' if ok3 else 'FAIL')

# 4) 小规模暴力 vs a_direct
ok4 = True
for k in range(1, 5):
    for n in range(0, 6):
        if n * k > 20:
            continue
        if a_brute(n, k) != a_direct(n, k):
            ok4 = False
            print('MISMATCH brute', k, n)
print('a_brute vs a_direct (n*k<=20):', 'PASS' if ok4 else 'FAIL')

a3 = [a_direct(n, 3) for n in range(1, 7)]
print('a_3(1..6) =', a3, 'PASS' if a3 == PROMPT_A3 else 'FAIL')
print('elapsed %.1fs' % (time.time() - t0))
