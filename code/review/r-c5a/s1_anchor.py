# -*- coding: utf-8 -*-
"""s1：锚定复核者自己的 DP（不经 core），并把引理 1 递推表与 DP 对照。"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rlib import U_dp, U_rec_table, height_brute, matrix_brute

t0 = time.time()
PROMPT = {
    1: [1, 2, 3, 4, 5, 6, 7], 2: [1, 4, 9, 16, 25, 36, 49], 3: [1, 6, 17, 36, 65, 106, 161],
    4: [1, 9, 32, 80, 165, 301, 504], 5: [1, 14, 64, 192, 457, 938, 1736],
    6: [1, 21, 119, 419, 1136, 2604, 5306], 7: [1, 31, 214, 873, 2669, 6778, 15108],
    8: [1, 46, 388, 1837, 6334, 17802, 43326], 9: [1, 68, 694, 3788, 14666, 45488, 120650],
    10: [1, 100, 1222, 7629, 32971, 112349, 323647]}
cols = {m: U_dp(m, 10) for m in range(7)}
ok_prompt = all(cols[m][k] == PROMPT[k][m] for k in PROMPT for m in range(7))
print('prompt table (k<=10,m<=6) vs own DP:', ok_prompt)

ok_hb = all(U_dp(m, 7)[k] == height_brute(k, m) for k in range(0, 8) for m in range(0, 5))
print('height-vector brute force (k<=7, m<=4) vs own DP:', ok_hb)

ok_mat = True
for k in range(1, 6):
    for n in range(0, 21 // k + 1):
        if n * k > 20:
            continue
        a = matrix_brute(n, k)
        c = U_dp((n + 1) // 2, k)[k] * U_dp(n // 2, k)[k]
        if a != c:
            ok_mat = False
            print('  mismatch', n, k, a, c)
print('original matrix brute force a_k(n) (n*k<=20) == U_k(ceil)U_k(floor):', ok_mat)

T = U_rec_table(130, 130)
ok_rec = all(U_dp(m, 90) == [T[k][m] for k in range(91)] for m in range(0, 41))
ok_rec2 = all(U_dp(m, 60) == [T[k][m] for k in range(61)] for m in (50, 60, 70))
print('Lemma-1 recurrence table == own DP (k<=90, m<=40; plus m=50,60,70 with k<=60):', ok_rec and ok_rec2)
print('elapsed %.1fs' % (time.time() - t0))
