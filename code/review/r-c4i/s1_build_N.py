# -*- coding: utf-8 -*-
"""s1：独立构造 N(k,q) 表（k<=K），并锚定到原始定义；结果存 pickle 供后续脚本使用。
锚定：
  (1) U_column（快 DP）== U_slow（逐个枚举高度向量，字面检查三元组），k<=7, m<=4
  (2) U == 0/1 矩阵暴力（列单调 + 行规则），k<=5, m<=3
  (3) U == 提示词第 2 节校验表（k<=10, m<=6）
  (4) N（容斥）== 按定义 DFS 枚举满射合法词，k<=11
"""
import sys, os, time, pickle
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rlib import U_column, U_slow, U_table, N_table_from_U, N_brute_surj, U_matrix_brute

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass

K = int(sys.argv[1]) if len(sys.argv) > 1 else 100
t0 = time.time()
PROMPT = {
    1: [1, 2, 3, 4, 5, 6, 7], 2: [1, 4, 9, 16, 25, 36, 49], 3: [1, 6, 17, 36, 65, 106, 161],
    4: [1, 9, 32, 80, 165, 301, 504], 5: [1, 14, 64, 192, 457, 938, 1736],
    6: [1, 21, 119, 419, 1136, 2604, 5306], 7: [1, 31, 214, 873, 2669, 6778, 15108],
    8: [1, 46, 388, 1837, 6334, 17802, 43326], 9: [1, 68, 694, 3788, 14666, 45488, 120650],
    10: [1, 100, 1222, 7629, 32971, 112349, 323647]}

ok1 = all(U_column(m, 7)[k] == U_slow(k, m) for m in range(0, 5) for k in range(0, 8))
print('anchor1 U_column == U_slow (k<=7,m<=4):', ok1)
ok2 = all(U_column(m, 5)[k] == U_matrix_brute(k, m) for m in range(0, 4) for k in range(1, 6))
print('anchor2 U_column == 0/1 matrix brute (k<=5,m<=3):', ok2)
ok3 = all(U_column(m, 10)[k] == PROMPT[k][m] for m in range(0, 7) for k in range(1, 11))
print('anchor3 U_column == prompt table (k<=10,m<=6):', ok3)

T = U_table(K, K - 1)
print('U table built K=%d in %.1fs' % (K, time.time() - t0))
N = N_table_from_U(T, K)
print('N table built in %.1fs' % (time.time() - t0))
ok4 = True
for k in range(0, 12):
    for q in range(0, k + 1):
        if N_brute_surj(k, q) != N[k][q]:
            ok4 = False
            print('  mismatch', k, q)
print('anchor4 N(incl-excl) == DFS surjective words (k<=11):', ok4)
# prompt N triangle rows (C3) k<=10
TRI = {1: [1], 2: [1, 2], 3: [1, 4, 2], 4: [1, 7, 8, 2], 5: [1, 12, 25, 16, 2], 6: [1, 19, 59, 65, 26, 2],
       7: [1, 29, 124, 199, 139, 38, 2], 8: [1, 44, 253, 557, 574, 277, 52, 2],
       9: [1, 66, 493, 1416, 1991, 1446, 509, 68, 2], 10: [1, 98, 925, 3337, 6051, 6012, 3257, 871, 86, 2]}
ok5 = all(N[k][q] == TRI[k][q - 1] for k in TRI for q in range(1, k + 1))
print('anchor5 N == prompt triangle (k<=10):', ok5)
with open(os.path.join(HERE, 'N_K%d.pkl' % K), 'wb') as fh:
    pickle.dump({'K': K, 'N': N}, fh)
print('ALL_ANCHORS_OK' if (ok1 and ok2 and ok3 and ok4 and ok5) else 'ANCHOR_FAIL')
print('runtime %.1fs' % (time.time() - t0))
