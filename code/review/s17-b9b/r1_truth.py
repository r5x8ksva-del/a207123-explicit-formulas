# -*- coding: utf-8 -*-
"""s17-b9b r1：真值与三种 h 算法的互相对照（不 import 项目代码）。
  r1-dp     逐个枚举 = 朴素 DP = U 三项递推（小范围）；与原始任务说明第 2 节的校验表一致
  r1-N      N 三角：U_k(m)=Σ_q C(m+1,q)N(k,q)（1<=k<=60，m<=30）
  r1-h3     h_k 三种算法逐项相等：U 的反演、N 公式、自写 T1.7（完整多项式，k<=90）；deg h_k=⌊2k/3⌋；h_k(1)=2（k>=2）
用法：py -3.14 code/review/s17-b9b/r1_truth.py
"""
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from s17_common import brute_U, pair_dp_U, U_rows, N_rows, h_from_N, t17_full, binom_row_next, h_from_U  # noqa: E402

sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


t0 = time.time()
# ---- r1-dp
ok = True
for m in range(0, 4):
    pd = pair_dp_U(8, m)
    for k in range(0, 9):
        if brute_U(k, m) != pd[k]:
            ok = False
Ut = {}
for k, row in U_rows(40, 8):
    Ut[k] = row
for m in range(0, 9):
    pd = pair_dp_U(40, m)
    for k in range(0, 41):
        if pd[k] != Ut[k][m]:
            ok = False
# 原始任务说明第 2 节的校验表（k=1..10，m=0..6）
TABLE = {1: [1, 2, 3, 4, 5, 6, 7], 2: [1, 4, 9, 16, 25, 36, 49], 3: [1, 6, 17, 36, 65, 106, 161],
         4: [1, 9, 32, 80, 165, 301, 504], 5: [1, 14, 64, 192, 457, 938, 1736],
         6: [1, 21, 119, 419, 1136, 2604, 5306], 7: [1, 31, 214, 873, 2669, 6778, 15108],
         8: [1, 46, 388, 1837, 6334, 17802, 43326], 9: [1, 68, 694, 3788, 14666, 45488, 120650],
         10: [1, 100, 1222, 7629, 32971, 112349, 323647]}
okT = all(Ut[k][:7] == TABLE[k] for k in TABLE)
report('r1-dp', ok and okT, '逐个枚举 = 朴素 DP（k<=8，m<=3）；朴素 DP = 三项递推（k<=40，m<=8）；三项递推 = 任务说明第 2 节校验表（k<=10，m<=6）')

# ---- r1-N
Ut60 = {k: row for k, row in U_rows(60, 30)}
Nt = {k: row for k, row in N_rows(60, 40)}
ok = True
for k in range(1, 61):
    for m in range(0, 31):
        v = sum(math.comb(m + 1, q) * Nt[k][q] for q in range(1, 41))
        ok = ok and v == Ut60[k][m]
okpos = all(Nt[k][q] > 0 for k in range(1, 41) for q in range(1, k + 1)) and all(Nt[k][k] == 2 for k in range(2, 41))
report('r1-N', ok and okpos, 'U_k(m)=Σ_q C(m+1,q)N(k,q)（1<=k<=60，0<=m<=30）；N(k,q)>0（1<=q<=k<=40），N(k,k)=2（2<=k<=40）')

# ---- r1-h3
K = 90
full = {k: h for k, h in t17_full(K)}
Uf = {k: row for k, row in U_rows(K, 70)}
Nf = {k: row for k, row in N_rows(K, 70)}
ok, okdeg, okone = True, True, True
B = [1] + [0] * 70           # C(1,r)，k=0
B[1] = 1
for k in range(0, K + 1):
    if k > 0:
        B = binom_row_next(B)
    Bs = [(-b if r & 1 else b) for r, b in enumerate(B)]
    d = len(full[k]) - 1
    okdeg = okdeg and d == (2 * k) // 3
    if k >= 2:
        okone = okone and sum(full[k]) == 2
    hu = h_from_U(Uf[k], Bs, min(70, d + 2))
    for i in range(min(70, d + 2) + 1):
        hv_full = full[k][i] if i <= d else 0
        hn = 1 if (k == 0 and i == 0) else (0 if k == 0 else h_from_N(k, Nf[k], i))
        ok = ok and hu[i] == hv_full == hn
report('r1-h3', ok and okdeg and okone,
       'h_{k,i} 的三种算法逐项相等（U 的反演、N 公式、自写 T1.7；0<=k<=90，i<=min(70,deg+2)）；deg h_k=⌊2k/3⌋；h_k(1)=2（2<=k<=90）')

print('# elapsed %.1fs' % (time.time() - t0))
print('SUMMARY s17-r1 pass=%d fail=%d' % (RES.count(True), RES.count(False)))
