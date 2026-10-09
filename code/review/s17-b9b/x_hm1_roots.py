# -*- coding: utf-8 -*-
"""探索（信息性）：h_k(−1) 的变号次数与 (−1,0) 中根数 N_k 的关系（notes/18 §3.2 的说法）。
N_k 用 Descartes 计数（h_k 全实根（A19）时精确）。"""
import os, sys, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from s17_common import t17_full
from rootlib import desc_count
sys.stdout.reconfigure(encoding='utf-8')
t0 = time.time()
vals = {}
N = {}
for k, h in t17_full(1000):
    vals[k] = sum(c if i % 2 == 0 else -c for i, c in enumerate(h))
    if k in (3, 4, 5, 100, 200, 500, 1000):
        N[k] = desc_count(h, -1, 0)
ch = sum(1 for k in range(3, 1000) if (vals[k] > 0) != (vals[k + 1] > 0))
F1 = (math.atan(2 / math.pi) + math.pi / 2) / (3 * math.pi)
print('h_k(-1) sign changes for 3<=k<=1000:', ch)
print('N_k in (-1,0):', N, '; N_k - k F(1):', {k: round(v - k * F1, 2) for k, v in N.items()})
print('N_1000 - N_3 =', N[1000] - N[3], ' (equals the number of sign changes iff N_{k+1}-N_k in {0,1} for all k)')
print('parity check sign(h_k(-1)) = (-1)^{N_k}:', all((vals[k] > 0) == (N[k] % 2 == 0) for k in N))
print('%.1fs' % (time.time() - t0))
