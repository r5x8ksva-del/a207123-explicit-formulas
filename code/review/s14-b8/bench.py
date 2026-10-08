# -*- coding: utf-8 -*-
"""s14-b8：估算几个重计算的速度（只跑很小的规模）。"""
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import b8lib as L  # noqa: E402

# 1. 模 3 素数的 G_{-j} 递推，K=300，跑 200000 步
K = 300
P = np.array([2147483647, 2147483579, 2147483629], dtype=np.int64)[:, None]
g = np.zeros((3, K + 1), dtype=np.int64)
g[:, 0] = 1
t = time.time()
for j in range(1, 200001):
    s3 = j * g[:, :-3]
    g[:, 1:] -= g[:, :-1]
    g[:, 3:] += s3
    g[:, 2] += j
    np.remainder(g, P, out=g)
    seg = g[0, 200:301]
    if not seg.all():
        pass
dt = time.time() - t
print('G-run mod 3 primes: 200000 steps %.2fs -> 13.45M steps est %.0fs' % (dt, dt / 200000 * 13.45e6))

# 2. 精确 G 递推 K=100，跑 20000 步
t = time.time()
cnt = 0
for j, gg in L.gneg_iter(100, 20000):
    cnt += 1
dt = time.time() - t
print('exact G K=100: 20000 steps %.2fs -> 494702 steps est %.0fs' % (dt, dt / 20000 * 494702))

# 3. 按定义的精确 DP：m=50，K=50
t = time.time()
L.U_dp_exact_row(50, 50)
print('exact DP m=50 K=50: %.2fs' % (time.time() - t))

# 4. 模 P 的 DP：m=300，K=300
t = time.time()
L.U_dp_modp_all(300, 0, 2147483647)
t0 = time.time()
V = np.zeros(1)
n = 301
cnt = np.ones((n, n), dtype=np.int64)
idx = np.arange(n)
Mx = np.maximum.outer(idx, idx)
Bi = np.broadcast_to(idx[:, None], (n, n))
PP = 2147483647
for k in range(3, 301):
    S = np.cumsum(cnt[::-1, :], axis=0)[::-1, :] % PP
    new = S[Mx, Bi]
    new[idx, idx] = S[0, idx]
    cnt = new
print('modP DP m=300 K=300: %.2fs (all m est %.0fs)' % (time.time() - t0, (time.time() - t0) * 301 / 3))
