# -*- coding: utf-8 -*-
"""探索（不计入检查）：h_k 的根在 t=1 右侧与 t=0 左侧分布在什么尺度上，用于设计 r6 的网格。"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from s17_common import t17_full
from rootlib import desc_count
sys.stdout.reconfigure(encoding='utf-8')
K = int(sys.argv[1])
for k, h in t17_full(K):
    pass
d = len(h) - 1
t0 = time.time()
print('k=%d d=%d' % (K, d))
print('positive side: roots in (1, 1+10^-j):', [(j, desc_count(h, 1, 1 + Fr(10) ** (-j))) for j in range(0, 13, 2)], '%.1fs' % (time.time() - t0), flush=True)
print('negative side: roots in (-10^-j, 0):', [(j, desc_count(h, -Fr(10) ** (-j), 0)) for j in range(-3, 110, 6)], '%.1fs' % (time.time() - t0), flush=True)
print('roots in (1, 10^9):', desc_count(h, 1, 10 ** 9), ' in (-10^9, 0):', desc_count(h, -10 ** 9, 0), ' in (0,1):', desc_count(h, 0, 1))
print('max coefficient bits', max(abs(x).bit_length() for x in h), '%.1fs' % (time.time() - t0))
