# -*- coding: utf-8 -*-
"""探索 1：N 三角两种算法对照；近对角线 D(k,d)=N(k,k-d) 的多项式拟合与精确门槛。"""
import time
from c4lib import *

t0 = time.time()
KR = 120
NR = N_table_rec(KR)
t1 = time.time()
print('rec table K=%d: %.2fs' % (KR, t1 - t0))
KD = 60
ND, T = N_table_dp(KD)
t2 = time.time()
print('dp table K=%d: %.2fs' % (KD, t2 - t1))
bad = [(k, q) for k in range(KD + 1) for q in range(k + 1) if NR[k][q] != ND[k][q]]
print('rec vs dp mismatches (k<=%d):' % KD, bad[:10], len(bad))

DMAX = 12
polys = {}
for d in range(0, DMAX + 1):
    deg = 2 * d
    ks = list(range(KR - deg, KR + 1))
    ys = [Dval(NR, k, d) for k in ks]
    p = interpolate(ks, ys)
    # 检查从哪里开始成立
    ok_from = None
    for k in range(KR, -1, -1):
        if pval(p, k) != Dval(NR, k, d):
            ok_from = k + 1
            break
    else:
        ok_from = 0
    polys[d] = p
    lead = p[-1] if p else 0
    exc = [(k, Dval(NR, k, d), pval(p, k)) for k in range(max(d + 1, 0), ok_from)]
    print('d=%d deg=%d lead=%s (2/(2^d d!)=%s) threshold K_d=%d' % (
        d, len(p) - 1, lead, Fraction(2, 2 ** d * __import__('math').factorial(d)), ok_from))
    print('   coeffs:', [str(c) for c in p])
    print('   exceptions (k, D, p(k)) for d+1<=k<K_d:', [(a, b, str(c)) for a, b, c in exc])
    print('   p(k) at k=0..d:', [str(pval(p, k)) for k in range(0, d + 1)])
