# -*- coding: utf-8 -*-
"""探索 7b：m 无关的两族必要条件。对 m>=2，纤维 v=1,2 的留数条件（平移 a=g1+3m+3, b=g2+3m+3 后）为
   Wv(xi_v) 与 xi_v^a, xi_v^b 在 Q(xi_v) 中线性相关，  W1(x) = 1 + x^5,  W2(x) = 1 + 2x^5 + 4x^8，
与 m 无关。本脚本穷举 |a|,|b| <= A，报告同时满足两条的 (a,b)。并顺带核对 theta_v 与 Wv(xi)xi^{-3m-3} 成比例（m<=8）。"""
import os, sys, time
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e7_twofamily import Field, W_poly, det3  # noqa  (导入时会先跑一遍 e7 的小搜索)
from polylib import P_poly, pmul, pderiv

A = int(sys.argv[1]) if len(sys.argv) > 1 else 150
t0 = time.time()
Wv = {1: [1, 0, 0, 0, 0, 1], 2: [1, 0, 0, 0, 0, 2, 0, 0, 4]}
data = {}
for v in (1, 2):
    Fd = Field(v)
    xi = [Fr(0), Fr(1), Fr(0)]
    w = Fd.red(Wv[v])
    # 核对：theta_v(m) / (Wv(xi) xi^{-3m-3}) 为有理数（m = v..8）
    up = Fd.mul(Fd.mul(pmul(xi, xi), [3, -2]), Fd.inv(pmul([1, -1], [1, -1])))
    xinv = Fd.inv(xi)
    for m in range(v, 9):
        theta = Fd.mul(Fd.mul(Fd.red(W_poly(m)), up), Fd.inv(Fd.red(pderiv(P_poly(m)))))
        ref = w
        for _ in range(3 * m + 3):
            ref = Fd.mul(ref, xinv)
        ratio = Fd.mul(theta, Fd.inv(ref))
        assert ratio[1] == 0 and ratio[2] == 0, ('not proportional', v, m)
    pw = {0: [Fr(1), Fr(0), Fr(0)]}
    for g in range(1, A + 1):
        pw[g] = Fd.mul(pw[g - 1], xi)
        pw[-g] = Fd.mul(pw[-g + 1], xinv)
    data[v] = (w, pw)
print('theta_v proportional to W_v(xi) xi^{-3m-3} for v=1,2, m<=8: OK')
sols1 = []
both = []
w1, p1 = data[1]
w2, p2 = data[2]
for a in range(-A, A + 1):
    for b in range(a + 1, A + 1):
        if det3(w1, p1[a], p1[b]) == 0:
            sols1.append((a, b))
            if det3(w2, p2[a], p2[b]) == 0:
                both.append((a, b))
print('|a|,|b|<=%d: fiber-1 solutions %d (e.g. %s); common solutions with fiber 2: %s   (%.1fs)' % (
    A, len(sols1), sols1[:8], both, time.time() - t0))
