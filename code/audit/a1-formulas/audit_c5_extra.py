# -*- coding: utf-8 -*-
"""审计 a1-formulas：T5.4(2) 的递推阶数（BM 作用于由定义 DP 得到的 a_k(n)）。
列（固定 k，序列关于 n）：最小阶 4k，连接多项式 (1-x)^{2k+1}(1+x)^{2k-1}；
行（固定 n=2..7，序列关于 k）：报告「10/22/28/49/55/85 阶」。
"""
import time
from fractions import Fraction
from common import *  # noqa

t0 = time.time()
T = core.U_fast_table(230, 4)
ok = True
info = []
for n, want in zip(range(2, 8), (10, 22, 28, 49, 55, 85)):
    seq = [T[k][(n + 1) // 2] * T[k][n // 2] for k in range(0, 2 * want + 30)]
    Cx, L = bm_rational(seq)
    info.append('n=%d:%d' % (n, L))
    if L != want:
        ok = False
report(ok, 'T5.4.2-rows', '行（固定 n）最小递推阶：%s（报告 10/22/28/49/55/85）' % ', '.join(info))
TC = core.U_fast_table(7, 45)
ok = True
info = []
for k in range(1, 8):
    seq = [TC[k][(n + 1) // 2] * TC[k][n // 2] for n in range(0, 8 * k + 20)]
    Cx, L = bm_rational(seq)
    den = pmul(ppow([1, -1], 2 * k + 1), ppow([1, 1], 2 * k - 1))
    info.append('k=%d:%d' % (k, L))
    if L != 4 * k or trim(psub(Cx, [Fraction(v) for v in den])):
        ok = False
report(ok, 'T5.4.2-cols', '列（固定 k）最小递推阶 4k 且连接多项式 (1-x)^{2k+1}(1+x)^{2k-1}：%s' % ', '.join(info))
summary('audit_c5_extra')
print('elapsed %.1fs' % (time.time() - t0))
