# -*- coding: utf-8 -*-
"""s12-b5 复核 r9：纤维 u=1 的留数条件的数值直观检查（与 r3 的代数论证互相独立）。

(2,1) 形状的表示要求 θ_t := u'(ξ_t)·Res_{ξ_t}F·ξ_t^{-g} 在 b_1 的三个根上相同。用 r2 已核对的闭式
  N:   (-1)^(q-1) ξ(1+ξ) Ψ_q(ξ)，N^c: (-1)^(q-1) Ψ_q(ξ)，N^E: (-1)^(q-1) ξ^5 Ψ_q(ξ)
对 g∈[-80,80] 逐个计算三根处的值，看哪些 g 使三值（相对误差 1e-9 内）相同。
  r9-N     N_q（2<=q<=12）：没有任何 g 使三值相同
  r9-Nc    N^c_q：只有 q=2、g=-6 相同（命题 6(i) 的 q=2 式）；q>=3 没有（与命题 6(i) 一致，虽然 6(i) 用的是别的纤维）
  r9-NE    N^E_q：只有 q=2、g=-1 相同（命题 6(ii)）
"""
import os
import sys
import time
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s12b5_common import report, summary, roots_cubic_b  # noqa: E402

t0 = time.time()
R = roots_cubic_b(1)


def psi(q, x):
    return sum(comb(q, n) * x ** (-3 * n) / factorial(n - 2) for n in range(2, q + 1))


def base(kind, q, x):
    pre = {'N': x * (1 + x), 'Nc': 1, 'NE': x ** 5}[kind]
    return (-1) ** (q - 1) * pre * psi(q, x)


coinc = {}
for kind in ('N', 'Nc', 'NE'):
    for q in range(2, 13):
        for g in range(-80, 81):
            vals = [base(kind, q, x) * x ** (-g) for x in R]
            ref = vals[0]
            if all(abs(v - ref) <= 1e-9 * abs(ref) for v in vals[1:]):
                coinc.setdefault(kind, []).append((q, g))
report('N' not in coinc, 'r9-N', 'N_q（2<=q<=12）在 g∈[-80,80] 内没有使三根处留数元相同的 g：%s' % coinc.get('N'))
report(coinc.get('Nc') == [(2, -6)], 'r9-Nc', 'N^c_q：三值相同的 (q,g) = %s（应只有 (2,-6)）' % coinc.get('Nc'))
report(coinc.get('NE') == [(2, -1)], 'r9-NE', 'N^E_q：三值相同的 (q,g) = %s（应只有 (2,-1)）' % coinc.get('NE'))
print('time %.1fs' % (time.time() - t0))
sys.exit(1 if summary('r9') else 0)
