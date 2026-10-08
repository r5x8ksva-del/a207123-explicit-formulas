# -*- coding: utf-8 -*-
"""s12-b5 复核 r5：定理 5(b)（以 c_i 为原子的 Stirling 类比型单和）。

方法与作者不同：不做部分分式，直接对真值 N(k,q)（自写 DP + 容斥，k<=60）解精确线性方程组
  N(k,q) = γ0 + sum_{i=1}^{q-1} sum_{r=0}^{2} γ_r(q,i) c_i(k+3(q-1)+σ-r)，5<=k<=60，
再与 Q[x]/(b_i) 中 x^σ W~_i 的约化坐标（自写约化）比较。
  r5-unique   方程组相容且列满秩（3q-2 个未知数，解唯一），2<=q<=8，σ∈{-2,0,2,5}
  r5-top      (q-1)!·γ_r(q,q-1) = x^σ W~_{q-1} 在 K_{q-1} 中的坐标（σ=0 时即 A_{q-1}^{(r)}）
  r5-all      全部系数：γ_r(q,i) = x^σ·(-1)^{q-1-i}/i!·W~_i·sum_t C(q,t) x^{3t}/(q-1-i-t)! 的坐标（注 3.1 的部分分式结构），1<=i<=q-1
  r5-Nc       N^c 的同样拟合：最高一项 (q-1)!γ = x^σ 的坐标（σ=0 时为 (1,0,0)，注 5.1）
  r5-rev      反向：把最高一项与 A_{q-2} 比较，应不符
  r5-vp       notes/12 引理 2.4 的赋值（定理 5(b) 引用）：min_r v_p(x^σ W~_p 的坐标)=-3(p-1)/2（σ=0，奇素数 p<=61）
  r5-norm     规范化的影响（补充，不是作者的断言）：若原子平移不带 3(q-1)（c_i(k+σ'-r)，σ' 与 q 无关），最高一项是
              x^{σ'-3(q-1)} W~_{q-1} 的坐标；对 p=q-1 素数，打印其 min v_p（σ'=0,1,2），看 p 进障碍是否还在
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s12b5_common import (report, summary, C, ie_tables, CI, Cubic, Wtil_poly, consistent_exact,  # noqa: E402
                          vp_frac, primes_upto)

t0 = time.time()
KI = 60
IN, INc, INE = ie_tables(KI, 8)
ci = CI(300)
KS = list(range(5, KI + 1))


def fit(tab, q, sigma):
    cols = [('0', 0, 0)] + [('c', i, r) for i in range(1, q) for r in range(3)]
    rows = []
    for k in KS:
        row = []
        for kind, i, r in cols:
            row.append(1 if kind == '0' else ci(i, k + 3 * (q - 1) + sigma - r))
        rows.append(row)
    rhs = [tab[k][q] for k in KS]
    okc, rk, sol = consistent_exact(rows, rhs)
    return okc, rk, len(cols), ({col: v for col, v in zip(cols, sol)} if okc else None)


def coords(i, sigma, poly):
    K = Cubic([1, -1, 0, -i])
    return K.mul(K.xpow(sigma), K.red([Fr(c) for c in poly]))


ok_u = ok_t = ok_a = ok_c = True
rev_bad = 0
nfit = 0
for q in range(2, 9):
    for sigma in (-2, 0, 2, 5):
        okc, rk, nunk, sol = fit(IN, q, sigma)
        nfit += 1
        if not (okc and rk == nunk):
            ok_u = False
            print('  not unique/consistent', q, sigma, okc, rk, nunk)
            continue
        top = coords(q - 1, sigma, Wtil_poly(q - 1))
        got = [factorial(q - 1) * sol[('c', q - 1, r)] for r in range(3)]
        if got != top:
            ok_t = False
            print('  top mismatch', q, sigma, got, top)
        if q >= 3:
            wrong = coords(q - 2, sigma, Wtil_poly(q - 2))
            if got != wrong:
                rev_bad += 1
        # 全部系数
        for i in range(1, q):
            n = q - 1 - i
            K = Cubic([1, -1, 0, -i])
            lag = [Fr(0)] * 3
            for t in range(n + 1):
                term = K.xpow(3 * t)
                lag = [a + Fr(comb(q, t), factorial(n - t)) * b for a, b in zip(lag, term)]
            el = K.mul(K.mul(K.xpow(sigma), K.red([Fr(c) for c in Wtil_poly(i)])), lag)
            el = [Fr((-1) ** (q - 1 - i), factorial(i)) * v for v in el]
            if [sol[('c', i, r)] for r in range(3)] != el:
                ok_a = False
                print('  coef mismatch', q, sigma, i)
        # N^c
        okc2, rk2, nunk2, sol2 = fit(INc, q, sigma)
        if not (okc2 and rk2 == nunk2):
            ok_c = False
        else:
            topc = coords(q - 1, sigma, [1])
            gotc = [factorial(q - 1) * sol2[('c', q - 1, r)] for r in range(3)]
            if gotc != topc:
                ok_c = False
report(ok_u, 'r5-unique', '%d 个拟合（2<=q<=8，σ∈{-2,0,2,5}，k∈[5,60]）都相容且列满秩：表示存在且唯一' % nfit)
report(ok_t, 'r5-top', '(q-1)!·γ_r(q,q-1) = x^σ W~_{q-1} 的约化坐标（σ=0 时为 A_{q-1}^{(r)}）')
report(ok_a, 'r5-all', '全部 γ_r(q,i) 等于 x^σ·(-1)^{q-1-i}/i!·W~_i·sum_t C(q,t)x^{3t}/(n-t)! 的坐标（注 3.1 的部分分式）')
report(ok_c, 'r5-Nc', 'N^c 的拟合同样唯一，最高一项 (q-1)!γ = x^σ 的坐标（σ=0 时为 (1,0,0)）')
report(rev_bad == 6 * 4, 'r5-rev', '反向：把最高一项与 A_{q-2}（x^σ W~_{q-2} 的坐标）比较，%d/24 个不符（应全部不符）' % rev_bad)

# ---------------------------------------------------------------- 赋值
ok = True
rows_out = []
for p in [p for p in primes_upto(61) if p >= 3]:
    a0 = coords(p, 0, Wtil_poly(p))
    v0 = min(vp_frac(v, p) for v in a0 if v != 0)
    if v0 != -3 * (p - 1) // 2:
        ok = False
    vs = []
    for sp in (0, 1, 2):
        a = coords(p, sp - 3 * p, Wtil_poly(p))
        vs.append(min(vp_frac(v, p) for v in a if v != 0))
    rows_out.append((p, v0, vs))
report(ok, 'r5-vp', 'min_r v_p(A_p^{(r)}) = -3(p-1)/2（3<=p<=61）：%s' % [(p, v0) for p, v0, _ in rows_out[:6]])
allbounded = all(min(vs) >= -1 for _, _, vs in rows_out)
print('  规范化 c_i(k+σ\'-r)（不带 3(q-1)）时最高一项的 min v_p，p=q-1：')
for p, v0, vs in rows_out:
    print('    p=%2d  带 3(q-1) 的 σ=0: %4d   不带: σ\'=0,1,2 -> %s' % (p, v0, vs))
report(True, 'r5-norm', '（信息）不带 3(q-1) 的规范化下最高一项的 min v_p 是否都 >=-1：%s——若是，引理 2.4/2.5 的 p 进障碍在该规范化下消失，'
       '定理 5(b) 的结论依赖平移 3(q-1)+σ 的约定' % allbounded)

print('time %.1fs' % (time.time() - t0))
sys.exit(1 if summary('r5') else 0)
