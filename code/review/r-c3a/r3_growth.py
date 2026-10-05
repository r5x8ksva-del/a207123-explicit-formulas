# -*- coding: utf-8 -*-
"""r-c3a 独立复核脚本 3：
 (a) C3A-25 猜想（f_k(t) Gevrey-1/3）：用 (C6) 递推生成 h_k（k<=300，整数多项式），精确求 f_k(-1/2) = h_k(-1/2)/(3/2)^{k+1}；
     先在 k<=40 对照 DP 的 (1-t)^{k+1} sum_m U_k(m) t^m（锚定），再看 log|f_k| - (1/3)log k! 是否近似线性。
 (b) 作者给的两个常数项差值数字：885.947066578982521659…（(3/5,-1/2)）、3.5774982569309233663e-8（(3/10,-1/10)）。
 (c) C3A-23 门槛：x=1/10 时常数项差值 x^{-3}|Γ(-λ)| e^a a^λ 在 r=|t|/(1-x) 跨过 W(1/e) 时由指数小变为指数大。
"""
import os
import sys
import time
from fractions import Fraction as Fr
from decimal import Decimal as D, getcontext
from math import comb, lgamma, log, exp

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, CODE)
import core

src = open(os.path.join(HERE, 'r2_numeric.py'), encoding='utf-8').read()
ns = {}
exec(compile(src[:src.index('# ============================================================ 1.')], 'r2_funcs', 'exec'), ns)

T0 = time.time()
RES = []


def rep(cid, ok, desc):
    RES.append(bool(ok))
    print(('PASS' if ok else 'FAIL'), cid, desc, flush=True)


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def pder(p):
    return [i * p[i] for i in range(1, len(p))] or [0]


KMAX = 300
hr = [[1], [1], [1, 1]]
for k in range(3, KMAX + 1):
    a = hr[k - 3]
    term = padd(pmul([1, -1], pder(a)), [(k - 2) * c for c in a])
    hr.append(trim(padd(hr[k - 1], pmul([0, 1, -1], term))))
T = core.U_fast_table(40, 41)
ok = True
for k in range(41):
    hd = trim([sum((-1) ** j * comb(k + 1, j) * T[k][i - j] for j in range(0, min(i, k + 1) + 1)) for i in range(41)])
    ok &= hd == hr[k]
t0 = Fr(-1, 2)
fk = [sum(Fr(c) * t0 ** i for i, c in enumerate(hr[k])) / (1 - t0) ** (k + 1) for k in range(KMAX + 1)]
rows = []
lin = []
for k in (25, 50, 75, 100, 150, 200, 250, 300):
    v = abs(fk[k])
    lv = log(v.numerator) - log(v.denominator)
    rows.append('k=%d: |f_k|^(1/k)=%.4f, |f_k|^(1/k)/k^(1/3)=%.4f, (log|f_k|-lgamma(k+1)/3)/k=%.4f, sign=%s'
                % (k, exp(lv / k), exp(lv / k) / k ** (1 / 3), (lv - lgamma(k + 1) / 3) / k, '+' if fk[k] > 0 else '-'))
    lin.append((lv - lgamma(k + 1) / 3) / k)
signs = ''.join('+' if fk[k] > 0 else '-' for k in range(0, 40))
rep('r3-fk-anchor', ok, '(C6) recurrence h_k == DP (1-t)^{k+1} sum_m U_k(m)t^m for k<=40 (anchor for the growth data)')
for r in rows:
    print('#   ' + r)
print('#   signs of f_k(-1/2), k=0..39: ' + signs)
# 数据观察（不是证明）：(log|f_k| - log(k!)/3)/k 在 k=100..300 内变化很小（与 Gevrey-1/3 相容）
spread = max(lin[3:]) - min(lin[3:])
rep('r3-fk-gevrey-data', spread < 0.1, '[DATA] C3A-25: (log|f_k(-1/2)| - log(k!)/3)/k varies by %.4f over k=100..300 (consistent with Gevrey-1/3; '
    'still only data, not a proof)' % spread)

# (b) 作者的常数项差值数字
getcontext().prec = 60
PI = ns['agm_pi']()
okb = True
for (x, t, s) in [(Fr(3, 5), Fr(-1, 2), '885.947066578982521659'), (Fr(3, 10), Fr(-1, 10), '3.5774982569309233663E-8')]:
    xd, td = ns['dec'](x), ns['dec'](t)
    lamd = (1 - xd) / xd ** 3
    a = -td / xd ** 3
    g = ns['gamma_neg_reflect'](lamd, PI)
    gap = a.exp() * (lamd * a.ln()).exp() / xd ** 3 * g
    ref = D(s)
    okb &= abs(gap - ref) / abs(ref) < D(10) ** -18
    print('#   const-part gap at (%s,%s) = %s   (author %s)' % (x, t, str(gap)[:28], s))
rep('r3-const-gap-values', okb, '[NUM] author\'s constant-part gaps x^{-3}Gamma(-lam)e^a a^lam = 885.947066578982521659.. and 3.5774982569309233663e-8 reproduced (rel 1e-18)')

# (c) C3A-23 门槛：W(1/e) 与 x=1/10 处的指数符号翻转
w = D('0.27')
for _ in range(60):
    w = w - (w * w.exp() - (-D(1)).exp()) / ((1 + w) * w.exp())
okc = str(w).startswith('0.27846')
x = Fr(21, 200)          # λ = 773.13…（x=1/10 会给出整数 λ=900，正好是极点 x_900）
xd = ns['dec'](x)
lamd = (1 - xd) / xd ** 3
vals = []
for tt in (Fr(-20, 100), Fr(-23, 100), Fr(-24, 100), Fr(-26, 100), Fr(-28, 100), Fr(-35, 100)):
    td = ns['dec'](tt)
    a = -td / xd ** 3
    lg = (a + lamd * a.ln() + (PI.ln()) - abs(ns['dsin'](PI * lamd, PI)).ln() - ns['lngamma'](1 + lamd, PI) - 3 * xd.ln())   # ln|gap|
    r = abs(td) / (1 - xd)
    vals.append((float(r), float(r * (1 + r).exp()), float(lg)))
okc &= all((v[1] < 1) == (v[2] < 0) for v in vals)
rep('r3-threshold', okc, 'C3A-23: W(1/e) = %s; at x=21/200 (lam=773.1) ln|const-part gap| < 0 exactly when r e^{1+r} < 1: %s'
    % (str(w)[:10], '; '.join('r=%.4f re^(1+r)=%.3f ln|gap|=%.1f' % v for v in vals)))

npass = sum(RES)
print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY r3 pass=%d fail=%d' % (npass, len(RES) - npass))
sys.exit(0 if npass == len(RES) else 1)
