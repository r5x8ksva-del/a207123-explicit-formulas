# -*- coding: utf-8 -*-
"""s17-b9b r7：对 notes/18 §3 的假设 (H) 与系数相变的数值审查（不 import 项目代码；数值佐证，不是证明）。
  r7-H     在复点 t 上精确算 h_k(t)（高斯整数 Horner），L_k(t):=(1/k)ln|h_k(t)|-(1/3)ln(k/(3e)) 与
           Φ_主支(t)=ln|1-t|-(1/3)ln|t-1-Log t|、Φ_最近(t)=ln|1-t|-(1/3)ln min_l|t-1-Log t+2πil| 比较（k=375,750,1500,3000）。
           在主支不是最近支的点（20i、3+8i、−3+8i、5i）上，数据跟的是主支——原文「由最近的 ψ(t)+2πil 决定」的说法在这些点不对，
           而公式本身（主支）对；h_k 全实根（A19）也要求极限是上半平面的调和函数，最近支版本做不到。
  r7-sign  k=3000：h_k 的系数在各 ξ 窗口里的实际变号数，与模型 k∫arg t_s(ξ)dξ/π 对照；ξ<ξ* 与 (ξ_2,2/3] 两段应几乎没有变号
用法：py -3.14 code/review/s17-b9b/r7_H.py
"""
import cmath
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s17_common import t17_full, lnbig  # noqa: E402

sys.stdout.reconfigure(encoding='utf-8')
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def eval_gauss(h, a, b, e):
    """h((a+bi)/2^e) 的模的自然对数（a、b 为整数，精确高斯整数 Horner）。"""
    re, im = 0, 0
    pr, pi_ = 1, 0                      # (a+bi)^j
    for j in range(len(h)):
        re, im = (re << e) + h[j] * pr, (im << e) + h[j] * pi_
        pr, pi_ = pr * a - pi_ * b, pr * b + pi_ * a
    d = len(h) - 1
    n2 = re * re + im * im
    return 0.5 * lnbig(n2) - d * e * math.log(2)


def Phi_p(t):
    return math.log(abs(1 - t)) - math.log(abs(t - 1 - cmath.log(t))) / 3


def Phi_n(t):
    p0 = t - 1 - cmath.log(t)
    return math.log(abs(1 - t)) - math.log(min(abs(p0 + 2j * math.pi * l) for l in range(-20, 21))) / 3


POINTS = [(0, 20, 0), (3, 8, 0), (-3, 8, 0), (0, 5, 0), (1, 1, 1), (-1, 1, 1), (0, 1, 1), (1, 2, 2), (-2, 0, 0), (-1, 0, 2)]
KS = [375, 750, 1500, 3000]
t00 = time.time()
res = {pt: [] for pt in POINTS}
hk3000 = None
for k, h in t17_full(max(KS)):
    if k in KS:
        for (a, b, e) in POINTS:
            L = eval_gauss(h, a, b, e) / k - math.log(k / (3 * math.e)) / 3
            res[(a, b, e)].append(L)
        if k == max(KS):
            hk3000 = h[:]
        print('  k=%d  %.1fs' % (k, time.time() - t00), flush=True)

lines = []
decided = []
for (a, b, e) in POINTS:
    t = complex(a, b) / 2 ** e
    pp, pn = Phi_p(t), Phi_n(t)
    Ls = res[(a, b, e)]
    gp = [L - pp for L in Ls]
    gn = [L - pn for L in Ls]
    # 误差按 k^{-1/3} 衰减（二阶项），用最后两个 k 做 Richardson 外推
    q = 2 ** (-1 / 3)
    Linf = (Ls[-1] - q * Ls[-2]) / (1 - q)
    shrink = gp[-1] / gp[-2] if gp[-2] != 0 else float('nan')
    lines.append('t=%s: Φ主=%.4f，Φ近=%.4f；L_k−Φ主=%s（相邻之比 %.3f）；外推 L_∞−Φ主=%+.4f，L_∞−Φ近=%+.4f'
                 % (str(t), pp, pn, ','.join('%+.4f' % x for x in gp), shrink, Linf - pp, Linf - pn))
    good_p = abs(Linf - pp) < 0.01
    if abs(pp - pn) > 0.03:
        decided.append(good_p and abs(Linf - pn) > 0.02)
    else:
        decided.append(good_p)
report('r7-H', len(decided) == len(POINTS) and all(decided),
       '（数值佐证）L_k(t)=(1/k)ln|h_k(t)|−(1/3)ln(k/3e)，k=%s：' % KS + '；'.join(lines)
       + '。L_k−Φ主 每次 k 加倍乘约 2^{-1/3}=0.794（二阶项），外推到 k=∞ 后 10 个点都落在主支上（<0.01），'
         '主支与最近支不同的 4 个点上离最近支 >0.02')

# ---------------------------------------------------------------- 系数的局部变号数
k = max(KS)
h = hk3000
d = len(h) - 1
sg = [1 if c > 0 else -1 for c in h]
nzero = sum(1 for c in h if c == 0)


def g(t):
    return (1 - t) / (3 * (t - 1 - cmath.log(t))) - t / (1 - t)


def gp(t):
    p = t - 1 - cmath.log(t)
    return (-p + (1 - t) ** 2 / t) / (3 * p * p) - 1 / (1 - t) ** 2


# 实的 t*、ξ*
lo, hi = 0.01, 0.3
for _ in range(200):
    m = (lo + hi) / 2
    if gp(complex(m, 0)).real > 0:
        lo = m
    else:
        hi = m
ts = (lo + hi) / 2
xs = g(complex(ts, 0)).real
sec = ((g(complex(ts + 1e-4, 0)) + g(complex(ts - 1e-4, 0)) - 2 * g(complex(ts, 0))) / 1e-8).real
# 复鞍点路径 → 累积函数 A(ξ)=∫_{ξ*}^{ξ} arg t_s dξ'/π
N = 60000
path = []
t = None
for n in range(1, N + 1):
    xi = xs + (2 / 3 - 1e-7 - xs) * (n / N) ** 2
    if t is None:
        t = complex(ts, math.sqrt(2 * (xi - xs) / abs(sec)))
    for _ in range(80):
        f = g(t) - xi
        st = f / gp(t)
        if abs(st) > 0.3 * abs(t):
            st *= 0.3 * abs(t) / abs(st)
        t = t - st
        if abs(f) < 1e-14:
            break
    im = t.imag if abs(t.imag) > 1e-12 * abs(t) else 0.0
    path.append((xi, math.atan2(max(im, 0.0), t.real) / math.pi))
cum = [(xs, 0.0)]
for (x0, a0), (x1, a1) in zip([(xs, 0.0)] + path[:-1], path):
    cum.append((x1, cum[-1][1] + (x1 - x0) * (a0 + a1) / 2))


def A(xi):
    if xi <= xs:
        return 0.0
    lo_, hi_ = 0, len(cum) - 1
    while hi_ - lo_ > 1:
        m = (lo_ + hi_) // 2
        if cum[m][0] <= xi:
            lo_ = m
        else:
            hi_ = m
    (x0, c0), (x1, c1) = cum[lo_], cum[hi_]
    return c0 + (c1 - c0) * (xi - x0) / (x1 - x0) if x1 > x0 else c0


edges = [0, xs, 0.13, 0.16, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.55, 0.6, 0.65, 0.6567, 2 / 3 + 1e-9]
rows = []
for a_, b_ in zip(edges, edges[1:]):
    i0, i1 = int(math.ceil(a_ * k)), min(d, int(math.floor(b_ * k)))
    act = sum(1 for i in range(i0, i1) if sg[i] != sg[i + 1]) if i1 > i0 else 0
    mod = k * (A(min(b_, 2 / 3)) - A(a_))
    rows.append((a_, b_, act, mod))
total = sum(1 for i in range(d) if sg[i] != sg[i + 1])
dev_mid = max(abs(r[2] - r[3]) / max(1.0, r[3]) for r in rows[1:-2])
report('r7-sign', total == k // 3 and nzero == 0 and rows[0][2] == 0,
       '（数值佐证）k=%d：系数没有零、总变号 %d=⌊k/3⌋；按 ξ 窗口的实际变号数 / 模型 k∫arg t_s dξ/π：%s；中间各窗口的相对偏差最大 %.1f%%。'
       'ξ<ξ*（i<%.1f）里没有变号（ℓ_k=%s）；(ξ_2,2/3] 里模型为 0'
       % (k, total, '；'.join('[%.4f,%.4f): %d / %.1f' % r for r in rows), 100 * dev_mid, xs * k,
          next(i for i in range(d + 1) if h[i] <= 0)))
print('# elapsed %.1fs' % (time.time() - t00))
print('SUMMARY s17-r7 pass=%d fail=%d' % (RES.count(True), RES.count(False)))
