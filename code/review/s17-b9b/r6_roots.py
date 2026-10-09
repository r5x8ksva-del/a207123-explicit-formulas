# -*- coding: utf-8 -*-
"""s17-b9b r6：h_k 的根的区间计数（精确），与模型 kF(τ) 及 notes/18 表 3 对照（不 import 项目代码）。
对 k∈{60,150,300,600}：
  1. h_k 用自写 T1.7 的完整多项式，并与 N 三角公式逐项对照（独立算法）。
  2. 每个目标区间 I（(−τ,0)，τ=0.1,0.5,1,2,5,10；(1,1.05)、(1,1.5)；(1,2^40)、(−2^40,0)、(0,1)）：
     上界 U = Descartes 变号数（rootlib.desc_count；对任何多项式都 >= 区间里的根数）；
     下界 L = 在区间里的一串有理点上数 h 的变号（介值定理；网格在 t=0 左侧按 2 的幂分层，主体每倍程 256 点、
     尾部每倍程 16 点（2^-80 以下 4 点），正侧在 1+2^-30..1+2^40 按倍程 256 点）。
     L=U 时计数精确，**不依赖 A19**；而且全部区间合计数到 deg h_k 个根时，顺带重新证明了这一个 h_k 全实根、根互异。
  3. 与 notes/18 表 3 的「根数 − kF(τ)」逐个对照（k=60、300、600），并算相对误差。
用法：py -3.14 code/review/s17-b9b/r6_roots.py [k,k,...]
"""
import math
import os
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s17_common import t17_full, N_rows, h_from_N  # noqa: E402
from rootlib import desc_count, sign_at  # noqa: E402

sys.stdout.reconfigure(encoding='utf-8')
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def F(tau):
    v = tau + 1 + math.log(tau)
    return (math.atan(v / math.pi) + math.pi / 2) / (3 * math.pi)


# notes/18 表 3（按原文抄录，用于对照；k=60、300、600，τ=0.1,0.5,1,2,5,10）
TABLE3 = {60: [-0.7, -0.6, -0.6, -0.5, -0.5, -0.5], 300: [-2.4, -2.0, -1.0, -1.6, -1.5, -0.6],
          600: [-2.7, -3.0, -2.1, -2.1, -2.1, -2.2]}
TABLE3_POS = {300: (0.75, 0.89), 600: (0.80, 0.91)}
TAUS = [Fr(1, 10), Fr(1, 2), Fr(1), Fr(2), Fr(5), Fr(10)]


def neg_grid(fine_lo=-12, fine_hi=13, per=256, tail_lo=-400):
    """t<0 侧的网格（返回 s=-t>0 的递增有理数列）：2^tail_lo..2^fine_lo 每倍程 1 点；2^fine_lo..2^fine_hi 每倍程 per 点。"""
    pts = set()
    for e in range(tail_lo, fine_lo):
        per_t = 16 if e >= -80 else 4
        base = Fr(2) ** e
        for m in range(per_t):
            pts.add(base * (1 + Fr(m, per_t)))
    for e in range(fine_lo, fine_hi):
        base = Fr(2) ** e
        for m in range(per):
            pts.add(base * (1 + Fr(m, per)))
    pts.add(Fr(2) ** fine_hi)
    for t in TAUS:
        pts.add(t)
    return sorted(pts)


def pos_grid(lo=-30, hi=40, per=256):
    """t>1 侧的网格（返回 x=t-1>0 的递增有理数列）。"""
    pts = set()
    for e in range(lo, hi):
        base = Fr(2) ** e
        for m in range(per):
            pts.add(base * (1 + Fr(m, per)))
    pts.add(Fr(2) ** hi)
    pts.add(Fr(1, 20))
    pts.add(Fr(1, 2))
    return sorted(pts)


def signs_at(h, xs):
    out = []
    for x in xs:
        s = sign_at(h, x)
        if s == 0:
            raise ValueError('h_k vanishes at %s' % x)
        out.append(s)
    return out


def changes(sg, lo_idx, hi_idx):
    return sum(1 for a in range(lo_idx, hi_idx) if sg[a] != sg[a + 1])


ks = [int(x) for x in sys.argv[1].split(',')] if len(sys.argv) > 1 else [60, 150, 300, 600]
t00 = time.time()
want = set(ks)
polys = {}
for k, h in t17_full(max(ks)):
    if k in want:
        polys[k] = h[:]
Nr = {}
for k, row in N_rows(max(ks), max(ks)):
    if k in want:
        Nr[k] = row[:]
ok_alg = all(h_from_N(k, Nr[k], i) == (polys[k][i] if i < len(polys[k]) else 0)
             for k in ks for i in range(len(polys[k]) + 2))
report('r6-alg', ok_alg, '自写 T1.7 的完整 h_k 与 N 三角公式逐项相等（k=%s，全部系数及其后两个 0）' % ks)

summary = {}
for k in ks:
    t0 = time.time()
    h = polys[k]
    d = len(h) - 1
    npos_exp, nneg_exp = k // 3, d - k // 3
    # 负侧
    sgrid = neg_grid()
    tpts = [-s for s in reversed(sgrid)] + [Fr(0)]          # t 递增：-2^5 ... -tiny, 0
    sg = signs_at(h, tpts)
    idx = {t: n for n, t in enumerate(tpts)}
    L_tot_neg = changes(sg, 0, len(tpts) - 1)
    U_tot_neg = desc_count(h, -Fr(2) ** 40, 0)
    U_beyond = desc_count(h, -Fr(2) ** 40, tpts[0])
    rows = []
    for tau in TAUS:
        L = changes(sg, idx[-tau], len(tpts) - 1)
        U = desc_count(h, -tau, 0)
        rows.append((float(tau), L, U, U - k * F(float(tau))))
    # 正侧
    xg = pos_grid()
    ppts = [Fr(1)] + [1 + x for x in xg]
    psg = signs_at(h, ppts)
    pidx = {t: n for n, t in enumerate(ppts)}
    L_pos_all = changes(psg, 0, len(ppts) - 1)
    U_pos_all = desc_count(h, 1, 1 + Fr(2) ** 40)
    L105 = changes(psg, 0, pidx[1 + Fr(1, 20)])
    U105 = desc_count(h, 1, 1 + Fr(1, 20))
    L15 = changes(psg, 0, pidx[1 + Fr(1, 2)])
    U15 = desc_count(h, 1, 1 + Fr(1, 2))
    U01 = desc_count(h, 0, 1)
    exact = all(r[1] == r[2] for r in rows) and L105 == U105 and L15 == U15 and L_pos_all == U_pos_all \
        and L_tot_neg == U_tot_neg and U_beyond == 0
    allreal = exact and (L_tot_neg + L_pos_all == d) and U01 == 0
    summary[k] = (rows, (L105, U105), (L15, U15), (L_pos_all, U_pos_all), (L_tot_neg, U_tot_neg))
    ok_tab = True
    tabmsg = ''
    if k in TABLE3:
        mine = [round(r[3], 1) for r in rows]
        ok_tab = all(abs(a - b) < 0.051 for a, b in zip(mine, TABLE3[k]))
        tabmsg = '；与表 3 的 %s %s' % (TABLE3[k], '一致' if ok_tab else '不一致')
    posmsg = ''
    if k in TABLE3_POS:
        fr = (U105 / npos_exp, U15 / npos_exp)
        okp = abs(fr[0] - TABLE3_POS[k][0]) < 0.006 and abs(fr[1] - TABLE3_POS[k][1]) < 0.006
        ok_tab = ok_tab and okp
        posmsg = '；(1,1.05)、(1,1.5) 中的比例 %.3f、%.3f（原文 %.2f、%.2f）' % (fr[0], fr[1], TABLE3_POS[k][0], TABLE3_POS[k][1])
    rel = max(abs(r[3]) / (k * F(r[0])) for r in rows)
    report('r6-k%d' % k, exact and allreal and ok_tab and U_pos_all == npos_exp,
           'k=%d（deg %d）：(−τ,0) 中的根数 [下界=上界]=%s，减 kF(τ) 为 %s（最大相对误差 %.1f%%）%s；'
           '正根 %d 个（=⌊k/3⌋），(1,1.05) 中 %d、(1,1.5) 中 %d%s；负根 %d 个、(0,1) 中 0 个，'
           '下界与上界处处相等，合计 %d=deg，所以这些计数精确且不依赖 A19（%.1fs）'
           % (k, d, [r[1] for r in rows], [round(r[3], 2) for r in rows], 100 * rel, tabmsg,
              U_pos_all, U105, U15, posmsg, L_tot_neg, L_tot_neg + L_pos_all, time.time() - t0))
print('# elapsed %.1fs' % (time.time() - t00))
print('SUMMARY s17-r6 pass=%d fail=%d' % (RES.count(True), RES.count(False)))
