# -*- coding: utf-8 -*-
"""s17-b9b r4：定理 1 的界与精确值逐点对照，以及几个「故意改坏」的变体（不 import 项目代码）。
h_{k,i} 用自写 T1.7（r2a 已与 U 的反演在 k<=3000、i<=100 上逐个对过）；c_i、ρ_i 用 90 位十进制。
对 1<=i<=IMAX、0<=k<=KMAX 中界 >=1e-60 的全部 (k,i)（定理对一切 k>=0 声称成立）：
  r4-thm     |h_{k,i}/(c_iρ_i^k)-1| <= B(k,i):=3(e^X-1)(1+4.2E)+4.2E；统计 实际/界 的最大值（全体与 k>=K_i 两段）
  r4-tau     界在 k=τ_i 处 >=1（1<=i<=IMAX），所以门槛附近必须靠精确计算
  r4-var     变体（把常数改小或把假引理当真）在数据上是否被推翻：
             V1 4.2→3；V2 c_j/c_i<=3P_j/P_i 的 3→1；V3 两者同时；V4 λ_j>=1 改成 λ_j>=2（X→X/e）；
             V5 X 只保留 n=1 项（3X 代替 3(e^X-1)）；V6 引理 1.3 的 D_i 换成 3i；V7 去掉 j=i 复根项（4.2E→0）
  r4-026     0.26→0.5：K_i(0.5) 处定理 1 的界 >1（证明的最后一步失效），而数据上 h_{k,i}>0 对 k>=K_i(0.5) 仍成立（只是没有证明）
用法：py -3.14 code/review/s17-b9b/r4_thm.py [IMAX] [KMAX]
"""
import math
import os
import sys
import time
from decimal import Decimal as D, getcontext, localcontext

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s17_common import t17_rows, rho_dec, c_dec, K_bound, parse_tau_table  # noqa: E402

sys.stdout.reconfigure(encoding='utf-8')
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


IMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 100
KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
t0 = time.time()
getcontext().prec = 90
tab18 = parse_tau_table(os.path.join(ROOT, 'notes', '18-主Agent-表B-B9-门槛的增长.md'))
rho = [None] + [rho_dec(i, 95) for i in range(1, IMAX + 1)]
cc = [None] + [c_dec(i, 92) for i in range(1, IMAX + 1)]
u = [None] + [r ** 3 for r in rho[1:]]
Dd = [None] + [rho[i] ** 2 + 3 * i for i in range(1, IMAX + 1)]
Kn = [None] + [float(K_bound(i)[0]) for i in range(1, IMAX + 1)]
K05 = [None] + [float(K_bound(i, '0.5')[0]) for i in range(1, IMAX + 1)]
pw = [None] + [D(1)] * IMAX                     # ρ_i^k
one = D(1)
TINY = D('1e-60')

# 统计量
max_all = (D(0), None)
max_tail = (D(0), None)
viol = 0
npairs = 0
var_names = ['V1 4.2→3', 'V2 3→1', 'V3 两者', 'V4 X→X/e', 'V5 3X 代替 3(e^X-1)', 'V6 D_i→3i', 'V7 去掉 j=i 复根项']
var_viol = [0] * len(var_names)
var_first = [None] * len(var_names)
var_maxratio = [D(0)] * len(var_names)
bound_at_tau = {}
pos_after_K05 = True
bound_at_K05 = {}
for k, h in t17_rows(KMAX, IMAX):
    for i in range(1, IMAX + 1):
        if k > 0:
            pw[i] = pw[i] * rho[i]
        X = (k + 1 + u[i]) * (-(1 + D(k) / Dd[i])).exp()
        E = (-D(k) / (2 * rho[i])).exp()
        eX1 = X.exp() - 1
        B = 3 * eX1 * (1 + D('4.2') * E) + D('4.2') * E
        if k == tab18[i - 1]:
            bound_at_tau[i] = B
        if math.ceil(K05[i]) == k:
            bound_at_K05[i] = B
        if k >= math.ceil(K05[i]) and h[i] <= 0:
            pos_after_K05 = False
        if B < TINY:
            continue
        npairs += 1
        dev = abs(D(h[i]) / (cc[i] * pw[i]) - one)
        r = dev / B
        if r > max_all[0]:
            max_all = (r, (k, i))
        if k >= Kn[i] and r > max_tail[0]:
            max_tail = (r, (k, i))
        if dev > B:
            viol += 1
        # 变体
        X6 = (k + 1 + u[i]) * (-(1 + D(k) / (3 * i))).exp()
        vb = [3 * eX1 * (1 + 3 * E) + 3 * E,
              eX1 * (1 + D('4.2') * E) + D('4.2') * E,
              eX1 * (1 + 3 * E) + 3 * E,
              3 * ((X / D(math.e)).exp() - 1) * (1 + D('4.2') * E) + D('4.2') * E,
              3 * X * (1 + D('4.2') * E) + D('4.2') * E,
              3 * (X6.exp() - 1) * (1 + D('4.2') * E) + D('4.2') * E,
              3 * eX1 * (1 + D('4.2') * E)]
        for s, bv in enumerate(vb):
            if bv > 0:
                rv = dev / bv
                if rv > var_maxratio[s]:
                    var_maxratio[s] = rv
            if dev > bv:
                var_viol[s] += 1
                if var_first[s] is None:
                    var_first[s] = (k, i, float(dev), float(bv))
    if k % 500 == 0:
        print('  k=%d  %.1fs' % (k, time.time() - t0), flush=True)

report('r4-thm', viol == 0 and npairs > 1000,
       '定理 1 的不等式在 1<=i<=%d、0<=k<=%d 中界>=1e-60 的全部 %d 个 (k,i) 上成立；实际/界 的最大值 %.4f（在 (k,i)=%s）；'
       '只看 k>=K_i 时最大 %.4f（在 %s；作者在抽样点上报告 0.239）'
       % (IMAX, KMAX, npairs, float(max_all[0]), max_all[1], float(max_tail[0]), max_tail[1]))
bt = [bound_at_tau[i] for i in range(1, IMAX + 1)]
report('r4-tau', all(b >= 1 for b in bt),
       '界在 k=τ_i 处 >=1 对 1<=i<=%d 全部成立（最小 %.3f，在 i=%d；作者 b9b-rev 只查 2<=i<=100）'
       % (IMAX, float(min(bt)), 1 + bt.index(min(bt))))
lines = []
for s, nm in enumerate(var_names):
    if var_first[s] is None:
        lines.append('%s：数据上不被推翻（实际/变体界 最大 %.3f）' % (nm, float(var_maxratio[s])))
    else:
        lines.append('%s：被 %d 个点推翻，首个 (k,i)=(%d,%d)，实际 %.3g > 变体界 %.3g（实际/变体界 最大 %.3f）'
                     % (nm, var_viol[s], var_first[s][0], var_first[s][1], var_first[s][2], var_first[s][3], float(var_maxratio[s])))
report('r4-var', True, '（信息性）' + '；'.join(lines))
bk = [bound_at_K05[i] for i in range(1, IMAX + 1)]
nbad05 = sum(1 for b in bk if b >= 1)
gen05 = 3 * ((D('0.5')).exp() - 1) * (1 + D('0.042')) + D('0.042')
report('r4-026', gen05 > 1 and nbad05 > 0 and pos_after_K05,
       '0.26→0.5：证明最后一步变成 3(e^0.5−1)(1.042)+0.042=%.3f>1，推不出 <1；K_i(0.5) 约为 K_i 的 %.2f 倍，'
       '在 k=⌈K_i(0.5)⌉ 处按精确 X、E 算的定理 1 界在 1<=i<=%d 上介于 %.3f 与 %.3f，其中 %d 个 i 的界 >=1（所以不能一致地认证）；'
       '而数据上 h_{k,i}>0 对 ⌈K_i(0.5)⌉<=k<=%d 全部成立（τ_i 远小于 K_i(0.5)）。0.26 是这条证明需要的（最大可取 0.2673），不是真理需要的'
       % (float(gen05), K05[IMAX] / Kn[IMAX], IMAX, float(min(bk)), float(max(bk)), nbad05, KMAX))
print('# elapsed %.1fs' % (time.time() - t0))
print('SUMMARY s17-r4 pass=%d fail=%d' % (RES.count(True), RES.count(False)))
