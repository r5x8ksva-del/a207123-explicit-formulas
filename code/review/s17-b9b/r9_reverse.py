# -*- coding: utf-8 -*-
"""s17-b9b r9：反向检查——我自己的检查在「故意改坏」时会不会报错（不 import 项目代码）。
  v1 U 的三项递推里 m·U_{k-3} 改成 (m+1)·U_{k-3}：τ_1..τ_40 与 notes/18 的表不再一致
  v2 N 三角递推里 (q-1) 改成 q：N 公式算出的 h 与 T1.7 不再相等
  v3 自写 T1.7 里 (k-2) 改成 (k-3)：与 U 的反演不再相等
  v4 τ 的表改一个数（τ_57+1）：r2 的对照会失败
  v5 根计数：把 h_300 乘上 (t+1/2)^2+10^-6（在 (−1,0) 附近加一对复根）后，Descartes 上界比介值定理下界多 2，
     「下界=上界」的精确性判据失败——说明 r6 不是只靠 Descartes（只靠 Descartes 就要用到 A19）
  v6 K_i 的常数 0.26 换成 0.5 时，K_i 变小，但定理 1 的最后一步（r4-026）不成立——由 r4 记录，这里只核对 K 的变化方向
用法：py -3.14 code/review/s17-b9b/r9_reverse.py
"""
import math
import os
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s17_common import U_rows, binom_row_next, h_from_U, t17_rows, t17_full, N_rows, h_from_N, K_bound, parse_tau_table  # noqa: E402
from rootlib import desc_count, sign_at  # noqa: E402

sys.stdout.reconfigure(encoding='utf-8')
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


t00 = time.time()
tab = parse_tau_table(os.path.join(ROOT, 'notes', '18-主Agent-表B-B9-门槛的增长.md'))


def tau_via_U(KA, I, mutate=None):
    last = [-1] * (I + 1)
    B = [1, 1] + [0] * (I - 1)
    for k, Urow in U_rows(KA, I, mutate=mutate):
        if k > 0:
            B = binom_row_next(B)
        Bs = [(-b if r & 1 else b) for r, b in enumerate(B)]
        h = h_from_U(Urow, Bs, I)
        for i in range(1, I + 1):
            if h[i] <= 0:
                last[i] = k
    return [last[i] + 1 for i in range(1, I + 1)]


good = tau_via_U(1200, 40)
bad = tau_via_U(1200, 40, mutate=lambda m: m + 1)
report('r9-v1', good == tab[:40] and bad != tab[:40],
       '正常的 U 反演 τ_1..τ_40 与表一致；把 m·U_{k-3} 改成 (m+1)·U_{k-3} 后不一致（前 6 项 %s）' % bad[:6])


# v2：N 三角改坏
def N_rows_bad(K, Q):
    base = {0: [1] + [0] * Q, 1: [0, 1] + [0] * (Q - 1), 2: [0, 1, 2] + [0] * (Q - 2)}
    prev = {}
    for k in range(0, K + 1):
        if k <= 2:
            row = base[k][:Q + 1]
        else:
            p1, p3 = prev[k - 1], prev[k - 3]
            row = [0] * (Q + 1)
            for q in range(1, Q + 1):
                t = (p3[q - 2] if q >= 2 else 0) + 2 * p3[q - 1] + p3[q]
                row[q] = p1[q - 1] + p1[q] + q * t
        prev[k] = row
        prev.pop(k - 4, None)
        yield k, row


T = {k: r for k, r in t17_rows(120, 40)}
okN = all(h_from_N(k, r, i) == T[k][i] for k, r in N_rows(120, 41) if k >= 1 for i in range(41))
badN = sum(1 for k, r in N_rows_bad(120, 41) if k >= 1 for i in range(41) if h_from_N(k, r, i) != T[k][i])
report('r9-v2', okN and badN > 0, '正常的 N 公式与 T1.7 在 k<=120、i<=40 全部相等；(q-1) 改成 q 后有 %d 个系数不等' % badN)

# v3：T1.7 改坏
Ug = {}
B = [1, 1] + [0] * 39
for k, Urow in U_rows(120, 40):
    if k > 0:
        B = binom_row_next(B)
    Ug[k] = h_from_U(Urow, [(-b if r & 1 else b) for r, b in enumerate(B)], 40)
badT = sum(1 for k, r in t17_rows(120, 40, kshift=-3) for i in range(41) if r[i] != Ug[k][i])
report('r9-v3', badT > 0, '自写 T1.7 的 (k-2) 改成 (k-3) 后与 U 的反演有 %d 个系数不等' % badT)

# v4：表改一个数
tab2 = tab[:]
tab2[56] += 1
report('r9-v4', good == tab[:40] and tau_via_U(1700, 60) != tab2[:60],
       'τ_57 改成 %d 后，U 反演算出的 τ_1..τ_60 与改过的表不一致' % tab2[56])

# v5：根计数的精确性判据
h = None
for k, hh in t17_full(300):
    h = hh
# 乘 (t+1/2)^2+10^-6 = t^2 + t + 1/4 + 10^-6；整数化：乘 4·10^6
c = [10 ** 6 + 4, 4 * 10 ** 6, 4 * 10 ** 6]          # (4·10^6)(t^2+t+1/4+10^-6) 的系数，低次在前
hp = [0] * (len(h) + 2)
for i, a in enumerate(h):
    for j, b in enumerate(c):
        hp[i + j] += a * b
spts = set()
for e in range(-400, 0):                      # s=-t：2^-400..1，主体每倍程 256 点、尾部 16/4 点（同 r6）
    per = 256 if e >= -12 else (16 if e >= -80 else 4)
    base = Fr(2) ** e
    for m in range(per):
        spts.add(base * (1 + Fr(m, per)))
spts.add(Fr(1))
pts = [-x for x in sorted(spts, reverse=True)] + [Fr(0)]
sg = [sign_at(hp, x) for x in pts]
L = sum(1 for a, b in zip(sg, sg[1:]) if a != b)
U = desc_count(hp, -1, 0)
L0 = sum(1 for a, b in zip([sign_at(h, x) for x in pts], [sign_at(h, x) for x in pts][1:]) if a != b)
U0 = desc_count(h, -1, 0)
report('r9-v5', L0 == U0 and U == L + 2,
       'h_300 在 (−1,0) 中：下界 %d = 上界 %d；乘上 (t+1/2)^2+10^-6 后下界 %d、上界 %d（多出的 2 是那对复根），判据「下界=上界」随即失败' % (L0, U0, L, U))

# v6：K 的方向
k26 = K_bound(100)[0]
k50 = K_bound(100, '0.5')[0]
report('r9-v6', k50 < k26, 'K_100(0.26)=%.1f，K_100(0.5)=%.1f（常数改大时 K 变小；r4-026 记录了这时证明的最后一步不成立）' % (k26, k50))
print('# elapsed %.1fs' % (time.time() - t00))
print('SUMMARY s17-r9 pass=%d fail=%d' % (RES.count(True), RES.count(False)))
