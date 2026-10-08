# -*- coding: utf-8 -*-
"""复核者 s14-b8：定理 4 的独立重做——不经推论 2 的筛选，对 1<=k<=K 的一切 s_k<j<=Jcut_k 检查 U_k(-j)≢0。

方法与作者不同：作者对 j | lcm(1..k) 的候选用 N 基 Σ(-1)^q N(k,q)C(j+q-2,q) 模 P1 求值；这里用 G_{-j} 递推
  G_{-1}=1，G_{-j-1}=(1-x+jx^3)G_{-j}+jx^2（c5a 定理 4.3），截到 x^K，同时模三个素数（行 0、1 是复核者自选的素数，行 2 是作者的 P1，
只用来顺带核对「模 P1 从未出现 0」），按 j 逐步推进，每一步检查窗口 s_k<j<=Jcut_k 里的全部 k。
Jcut_k:=max_q ceil θ_q 由自己的精确 N 表算（k>=4 时 = J_k）。窗口里某一行为 0 就记下，三行都为 0 就用精确整数复算。
端到端核对：每个 k 在 j=s_k+1、中点、Jcut_k、Jcut_k+1 处的三行余数 = 牛顿基精确多项式值的余数。
反向检查：在 (k0,j0) 处把被检查的值减去 U_{k0}(-j0) 的余数，必须恰好在那里报零。
用法：py -3.14 code/review/s14-b8/r3_gneg_modp_scan.py [K=300]
"""
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import b8lib as L  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

K = int(sys.argv[1]) if len(sys.argv) > 1 else 300
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


T0 = time.time()
P_A, P1, P2 = 2147483647, 2147483629, 2147483587
cands = []
x = 2 ** 31 - 1
while len(cands) < 1:
    x -= 1
    if x not in (P_A, P1, P2) and L.is_prime_td(x):
        cands.append(x)
P_C = cands[0]
PR = [P_A, P_C, P1]
assert all(L.is_prime_td(p) for p in PR)
P = np.array(PR, dtype=np.int64)[:, None]
print('K=%d，素数行：%s（P_A、P_C 为复核者自选，第三行为作者的 P1）' % (K, PR), flush=True)

UR = L.U_rec_table(K, K + 1)
N = [L.N_row(UR[k], k) for k in range(K + 1)]
D = [L.newton_coeffs(UR[k], k) for k in range(K + 1)]
Jc = [0] + [L.Jcut(N[k], k) for k in range(1, K + 1)]
okJ = all(Jc[k] == L.J_formula(k) for k in range(4, K + 1)) and Jc[1:4] == [1, 1, 5]
s = [0] + [L.s_of(k) for k in range(1, K + 1)]
JEND = max(Jc) + 1
total_window = sum(max(0, Jc[k] - s[k]) for k in range(1, K + 1))
print('Jcut_k=J_k（k>=4）%s；窗口总数 Σ_k (Jcut_k-s_k) = %d；JEND=%d（%.0fs）' % (okJ, total_window, JEND, time.time() - T0), flush=True)

# 端到端核对点
CK = {}
for k in range(1, K + 1):
    for jj in {s[k] + 1, (s[k] + 1 + Jc[k]) // 2, Jc[k], Jc[k] + 1}:
        if jj >= 1:
            CK.setdefault(jj, []).append(k)
EXP = {}
for jj, ks in CK.items():
    for k in ks:
        v = L.eval_newton(D[k], -jj)
        EXP[(jj, k)] = [v % p for p in PR]
print('核对点 %d 个已算好（%.0fs）' % (len(EXP), time.time() - T0), flush=True)

# 反向检查的人为零点
K0, J0 = min(150, K), 777777 if K >= 150 else 400
INJ = np.array([L.eval_newton(D[K0], -J0) % p for p in PR], dtype=np.int64)

g = np.zeros((3, K + 1), dtype=np.int64)
g[:, 0] = 1                       # G_{-1}
zero_events = []                  # (j, k, 哪些行为 0)
end_bad, n_end = [], 0
triv_ok = True
inj_found = None
n_checked = 0
kmin = 1
t = time.time()
for jj in range(1, JEND + 1):
    if jj >= 2:
        j = jj - 1                # 由 G_{-j} 得 G_{-(j+1)}
        s3 = j * g[:, :-3]
        g[:, 1:] -= g[:, :-1]
        g[:, 3:] += s3
        g[:, 2] += j
        np.remainder(g, P, out=g)
    # 平凡零点 k>=3jj-2
    lo_t = max(1, 3 * jj - 2)
    if lo_t <= K:
        triv_ok &= bool((g[:, lo_t:] == 0).all())
    hi = min(K, 3 * jj - 3)
    while kmin <= K and Jc[kmin] < jj:
        kmin += 1
    if kmin <= hi:
        seg = g[:, kmin:hi + 1]
        n_checked += hi - kmin + 1
        if not seg.all():
            zr = np.nonzero(~seg.all(axis=0))[0]
            for i in zr:
                zero_events.append((jj, kmin + int(i), [int(seg[r, i] == 0) for r in range(3)]))
        if jj == J0 and kmin <= K0 <= hi:
            col = (seg[:, K0 - kmin] - INJ) % P[:, 0]
            inj_found = bool((col == 0).all())
    if jj in CK:
        for k in CK[jj]:
            n_end += 1
            got = [int(v) for v in g[:, k]]
            if got != EXP[(jj, k)]:
                end_bad.append((jj, k))
    if jj % 1000000 == 0:
        print('  j=%d（%.0fs，已查 %d 个 (k,j)，零事件 %d）' % (jj, time.time() - t, n_checked, len(zero_events)), flush=True)

# 三行都为 0 的事件用精确整数复算
true_zeros = []
for (jj, k, rows) in zero_events:
    if all(rows):
        if L.eval_newton(D[k], -jj) == 0:
            true_zeros.append((k, jj))
row_zero_counts = [sum(1 for e in zero_events if e[2][r]) for r in range(3)]


def divides_lcm(j, k):
    return L.lcm_upto(k) % j == 0


p1_cand_zeros = [(jj, k) for (jj, k, rows) in zero_events if rows[2] and divides_lcm(jj, k)]
report('m-scan', not true_zeros and n_checked == total_window and okJ,
       '不经筛选：1<=k<=%d、s_k<j<=Jcut_k 的全部 %d 个 (k,j)，U_k(-j) 模 %s 的余数三行同时为 0 的有 %d 个，精确复算后真零点 %s；'
       '各行单独为 0 的次数 %s（期望各约 %.2f）；零事件 %s'
       % (K, n_checked, PR, sum(1 for e in zero_events if all(e[2])), true_zeros or '无', row_zero_counts,
          total_window / P_A, zero_events[:10]))
report('m-p1', not p1_cand_zeros,
       '顺带：作者的候选（j | lcm(1..k)）中模 P1=%d 为 0 的个数 %d（作者说「P2 一次也没用到」，等价于这个数为 0）' % (P1, len(p1_cand_zeros)))
report('m-end', not end_bad and n_end == len(EXP) and triv_ok,
       '端到端：%d 个核对点（每个 k 的 j=s_k+1、中点、Jcut_k、Jcut_k+1）三行余数 = 牛顿基精确值的余数 %s；j<=s_k 时三行全为 0 %s'
       % (n_end, not end_bad, triv_ok))
report('m-rev', inj_found is True, '反向：在 (k,j)=(%d,%d) 处减去 U_k(-j) 的余数后三行同时为 0（被抓到）%s' % (K0, J0, inj_found))
print('total %.0fs' % (time.time() - T0))
n_pass = sum(RES)
print('SUMMARY s14-b8-r3 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
sys.exit(0 if n_pass == len(RES) else 1)
