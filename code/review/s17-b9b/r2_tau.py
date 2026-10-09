# -*- coding: utf-8 -*-
"""s17-b9b r2：门槛 τ_i 的独立复算（不 import 项目代码）。
阶段 A（与作者不同的算法）：U 的三项递推按 k 滚动（m<=100）+ 二项式反演 h_{k,i}=Σ_r(-1)^rC(k+1,r)U_k(i-r)，
        k<=KA（默认 3000），i<=100；每个 (k,i) 都与自写的 T1.7 截断递推对照；用我自己的 K_i 严格上界认证 τ_1..τ_100。
阶段 B（与作者不同的算法，抽查 100<i<=300）：N 三角递推（q<=301）+ h_{k,i}=Σ_q N(k,q)(-1)^{i+1-q}C(k-q,i+1-q)，
        对抽查的 i、全部 k<=⌈K_i⌉ 计算，独立确定 τ_i；同时与自写 T1.7 逐个对照。
阶段 C（同一递推、独立实现）：自写 T1.7 截断到 i<=IC，k<=KC（默认 10000，IC=1100），给出 τ_1..τ_300 全表（K_i<=10000 认证）
        与 ℓ_k（k<=10000）。
所有 τ 与 notes/18 §2 的表（按文本读入）、notes/16 定理 2 与注 2.0 的两段列表对照。
用法：py -3.14 code/review/s17-b9b/r2_tau.py A [KA]
      py -3.14 code/review/s17-b9b/r2_tau.py BC [KC] [IC] [spot,i,...]
"""
import json
import math
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s17_common import U_rows, binom_row_next, h_from_U, t17_rows, N_rows, K_bound, parse_tau_table  # noqa: E402

sys.stdout.reconfigure(encoding='utf-8')
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def notes16_lists():
    txt = open(os.path.join(ROOT, 'notes', '16-主Agent-表B-B9-符号模式与门槛.md'), encoding='utf-8').read()
    m1 = re.search(r'依次是\s*\n\s*([0-9, ]+)。', txt)
    m2 = re.search(r'τ_41,…,τ_100 = ([0-9, ]+)。', txt)
    a = [int(x) for x in m1.group(1).split(',')]
    b = [int(x) for x in m2.group(1).split(',')]
    return a, b


def phase_A(KA):
    t0 = time.time()
    I = 100
    tab18 = parse_tau_table(os.path.join(ROOT, 'notes', '18-主Agent-表B-B9-门槛的增长.md'))
    t40, t41_100 = notes16_lists()
    print('# 阶段 A：U 三项递推 + 二项式反演，k<=%d，i<=%d；notes/18 表 %d 项，notes/16 列表 %d+%d 项'
          % (KA, I, len(tab18), len(t40), len(t41_100)), flush=True)
    Kb = [None] + [K_bound(i)[0] for i in range(1, I + 1)]
    last_bad = [-1] * (I + 1)
    neq = 0
    B = [1, 1] + [0] * (I - 1)          # C(1, r)
    tgen = t17_rows(KA, I)
    for (k, Urow), (k2, Trow) in zip(U_rows(KA, I), tgen):
        assert k == k2
        if k > 0:
            B = binom_row_next(B)        # C(k+1, r)
        Bs = [(-b if r & 1 else b) for r, b in enumerate(B)]
        h = h_from_U(Urow, Bs, I)
        if h != Trow:
            neq += 1
        for i in range(1, I + 1):
            if h[i] <= 0:
                last_bad[i] = k
        if k % 500 == 0:
            print('  k=%d  %.1fs' % (k, time.time() - t0), flush=True)
    tau = [None] + [last_bad[i] + 1 for i in range(1, I + 1)]
    cert = all(math.ceil(Kb[i]) <= KA for i in range(1, I + 1))
    report('r2a-eq', neq == 0, 'U 反演 = 自写 T1.7（0<=k<=%d、0<=i<=%d 的全部 %d 个系数逐个相等）' % (KA, I, (KA + 1) * (I + 1)))
    report('r2a-cert', cert, '我的 K_i 严格上界：⌈K_i⌉<=%d 对 1<=i<=%d 成立（K_100<=%s），所以 τ_i=1+max{k<=%d: h_{k,i}<=0}'
           % (KA, I, str(Kb[I])[:9], KA))
    ok18 = tau[1:] == tab18[:I]
    ok16 = tau[1:41] == t40 and tau[41:101] == t41_100
    report('r2a-tau', ok18 and ok16, 'τ_1..τ_100（U 反演，独立算法）与 notes/18 §2 的表、notes/16 定理 2（i<=40）、注 2.0 中 s14-b9 的列表（41<=i<=100）逐个相同；τ_100=%d'
           % tau[I])
    print('# tau_1..tau_100 (U-route) = %s' % tau[1:], flush=True)
    print('# elapsed %.1fs' % (time.time() - t0))


def phase_BC(KC, IC, spots):
    t0 = time.time()
    tab18 = parse_tau_table(os.path.join(ROOT, 'notes', '18-主Agent-表B-B9-门槛的增长.md'))
    Q = max(spots) + 1
    Kb = {i: K_bound(i)[0] for i in range(1, 320)}
    Kspot = {i: math.ceil(Kb[i]) for i in spots}
    KN = max(Kspot.values())
    assert KN <= KC
    print('# 阶段 B/C：N 三角（q<=%d）抽查 i=%s（各自算到 k<=⌈K_i⌉=%s）；自写 T1.7 截断 i<=%d、k<=%d'
          % (Q, spots, [Kspot[i] for i in spots], IC, KC), flush=True)
    last_T = [-1] * (IC + 1)
    last_N = {i: -1 for i in spots}
    ell = {}
    neq, ncmp = 0, 0
    ngen = N_rows(KN, Q)
    for k, Trow in t17_rows(KC, IC):
        first = None
        for i in range(IC + 1):
            if Trow[i] <= 0:
                last_T[i] = k
                if first is None:
                    first = i
        ell[k] = first
        if k <= KN:
            kk, Nrow = next(ngen)
            assert kk == k
            for i in spots:
                if k > Kspot[i]:
                    continue
                if k <= i + 1:
                    # 小 k：直接用公式（math.comb，参数非负）
                    hv = 0
                    for q in range(1, min(i + 1, k) + 1):
                        p = i + 1 - q
                        c = math.comb(k - q, p)
                        hv += (-c if p & 1 else c) * Nrow[q]
                else:
                    n = k - i - 1               # C(k-q, i+1-q)=C(n+p, p)，p=i+1-q
                    c = 1
                    hv = Nrow[i + 1]            # p=0
                    for p in range(1, i + 1):
                        c = c * (n + p) // p
                        term = c * Nrow[i + 1 - p]
                        hv = hv - term if p & 1 else hv + term
                ncmp += 1
                if hv != Trow[i]:
                    neq += 1
                if hv <= 0:
                    last_N[i] = k
        if k % 1000 == 0:
            print('  k=%d  %.1fs' % (k, time.time() - t0), flush=True)
    tauT = [None] + [last_T[i] + 1 for i in range(1, IC + 1)]
    Imax_cert = max(i for i in range(1, 320) if math.ceil(Kb[i]) <= KC)
    report('r2b-eq', neq == 0, 'N 三角公式 = 自写 T1.7：抽查 i=%s 的全部 k<=⌈K_i⌉，共 %d 个系数逐个相等' % (spots, ncmp))
    okN = all(last_N[i] + 1 == tab18[i - 1] for i in spots)
    report('r2b-tau', okN, '抽查（N 三角，独立算法，认证到 ⌈K_i⌉）：%s 与 notes/18 表一致'
           % ', '.join('τ_%d=%d' % (i, last_N[i] + 1) for i in spots))
    okC = tauT[1:301] == tab18[:300]
    diffs = [tauT[i + 1] - tauT[i] for i in range(1, 300)]
    from collections import Counter
    cnt = Counter(diffs[7:])                      # i=8..299
    report('r2c-tau', okC and Imax_cert >= 300,
           '自写 T1.7（k<=%d）：τ_1..τ_300 与 notes/18 表逐个相同；K_i<=%d 对 i<=%d 成立（下一个 i 的 ⌈K_i⌉=%d）；'
           '8<=i<300 的相邻差 %s；窗口平均 (τ_100-τ_1)/99=%.3f、(τ_200-τ_100)/100=%.2f、(τ_300-τ_200)/100=%.2f'
           % (KC, KC, Imax_cert, math.ceil(Kb[Imax_cert + 1]), dict(sorted(cnt.items())),
              (tauT[100] - tauT[1]) / 99, (tauT[200] - tauT[100]) / 100, (tauT[300] - tauT[200]) / 100))
    out = {'tau_T': tauT[1:], 'ell': ell, 'KC': KC, 'IC': IC}
    with open(os.path.join(ROOT, 'logs', 'review_s17-b9b_r2_tau_data.json'), 'w', encoding='utf-8') as f:
        json.dump(out, f)
    print('# 数据写入 logs/review_s17-b9b_r2_tau_data.json（τ 全表与 ℓ_k）')
    print('# elapsed %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'A':
        phase_A(int(sys.argv[2]) if len(sys.argv) > 2 else 3000)
    else:
        KC = int(sys.argv[2]) if len(sys.argv) > 2 else 10000
        IC = int(sys.argv[3]) if len(sys.argv) > 3 else 1100
        spots = [int(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 else [101, 150, 223, 287, 300]
        phase_BC(KC, IC, spots)
    print('SUMMARY s17-r2-%s pass=%d fail=%d' % (mode, RES.count(True), RES.count(False)))
