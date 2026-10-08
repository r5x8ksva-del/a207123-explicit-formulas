# -*- coding: utf-8 -*-
"""复核者 s14-b8：用 G_{-j} 递推（c5a 定理 4.3）精确地、不经推论 2 的筛选检查 B8，并核对定理 3 的符号与 notes/05 的变号界。

对 1<=k<=K、1<=j<=J_K+EXTRA 逐个算精确整数 U_k(-j)（G_{-j-1}=(1-x+jx^3)G_{-j}+jx^2 截到 x^K），检查：
  w-zero   s_k<j<=Jcut_k（Jcut_k:=max_q ceil θ_q，由自己的 N 表算；k>=4 时等于 J_k）时 U_k(-j)!=0（不经任何筛选）；
  w-triv   1<=j<=s_k 时 U_k(-j)=0；
  w-sign   j>Jcut_k 时 (-1)^k U_k(-j)>0（定理 3 的结论，直到 j=J_K+EXTRA）；
  w-chg    j>s_k 时数列 U_k(-j) 的变号次数 <= floor(k/3)（notes/05 §4）；并报告 (-1)^kU_k(-j)<=0 的最后一个 j 与 J_k 之比；
  w-cor2   j<=JC 时，对每个满足 p^{v_p(j)}>k 的素数 p，U_k(-j)≡1 (mod p)（推论 2，大规模）；
  w-end    每个 k 在 j=Jcut_k 与 Jcut_k+1 处的递推值 = 牛顿基多项式值（端到端核对递推实现）；
  w-rev    反向：在 (k0,j0) 处人为把被检查的值减去 U_{k0}(-j0)，零点检查必须恰好抓到这一个。
用法：py -3.14 code/review/s14-b8/r2_gneg_exact.py [K=100] [EXTRA=3000] [JC=60000]
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import b8lib as L  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

K = int(sys.argv[1]) if len(sys.argv) > 1 else 100
EXTRA = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
JC = int(sys.argv[3]) if len(sys.argv) > 3 else 60000
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


T0 = time.time()
UR = L.U_rec_table(K, K + 1)
N = [L.N_row(UR[k], k) for k in range(K + 1)]
D = [L.newton_coeffs(UR[k], k) for k in range(K + 1)]
Jc = [0] + [L.Jcut(N[k], k) for k in range(1, K + 1)]
okJ = all(Jc[k] == L.J_formula(k) for k in range(4, K + 1)) and Jc[1:4] == [1, 1, 5]
okmono = all(Jc[k] <= Jc[k + 1] for k in range(1, K))
s = [0] + [L.s_of(k) for k in range(1, K + 1)]
JEND = L.J_formula(K) + EXTRA
print('K=%d JEND=%d JC=%d；Jcut 与公式一致 %s，单调 %s' % (K, JEND, JC, okJ, okmono), flush=True)

# 推论 2 用的最小素因子表
spf = list(range(JC + 1))
for i in range(2, int(JC ** 0.5) + 1):
    if spf[i] == i:
        for mlt in range(i * i, JC + 1, i):
            if spf[mlt] == mlt:
                spf[mlt] = i


def factor(n):
    out = []
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        out.append((p, p ** e))
    return out


# 反向检查的人为零点
K0, J0 = min(45, K), min(400, Jc[min(45, K)])
INJ = L.eval_newton(D[K0], -J0)

CK = {}
for k in range(1, K + 1):
    for jj in (Jc[k], Jc[k] + 1):
        CK.setdefault(jj, []).append(k)

# 候选判定用的 lpp(j)=max_p p^{v_p(j)}（j 有 >K 的素因子时记为无穷大）
import numpy as np  # noqa: E402
_rem = np.arange(JEND + 1, dtype=np.int64)
_lpp = np.ones(JEND + 1, dtype=np.int64)
for _p in L.primes_upto(K):
    _pe = _p
    while _pe <= JEND:
        _sl = slice(_pe, JEND + 1, _pe)
        _rem[_sl] //= _p
        _lpp[_sl] = np.maximum(_lpp[_sl], _pe)
        _pe *= _p
_lpp[_rem != 1] = 10 ** 12
LPP = _lpp.tolist()
del _rem, _lpp
# 统计：窗口内 |U_k(-j)| 的最小位长（全部 j 与候选 j），以及启发式「偶然为 0 的概率」Σ 1/|U|（按 2^{1-位长} 近似）
minb_all = [10 ** 9] * (K + 1)
minb_cand = [10 ** 9] * (K + 1)
argmin_cand = [None] * (K + 1)
heur_cand = [0.0] * (K + 1)

n_win, zeros_win, inj_hit = 0, [], []
n_triv, bad_triv = 0, []
n_sign, bad_sign = 0, []
n_c2, bad_c2 = 0, 0
prev = [0] * (K + 1)
chg = [0] * (K + 1)
last_np = [None] * (K + 1)     # (-1)^k U_k(-j) <= 0 的最后一个 j（j>s_k）
end_ok, n_end = True, 0
kmin = 1
t = time.time()
for j, g in L.gneg_iter(K, JEND):
    # 平凡零点：j<=s_k ⟺ k>=3j-2
    for k in range(max(1, 3 * j - 2), K + 1):
        n_triv += 1
        if g[k] != 0:
            bad_triv.append((k, j))
    hi = min(K, 3 * j - 3)            # j>s_k ⟺ k<=3j-3
    while kmin <= K and Jc[kmin] < j:
        kmin += 1
    # 窗口 s_k<j<=Jcut_k：k∈[kmin, hi]
    for k in range(kmin, hi + 1):
        n_win += 1
        v = g[k]
        if k == K0 and j == J0:
            if v - INJ == 0:
                inj_hit.append((k, j))
        if v == 0:
            zeros_win.append((k, j))
        bl = v.bit_length()
        if bl < minb_all[k]:
            minb_all[k] = bl
        if LPP[j] <= k:
            if bl < minb_cand[k]:
                minb_cand[k] = bl
                argmin_cand[k] = j
            if bl < 1070:
                heur_cand[k] += 2.0 ** (1 - bl)
    # 窗口以外、j>s_k：k<kmin（Jcut_k<j），检查符号；同时统计变号
    for k in range(1, hi + 1):
        v = g[k]
        sg = (v > 0) - (v < 0)
        if prev[k] != 0 and sg != 0 and sg != prev[k]:
            chg[k] += 1
        if sg != 0:
            prev[k] = sg
        pos = (sg == 1) if k % 2 == 0 else (sg == -1)
        if not pos:
            last_np[k] = j
        if k < kmin:
            n_sign += 1
            if not pos:
                bad_sign.append((k, j))
    # 端到端：j=Jcut_k、Jcut_k+1
    if j in CK:
        for k in CK[j]:
            n_end += 1
            end_ok &= (g[k] == L.eval_newton(D[k], -j))
    # 推论 2（大规模）
    if j <= JC:
        fac = factor(j)
        for k in range(1, K + 1):
            for p, pe in fac:
                if pe > k:
                    n_c2 += 1
                    if g[k] % p != 1 % p:
                        bad_c2 += 1
    if j % 100000 == 0:
        print('  j=%d (%.0fs)' % (j, time.time() - t), flush=True)

report('w-zero', not zeros_win and okJ,
       '不经筛选：1<=k<=%d、s_k<j<=Jcut_k 的全部 %d 个 (k,j) 精确 U_k(-j)!=0（零点 %s）；Jcut_k=J_k（k>=4）%s'
       % (K, n_win, zeros_win[:5] or '无', okJ))
report('w-triv', not bad_triv, '1<=j<=s_k 时 U_k(-j)=0：%d 个，失败 %d' % (n_triv, len(bad_triv)))
report('w-sign', not bad_sign,
       '定理 3：J_k<j<=%d 时 (-1)^k U_k(-j)>0（1<=k<=%d，共 %d 个 (k,j)），失败 %d %s' % (JEND, K, n_sign, len(bad_sign), bad_sign[:5]))
okchg = all(chg[k] <= k // 3 for k in range(1, K + 1))
eq = sum(1 for k in range(1, K + 1) if chg[k] == k // 3)
ratios = ['k=%d:%s/%d' % (k, last_np[k], Jc[k]) for k in range(10, K + 1, 10)]
report('w-chg', okchg,
       'notes/05：j>s_k（直到 %d）时 U_k(-j) 变号次数 <= floor(k/3)（k<=%d）%s，其中恰等于 floor(k/3) 的 k 有 %d 个；'
       '(-1)^kU_k(-j)<=0 的最后一个 j / J_k：%s' % (JEND, K, okchg, eq, ', '.join(ratios)))
report('w-cor2', bad_c2 == 0, '推论 2：j<=%d、p^{v_p(j)}>k 时 U_k(-j)≡1 (mod p)（1<=k<=%d）：%d 组，失败 %d' % (JC, K, n_c2, bad_c2))
report('w-end', end_ok and n_end == 2 * K, '端到端：j=Jcut_k、Jcut_k+1 处递推值 = 牛顿基多项式值（%d 个）' % n_end)
report('w-rev', inj_hit == [(K0, J0)], '反向：把 (k,j)=(%d,%d) 处的值减去 U_%d(-%d) 后零点检查抓到 %s' % (K0, J0, K0, J0, inj_hit))
print('统计（启发式，不是证明）：k, 窗口内 min log10|U_k(-j)|（全部 j）, 候选中的 min log10|U| 与取到的 j, 候选上 Σ1/|U| 的估计')
for k in list(range(4, 21)) + list(range(25, K + 1, 5)):
    if k > K:
        break
    print('  k=%d  all:%.1f  cand:%.1f (j=%s)  heur:%.2e' % (k, (minb_all[k] - 1) * 0.30103, (minb_cand[k] - 1) * 0.30103,
                                                         argmin_cand[k], heur_cand[k]))
tot_heur = sum(heur_cand[4:])
print('  Σ_k 启发式期望（4<=k<=%d）= %.3e；k>=20 部分 = %.3e' % (K, tot_heur, sum(heur_cand[20:])))
print('total %.0fs' % (time.time() - T0))
n_pass = sum(RES)
print('SUMMARY s14-b8-r2 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
sys.exit(0 if n_pass == len(RES) else 1)
