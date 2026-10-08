# -*- coding: utf-8 -*-
"""复核者 s14-b8：(1) 用筛法（不是作者的 DFS 因子枚举）独立数候选个数；(2) 用另一个素数、另一种求值（k!·u_k(m) 的单项式系数 + Horner）
在候选上重做定理 4 的一部分，系数只来自按定义的转移 DP（模 P_D），不经过 N 表和任何递推。

(1) 候选 = {j : s_k<j<=Jcut_k，j 的每个素数幂因子 <=k}（⟺ j | lcm(1..k)）。对 j<=J_300 筛出 lpp(j):=max_p p^{v_p(j)}（只对 300-光滑的 j），
    j 对 k 是候选 ⟺ max(lpp(j), kJ(j)) <= k <= min(300, 3j-3)，kJ(j):=min{k: Jcut_k>=j}；用差分数组得到每个 k 的个数。
    与作者 explore_b8_scan 日志的逐 25 个 k 的个数、累计数、总数 71,660,856 对照。
(2) Horner：c-dp 按定义 DP 模 P_D 得 U_k(0..300)；c-coef 由牛顿差分换成 k!·u_k 的单项式系数；c-horner 对 k<=150 的全部候选与
    k=175,200,...,300 的全部候选求值；c-valid 求值器在 1<=j<=s_k 给 0、在 j=s_k+1、Jcut_k 处与精确值一致；c-rev 改坏一个系数后 c-valid 失败。
用法：py -3.14 code/review/s14-b8/r4_candidates_horner.py
"""
import os
import sys
import time
from math import factorial

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import b8lib as L  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


T0 = time.time()
K = 300
UR = L.U_rec_table(K, K + 1)
N = [L.N_row(UR[k], k) for k in range(K + 1)]
D = [L.newton_coeffs(UR[k], k) for k in range(K + 1)]
Jc = np.array([0] + [L.Jcut(N[k], k) for k in range(1, K + 1)], dtype=np.int64)
s = np.array([0] + [L.s_of(k) for k in range(1, K + 1)], dtype=np.int64)
JMAX = int(Jc.max())

# ---------------------------------------------------------------- (1) 筛法数候选
t = time.time()
rem = np.arange(JMAX + 1, dtype=np.int64)
lpp = np.ones(JMAX + 1, dtype=np.int64)
for p in L.primes_upto(K):
    pe = p
    while pe <= JMAX:
        sl = slice(pe, JMAX + 1, pe)
        rem[sl] //= p
        lpp[sl] = np.maximum(lpp[sl], pe)
        pe *= p
smooth = (rem == 1)
smooth[0] = False
del rem
js = np.nonzero(smooth)[0].astype(np.int64)
js = js[js >= 2]
lpp_js = lpp[js]
del lpp, smooth
kJ = np.searchsorted(Jc[1:], js, side='left') + 1      # min{k: Jcut_k >= j}（Jcut 单调不减）
lower = np.maximum(lpp_js, kJ)
upper = np.minimum(K, 3 * js - 3)
valid = lower <= upper
diff = np.zeros(K + 3, dtype=np.int64)
np.add.at(diff, lower[valid], 1)
np.add.at(diff, upper[valid] + 1, -1)
cnt = np.cumsum(diff)[:K + 1]
print('300-光滑的 j<=%d 共 %d 个；筛法用时 %.0fs' % (JMAX, len(js), time.time() - t), flush=True)

author_k = {25: 599, 50: 4730, 75: 15450, 100: 33313, 125: 68534, 150: 118425,
            175: 191894, 200: 293256, 225: 384827, 250: 537791, 275: 725805, 300: 946320}
author_cum150 = {25: 4040, 50: 60687, 75: 295253, 100: 907193, 125: 2201507, 150: 4565834}
author_cum151 = {175: 3857367, 200: 9823314, 225: 18242008, 250: 29981137, 275: 45882776, 300: 67095022}
ok_k = all(int(cnt[k]) == v for k, v in author_k.items())
ok_c1 = all(int(cnt[1:k + 1].sum()) == v for k, v in author_cum150.items())
ok_c2 = all(int(cnt[151:k + 1].sum()) == v for k, v in author_cum151.items())
total = int(cnt[1:].sum())
win = int(sum(max(0, int(Jc[k]) - int(s[k])) for k in range(1, K + 1)))
# 直接法抽查：小 k 用定义逐个数
ok_direct = True
for k in list(range(1, 41)) + [60, 97]:
    Lk = L.lcm_upto(k)
    c = sum(1 for j in range(int(s[k]) + 1, int(Jc[k]) + 1) if Lk % j == 0)
    ok_direct &= (c == int(cnt[k]))
report('c-count', ok_k and ok_c1 and ok_c2 and total == 71660856 and ok_direct,
       '候选个数（筛法）与作者一致：逐 25 个 k %s、累计（k<=150 与 151..300）%s/%s、总数 %d（笔记 71,660,856）；k<=40、60、97 用 L_k%%j 逐个数一致 %s；'
       'k=150：%d/%d，k=300：%d/%d；全部候选占窗口 Σ(J_k-s_k)=%d 的 %.2f%%'
       % (ok_k, ok_c1, ok_c2, total, ok_direct, cnt[150], Jc[150], cnt[300], Jc[300], win, 100.0 * total / win))

# p=2 的附带加强能再去掉多少候选（k∈{2^e,2^e+1} 时去掉 2^e | j 的候选）
extra = []
for e in range(2, 9):
    for k in (2 ** e, 2 ** e + 1):
        if k > K:
            continue
        m = js[(lpp_js <= k) & (js > s[k]) & (js <= Jc[k])]
        extra.append((k, int(cnt[k]), int(np.count_nonzero(m % (2 ** e) == 0))))
print('附带：p=2 的加强可去掉的候选 (k, 候选数, 被 2^e 整除的个数)：%s' % extra, flush=True)

# ---------------------------------------------------------------- (2) Horner
P_A, P1, P2, P_C = 2147483647, 2147483629, 2147483587, 2147483579
x = 2 ** 31 - 1
P_D = None
while P_D is None:
    x -= 1
    if x not in (P_A, P1, P2, P_C) and L.is_prime_td(x):
        P_D = x
t = time.time()
V = L.U_dp_modp_all(K, K, P_D)
ok_v = all(int(V[k, m]) == UR[k][m] % P_D for k in range(K + 1) for m in range(K + 1))
report('c-dp', ok_v, '按定义 DP 模 P_D=%d 的 U_k(m)（k,m<=300）= 自推递推表的余数（第二个素数上重复 r1 的 A4）(%.0fs)' % (P_D, time.time() - t))


def coeffs_kfact(k):
    """k!·u_k(m) 模 P_D 的单项式系数（升幂），只用 V[k,0..k]。"""
    P = P_D
    vals = [int(V[k, m]) for m in range(k + 1)]
    d = list(vals)
    dq = [d[0]]
    for _ in range(k):
        d = [(d[i + 1] - d[i]) % P for i in range(len(d) - 1)]
        dq.append(d[0])
    kf = factorial(k)
    c = np.zeros(k + 1, dtype=np.int64)
    ff = np.zeros(k + 2, dtype=np.int64)
    ff[0] = 1                                     # m 的下降阶乘 m(m-1)...(m-q+1)，从 q=0 开始
    for q in range(k + 1):
        w = (dq[q] * ((kf // factorial(q)) % P)) % P
        c = (c + w * ff[:k + 1]) % P
        nf = np.zeros(k + 2, dtype=np.int64)       # ff·(m-q)
        nf[1:] = ff[:-1]
        nf = (nf - q * ff) % P
        ff = nf
    return c


def horner(c, jarr):
    P = P_D
    xv = (P - (jarr % P)) % P
    acc = np.full(len(jarr), int(c[-1]), dtype=np.int64)
    for i in range(len(c) - 2, -1, -1):
        acc = (acc * xv + int(c[i])) % P
    return acc


t = time.time()
COEF = {}
ok_valid = True
for k in range(1, K + 1):
    c = coeffs_kfact(k)
    COEF[k] = c
    triv = horner(c, np.arange(1, int(s[k]) + 1, dtype=np.int64)) if s[k] >= 1 else np.zeros(0)
    ok_valid &= bool((triv == 0).all())
    for jj in (int(s[k]) + 1, int(Jc[k])):
        exact = (factorial(k) * L.eval_newton(D[k], -jj)) % P_D
        ok_valid &= (int(horner(c, np.array([jj], dtype=np.int64))[0]) == exact)
report('c-valid', ok_valid, '求值器：1<=j<=s_k 时为 0，j=s_k+1、Jcut_k 处 = k!·精确值的余数（1<=k<=300）(%.0fs)' % (time.time() - t))

t = time.time()
ks = list(range(1, 151)) + [175, 200, 225, 250, 275, 300]
ncand, zeros = 0, []
for k in ks:
    m = js[(lpp_js <= k) & (js > s[k]) & (js <= Jc[k])]
    ncand += len(m)
    r = horner(COEF[k], m)
    z = np.nonzero(r == 0)[0]
    for i in z:
        jj = int(m[i])
        if L.eval_newton(D[k], -jj) == 0:
            zeros.append((k, jj))
        else:
            zeros.append((k, jj, 'accidental'))
report('c-horner', not [z for z in zeros if len(z) == 2],
       '候选上的 Horner 求值（模 P_D，系数只来自按定义的 DP）：k<=150 全部与 k=175,200,...,300 全部，共 %d 个 j，余数为 0 的 %s (%.0fs)'
       % (ncand, zeros or '无', time.time() - t))

# 反向：改坏 k=100 的常数项
cb = COEF[100].copy()
cb[0] = (cb[0] + 1) % P_D
rv = not bool((horner(cb, np.arange(1, int(s[100]) + 1, dtype=np.int64)) == 0).all())
# 反向：人为零点
m100 = js[(lpp_js <= 100) & (js > s[100]) & (js <= Jc[100])]
j0 = int(m100[len(m100) // 2])
cz = COEF[100].copy()
cz[0] = (cz[0] - int(horner(COEF[100], np.array([j0], dtype=np.int64))[0])) % P_D
rz = horner(cz, m100)
rv2 = (np.count_nonzero(rz == 0) >= 1) and int(rz[len(m100) // 2]) == 0
report('c-rev', rv and rv2, '反向：k=100 的常数项加 1 后平凡零点检查失败 %s；把常数项减去 j0=%d 处的值后扫描在 j0 报零 %s' % (rv, j0, rv2))
print('total %.0fs' % (time.time() - T0))
n_pass = sum(RES)
print('SUMMARY s14-b8-r4 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
sys.exit(0 if n_pass == len(RES) else 1)
