# -*- coding: utf-8 -*-
"""复核者 s14-b8：真值、定理 1/推论 2、定理 3、命题 5 的点值、§5 的反演式、素数与 Miller–Rabin 说法。

不 import 项目代码；真值从定义出发（暴力枚举 + 转移 DP），快速精确表用自己推导的递推，并逐项对照 DP。
逐条打印 PASS/FAIL，最后一行 SUMMARY。用法：py -3.14 code/review/s14-b8/r1_truth_theory.py
"""
import os
import random
import sys
import time
from fractions import Fraction as Fr
from math import comb

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import b8lib as L  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


P_A = 2147483647
P1, P2 = 2147483629, 2147483587   # 作者用的两个素数（只用来核对它们是素数）
KMAX = 300
T0 = time.time()

# ================================================================ A. 真值
# A1 暴力枚举 vs 转移 DP
ok = True
for k in range(0, 9):
    for m in range(0, 4):
        ok &= (L.U_brute(k, m) == L.U_dp_exact_row(k, m)[k])
for k in range(0, 7):
    for m in range(4, 6):
        ok &= (L.U_brute(k, m) == L.U_dp_exact_row(k, m)[k])
report('A1-brute-dp', ok, '按定义暴力枚举 = 转移 DP（k<=8,m<=3；k<=6,m<=5）')

# A2 N 暴力 vs 由 DP 反演
ok = True
for k in range(0, 8):
    rows = [L.U_dp_exact_row(k, m)[k] for m in range(0, k + 1)]
    ok &= (L.N_brute(k) == L.N_row(rows, k))
report('A2-N-brute', ok, 'N(k,q) 暴力枚举（值域恰为 {1..q} 的合法词）= 由 DP 值反演（k<=7）')

# A3 精确 DP vs 自推递推表（k,m<=60）
t = time.time()
UR = L.U_rec_table(KMAX, KMAX + 40)
ok = True
for m in range(0, 61):
    row = L.U_dp_exact_row(60, m)
    ok &= all(row[k] == UR[k][m] for k in range(0, 61))
report('A3-rec-vs-dp-exact', ok, '自推递推表 = 按定义 DP 的精确值（0<=k<=60, 0<=m<=60）(%.1fs)' % (time.time() - t))

# A4 自推递推表 vs 按定义 DP 模 P_A（k,m<=300）
t = time.time()
V = L.U_dp_modp_all(KMAX, KMAX, P_A)
ok = all(int(V[k, m]) == UR[k][m] % P_A for k in range(KMAX + 1) for m in range(KMAX + 1))
report('A4-rec-vs-dp-modp', ok, '自推递推表 ≡ 按定义 DP（模 %d，0<=k<=300, 0<=m<=300，共 %d 个值）(%.1fs)'
       % (P_A, (KMAX + 1) ** 2, time.time() - t))

# A5 N 表（k<=300）
t = time.time()
N = [L.N_row(UR[k], k) for k in range(KMAX + 1)]
D = [L.newton_coeffs(UR[k], k) for k in range(KMAX + 1)]
ok_basic = all(N[k][0] == (1 if k == 0 else 0) for k in range(KMAX + 1))
ok_basic &= all(N[k][1] == 1 for k in range(1, KMAX + 1))
ok_basic &= all(N[k][k] == 2 for k in range(2, KMAX + 1))
ok_basic &= all(N[k][k - 1] == k * k - k - 4 for k in range(4, KMAX + 1))
ok_pos = all(N[k][q] > 0 for k in range(1, KMAX + 1) for q in range(1, k + 1))
ok_nd = all(D[k][q] == N[k][q] + (N[k][q + 1] if q + 1 <= k else 0) for k in range(KMAX + 1) for q in range(k + 1))
ok_ext = True
for k in range(KMAX + 1):
    for m in range(k, k + 41):
        ok_ext &= (L.eval_Nbasis(N[k], m) == UR[k][m])
report('A5-N-table', ok_basic and ok_pos and ok_nd and ok_ext,
       'N(k,0)=[k=0]、N(k,1)=1、N(k,k)=2、N(k,k-1)=k^2-k-4（k<=300）%s；N(k,q)>0（1<=q<=k）%s；牛顿系数 d_q=N(k,q)+N(k,q+1) %s；'
       'Σ_q N(k,q)C(m+1,q) 在反演未用到的 m=k..k+40 上 = 递推表 %s (%.1fs)'
       % (ok_basic, ok_pos, ok_nd, ok_ext, time.time() - t))

# A6 U_k(-j) 三种算法一致（k<=60, j<=60），平凡零点
t = time.time()
G = {}
for j, g in L.gneg_iter(60, 60):
    G[j] = list(g)
ok3 = all(L.eval_Nbasis(N[k], -j) == L.eval_newton(D[k], -j) == G[j][k] for k in range(61) for j in range(1, 61))
ok_triv = all(L.eval_newton(D[k], -j) == 0 for k in range(1, KMAX + 1) for j in range(1, L.s_of(k) + 1))
ok_first = all(L.eval_newton(D[k], -(L.s_of(k) + 1)) != 0 for k in range(1, KMAX + 1))
report('A6-three-ways', ok3 and ok_triv and ok_first,
       'U_k(-j)：N 基 (0.1) = 牛顿基 C(m,q) = G_{-j} 递推（0<=k<=60, 1<=j<=60）%s；1<=j<=s_k 时为 0（k<=300）%s；'
       'U_k(-s_k-1)!=0（k<=300）%s (%.1fs)' % (ok3, ok_triv, ok_first, time.time() - t))

# ================================================================ B. 定理 1、推论 2
def Uval(k, m):
    return L.eval_newton(D[k], m)


# B1 定理 1 抽样
t = time.time()
cnt, bad = 0, 0
for k in range(1, 41):
    cache = {}

    def U(m, k=k, cache=cache):
        if m not in cache:
            cache[m] = Uval(k, m)
        return cache[m]
    for p in L.primes_upto(47):
        e0 = 1
        while p ** e0 <= k:
            e0 += 1
        for e in (e0, e0 + 1, e0 + 2):
            pe = p ** e
            if pe > 10 ** 6:
                continue
            for m in range(-120, 121):
                cnt += 1
                if (U(m + pe) - U(m)) % p:
                    bad += 1
rng = random.Random(20261008)
cnt2, bad2 = 0, 0
ps = L.primes_upto(400)
for _ in range(3000):
    k = rng.randint(1, KMAX)
    p = rng.choice(ps)
    e0 = 1
    while p ** e0 <= k:
        e0 += 1
    e = e0 + rng.randint(0, 2)
    m = rng.randint(-10 ** 5, 10 ** 5)
    cnt2 += 1
    if (Uval(k, m + p ** e) - Uval(k, m)) % p:
        bad2 += 1
report('B1-thm1', bad == 0 and bad2 == 0,
       '定理 1：p^e>k 时 U_k(m+p^e)≡U_k(m) (mod p)：系统抽样 1<=k<=40、p<=47、e=e_min..e_min+2（p^e<=10^6）、-120<=m<=120 共 %d 组，失败 %d；'
       '随机抽样 k<=300、p<=400、|m|<=10^5 共 %d 组，失败 %d (%.1fs)' % (cnt, bad, cnt2, bad2, time.time() - t))

# B2 p^e<=k 时：在一个完整周期上精确判定同余是否对一切 m 成立
t = time.time()
tot_pairs, fail_all, fail_author_range = 0, 0, 0
holds = []
for k in range(2, 41):
    cache = {}

    def U(m, k=k, cache=cache):
        if m not in cache:
            cache[m] = Uval(k, m)
        return cache[m]
    for p in L.primes_upto(k):
        emin = 1
        while p ** emin <= k:
            emin += 1
        T = p ** emin                      # U_k mod p 的周期（定理 1）
        pe = p
        while pe <= k:
            tot_pairs += 1
            f_all = any((U(m + pe) - U(m)) % p for m in range(0, T))
            f_auth = any((U(m + pe) - U(m)) % p for m in range(-10, 11))
            fail_all += f_all
            fail_author_range += f_auth
            if not f_all:
                holds.append((k, pe))
            pe *= p
ex1 = Uval(3, 3) - Uval(3, 0)
ex2 = Uval(4, 3) - Uval(4, 0)
# 例外的解释：p=2、2^e ∈ {k-1,k} 时，q>=2^e 的项只剩 N(k,k)=2、N(k,k-1)=k^2-k-4，都是偶数
expect = {(kk, pp) for kk in range(2, 41) for pp in (2, 4, 8, 16, 32) if pp <= kk and pp in (kk - 1, kk)}
expl = (set(holds) == expect)
report('B2-need', fail_all > 0 and tot_pairs == 461 and expl and ex1 % 3 and ex2 % 3,
       'p^e<=k（2<=k<=40）共 %d 组 (k,p^e)：在完整周期上同余失败 %d 组、对一切 m 成立 %d 组 %s'
       '（恰为 p=2、2^e∈{k-1,k} 的全部情形：%s，原因是 N(k,k)=2、N(k,k-1)=k^2-k-4 都是偶数）；只看 -10<=m<=10（作者的范围）失败 %d 组；'
       '例：U_3(3)-U_3(0)=%d、U_4(3)-U_4(0)=%d 都不被 3 整除 (%.1fs)'
       % (tot_pairs, fail_all, len(holds), holds, expl, fail_author_range, ex1, ex2, time.time() - t))

# B3 推论 2（a=0）：精确 G 递推，k<=100，j<=3000
t = time.time()
SPF_N = 5001
spf = list(range(SPF_N))
for i in range(2, SPF_N):
    if spf[i] == i:
        for mlt in range(i * i, SPF_N, i):
            if spf[mlt] == mlt:
                spf[mlt] = i


def factor(n):
    out = {}
    while n > 1:
        p = spf[n]
        out[p] = out.get(p, 0) + 1
        n //= p
    return out


cnt3, bad3 = 0, 0
cnt4, notone = 0, 0
for j, g in L.gneg_iter(100, 3000):
    fac = factor(j)
    for k in range(1, 101):
        for p, e in fac.items():
            if p ** e > k:
                cnt3 += 1
                if g[k] % p != 1 % p:
                    bad3 += 1
            elif j > L.s_of(k) and j <= 200:
                cnt4 += 1
                if g[k] % p != 1 % p:
                    notone += 1
# 一般 a
cnt5, bad5 = 0, 0
for _ in range(4000):
    k = rng.randint(1, 120)
    p = rng.choice(L.primes_upto(200))
    e0 = 1
    while p ** e0 <= k:
        e0 += 1
    pe = p ** (e0 + rng.randint(0, 1))
    a = rng.randint(-60, 300)
    tmul = rng.randint(1, 50)
    j = tmul * pe - a
    if j < 1:
        continue
    cnt5 += 1
    if (Uval(k, -j) - Uval(k, a)) % p:
        bad5 += 1
u33, u43 = Uval(3, -3), Uval(4, -3)
report('B3-cor2', bad3 == 0 and bad5 == 0 and notone > 0,
       '推论 2：p^{v_p(j)}>k 时 U_k(-j)≡1 (mod p)（1<=k<=100, 1<=j<=3000）%d 组，失败 %d；一般形式 p^e|j+a ⇒ U_k(-j)≡U_k(a) (mod p) 随机 %d 组，失败 %d；'
       '对照：p^{v_p(j)}<=k 时（s_k<j<=200）%d 组中 %d 组 U_k(-j)≢1，例 U_3(-3)=%d、U_4(-3)=%d (%.1fs)'
       % (cnt3, bad3, cnt5, bad5, cnt4, notone, u33, u43, time.time() - t))

# B4 「推论 2 ⇒ j | L_k」：j 不整除 L_k ⟺ 存在 p 使 p^{v_p(j)}>k（逐个核对 k<=60, j<=5000）
ok = True
for k in range(1, 61):
    Lk = L.lcm_upto(k)
    for j in range(1, 5001):
        fac = factor(j)
        big = any(p ** e > k for p, e in fac.items())
        ok &= (big == (Lk % j != 0))
report('B4-lcm', ok, '「j 有素数幂因子 >k」⟺「j ∤ lcm(1..k)」（1<=k<=60, 1<=j<=5000 逐个）')

# B5 p=2 的加强（复核者的附带观察）：2^e ∈ {k-1,k} 时仍有 U_k(m+2^e)≡U_k(m) (mod 2)，
# 所以 2^e | j 时 U_k(-j) 为奇数。核对 k=2^e、2^e+1（e=1..8），j=2^e·t（t=1..60）。
t = time.time()
cnt6, bad6 = 0, 0
for e in range(1, 9):
    for k in (2 ** e, 2 ** e + 1):
        if k < 2 or k > KMAX:
            continue
        for tt in range(1, 61):
            j = (2 ** e) * tt
            cnt6 += 1
            if Uval(k, -j) % 2 != 1:
                bad6 += 1
report('B5-p2-refine', bad6 == 0,
       '附带：p=2 时条件可放宽为 2^e>=k-1：k∈{2^e,2^e+1}（e=1..8）、j=2^e·t（t<=60）的 U_k(-j) 全为奇数：%d 组，失败 %d (%.1fs)'
       % (cnt6, bad6, time.time() - t))

# ================================================================ C. 定理 3
t = time.time()
ok_max, ok_lc, ok_r, ok_small, ok_inc, ok_jc = True, True, True, True, True, True
for k in range(4, KMAX + 1):
    th = L.theta_fracs(N[k], k)                         # th[q-1] = θ_q
    r = [Fr(N[k][q], N[k][q + 1]) for q in range(1, k)]  # r[q-1] = r_q
    mx = max(th)
    ok_max &= (mx == L.J_formula(k)) and th.index(mx) == k - 2 and th.count(mx) == 1
    ok_lc &= all(N[k][q] ** 2 > N[k][q - 1] * N[k][q + 1] for q in range(2, k))
    ok_r &= (r[-1] >= 1) and all(r[i] < r[i + 1] for i in range(len(r) - 1))
    ok_small &= all(th[i] < 2 for i in range(len(r)) if r[i] < 1)
    ok_inc &= all(th[i + 1] > th[i] for i in range(len(r) - 1) if r[i] >= 1)
    ok_jc &= (L.Jcut(N[k], k) == L.J_formula(k))
jc123 = [L.Jcut(N[k], k) for k in (1, 2, 3)]
report('C1-theta', ok_max and ok_lc and ok_r and ok_small and ok_inc and ok_jc,
       '定理 3（4<=k<=300，精确有理数）：max_q θ_q = J_k 且只在 q=k-1 取到 %s；N(k,·) 严格对数凹 %s；r_q 严格增且 r_{k-1}>=1 %s；'
       'r_q<1 时 θ_q<2 %s；r_q>=1 时 θ_{q+1}>θ_q %s；max_q ceil(θ_q)=J_k %s；k=1,2,3 的 max ceil θ = %s (%.1fs)'
       % (ok_max, ok_lc, ok_r, ok_small, ok_inc, ok_jc, jc123, time.time() - t))

t = time.time()
ok_eq, ok_strict = True, True
for k in range(4, KMAX + 1):
    J = L.J_formula(k)
    T = [N[k][q] * comb(J + q - 2, q) for q in range(1, k + 1)]
    ok_eq &= (T[-1] == T[-2]) and all(T[i] < T[i + 1] for i in range(k - 2))
    T = [N[k][q] * comb(J + 1 + q - 2, q) for q in range(1, k + 1)]
    ok_strict &= all(T[i] < T[i + 1] for i in range(k - 1))
report('C2-tight', ok_eq and ok_strict,
       'j=J_k 时 T_1<...<T_{k-1}=T_k %s；j=J_k+1 时 T_q 严格增 %s（4<=k<=300）(%.1fs)' % (ok_eq, ok_strict, time.time() - t))

t = time.time()
ok_s1, n_s1 = True, 0
for k in range(4, 61):
    J = L.J_formula(k)
    for j in range(J + 1, J + 2001):
        n_s1 += 1
        ok_s1 &= ((-1) ** k * Uval(k, -j) > 0)
ok_s2, n_s2 = True, 0
for k in range(61, KMAX + 1):
    J = L.J_formula(k)
    js = [J + 1, J + 2] + [rng.randint(J + 3, 50 * J) for _ in range(8)]
    for j in js:
        n_s2 += 1
        ok_s2 &= ((-1) ** k * Uval(k, -j) > 0)
# 真实的符号稳定点：最大实根
lastneg = {}
for k in (30, 40):
    J = L.J_formula(k)
    last = None
    for j in range(L.s_of(k) + 1, J + 1):
        if (-1) ** k * Uval(k, -j) <= 0:
            last = j
    lastneg[k] = last
report('C3-sign', ok_s1 and ok_s2 and lastneg == {30: 5291, 40: 10363},
       '(-1)^k U_k(-j)>0：4<=k<=60、J_k<j<=J_k+2000 共 %d 个 %s；61<=k<=300 每个 k 取 j=J_k+1,J_k+2 与 8 个随机 j<=50J_k 共 %d 个 %s；'
       '(-1)^kU_k(-j)<=0 的最后一个 j：k=30 为 %s（笔记：最大实根≈5291.6），k=40 为 %s（≈10363.9）(%.1fs)'
       % (n_s1, ok_s1, n_s2, ok_s2, lastneg[30], lastneg[40], time.time() - t))

# ================================================================ D. 命题 5 的点值
t = time.time()


def ufr(k, y):
    return L.eval_newton(D[k], y)


def sgn(v):
    return (v > 0) - (v < 0)


a1, a2 = ufr(30, Fr(-600003, 10000)), ufr(30, Fr(-600004, 10000))
u30_60 = Uval(30, -60)
u30_59, u30_61 = Uval(30, -59), Uval(30, -61)
b1, b2 = ufr(10, Fr(-902, 100)), ufr(10, Fr(-903, 100))
u10_9, u10_10 = Uval(10, -9), Uval(10, -10)
c1, c2 = ufr(37, Fr(-5531997, 1000)), ufr(37, Fr(-5531999, 1000))
d1, d2 = ufr(40, Fr(-69004, 1000)), ufr(40, Fr(-69005, 1000))
ok = (sgn(a1) * sgn(a2) < 0 and sgn(u30_60) == sgn(a1) and u30_60 == 131528853446152312280711
      and sgn(b1) * sgn(b2) < 0 and u10_9 == -153 and u10_10 == 17821
      and sgn(c1) * sgn(c2) < 0 and sgn(d1) * sgn(d2) < 0)
report('D1-prop5-points', ok,
       'u_30 在 m∈(-60.0004,-60.0003) 变号，U_30(-60)=%d≈%.2e，U_30(-59)=%.2e，U_30(-61)=%.2e；u_10 在 (-9.03,-9.02) 变号，'
       'U_10(-9)=%d，U_10(-10)=%d；u_37 在 y∈(5531.997,5531.999) 变号；u_40 在 y∈(69.004,69.005) 变号 (%.1fs)'
       % (u30_60, u30_60, u30_59, u30_61, u10_9, u10_10, time.time() - t))

# ================================================================ E. 素数与 Miller–Rabin 的确定性界
def sprp(n, a):
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = pow(a, d, n)
    if x in (1, n - 1):
        return True
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1:
            return True
    return False


psi12 = 318665857834031151167461
first13 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
passes12 = all(sprp(psi12, a) for a in first13[:12])
fails41 = not sprp(psi12, 41)
ok_pr = L.is_prime_td(P1) and L.is_prime_td(P2) and L.is_prime_td(P_A)
report('E1-primes', ok_pr, 'P1=%d、P2=%d、P_A=%d 用试除法确认为素数' % (P1, P2, P_A))
report('E2-MR-bound', passes12 and fails41,
       '合数 n=%d≈3.19e23 通过前 12 个素数底的强伪素数测试 %s、被底 41 判为合数 %s：所以「前 12 个素数为底对 <3.3e24 确定」不对'
       '（12 个底只对 <3.18e23 确定；3.3e24 是 13 个底的界）。对 P1、P2<2^31 无影响' % (psi12, passes12, fails41))

# ================================================================ F. §5 的反演式
t = time.time()


ok_h, ok_deg = True, True
for k in range(1, 61):
    h = [0] * k                                   # h_k(t) = Σ_q N(k,q) t^{q-1} (1-t)^{k-q}
    for q in range(1, k + 1):
        for i in range(k - q + 1):
            h[q - 1 + i] += N[k][q] * (-1) ** i * comb(k - q, i)
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    dgr = len(h) - 1
    s = L.s_of(k)
    ok_deg &= (dgr == k - s)
    for n in range(0, dgr + 4):
        rhs = (-1) ** k * sum((-1) ** i * comb(k + 1, i) * Uval(k, -(s + 1 + n - i)) for i in range(n + 1))
        lhs = h[dgr - n] if dgr - n >= 0 else 0
        ok_h &= (lhs == rhs)
report('F1-sec5', ok_h and ok_deg,
       '§5：deg h_k = k-s_k %s；h_{k,d-n} = (-1)^k Σ_i (-1)^i C(k+1,i) U_k(-(s_k+1+n-i))（1<=k<=60, 0<=n<=d+3）%s (%.1fs)'
       % (ok_deg, ok_h, time.time() - t))

# ================================================================ 反向检查
# R1：把 N(k,k-1) 改成 k^2-k-3，θ_{k-1} 不再等于 J_k，C1 的检查失败
k = 50
Nbad = list(N[k])
Nbad[k - 1] = k * k - k - 3
thb = L.theta_fracs(Nbad, k)
rv1 = max(thb) != L.J_formula(k)
# R2：把 G 递推的 jx^2 改成 (j+1)x^2，三种算法的一致性检查失败
Gb = {1: [1] + [0] * 20}
g = Gb[1]
for j in range(1, 30):
    new = [0] * 21
    for kk in range(21):
        v = g[kk] - (g[kk - 1] if kk >= 1 else 0) + (j * g[kk - 3] if kk >= 3 else 0) + ((j + 1) if kk == 2 else 0)
        new[kk] = v
    g = new
    Gb[j + 1] = g
rv2 = not all(Gb[j][kk] == L.eval_newton(D[kk], -j) for kk in range(21) for j in range(1, 31))
# R3：把 B1 的循环改成 e=e_min-1（p^e<=k），必须出现失败
bad_r3 = 0
for k in range(2, 41):
    for p in L.primes_upto(k):
        e0 = 1
        while p ** e0 <= k:
            e0 += 1
        pe = p ** (e0 - 1)
        bad_r3 += any((Uval(k, m + pe) - Uval(k, m)) % p for m in range(-20, 21))
rv3 = bad_r3 > 0
# R4：把 p=2 的例外推广到 2^e=k-2 就不再成立（说明例外的解释是精确的）
rv4 = any((Uval(k, m + 2 ** e) - Uval(k, m)) % 2 for (k, e) in ((6, 2), (10, 3), (18, 4), (34, 5)) for m in range(0, 64))
report('R1-reverse', rv1 and rv2 and rv3 and rv4,
       '反向：N(50,49) 改坏后 max θ≠J_50 %s；G 递推的 jx^2 改成 (j+1)x^2 后与多项式值不一致 %s；B1 的循环改用 e=e_min-1 后失败 %d 组 %s；'
       'p=2、2^e=k-2（k=6,10,18,34）时同余失败 %s' % (rv1, rv2, bad_r3, rv3, rv4))

n_pass = sum(RES)
print('total %.0fs' % (time.time() - T0))
print('SUMMARY s14-b8-r1 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
sys.exit(0 if n_pass == len(RES) else 1)
