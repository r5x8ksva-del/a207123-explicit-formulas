# -*- coding: utf-8 -*-
"""check_rv：第二轮对抗性复核带来的新结论与反例（主 Agent 独立重写的核对，不调用复核者脚本）。

  rv-Ntri-vs-def     N 三角递推（T1.4，已证明）与 DFS 定义 / 容斥的一致性（作为下面大 k 计算的底座）
  rv-c4-shiftpos-cex p_d(2d+1+m) 的单项式系数全正：d<=46 成立；47<=d<=57 均失败（d=47 为 m^91）
  rv-c4-newton-cex   以 2d+1 为基点的 Newton 系数全正：奇数 d<=67 的第 0 个为正，奇数 69<=d<=101 为负
  rv-num-cong        Num_q ≡ W_i·S_{q,i} (mod b_i)（复核者 r-c4ii 的引理 R1）
  rv-num-laguerre    S_{q,i} = n!·v^n·L_n^{(i+1)}(-1/v)（v=x^3, n=q-1-i）作为 v 的多项式恒等式
  rv-negzeros        U_k 的负整数零点恰为 -1..-floor((k+2)/3)（有理根定理 + Fujiwara 界，严格有限验证）
  rv-sum-identity    Σ_{j=1}^m j·h_{s-1}(j..m) = S(m+s,m) − [s=0]（更正 c2a 笔记中缺少的 s=0 情形）
"""
import os
import sys
import time
from fractions import Fraction
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_fast_table, N_brute, N_from_U, h_complete, stirling2_table
from polylib import P_poly, b_poly, pmul, padd, pshift, pscale, pdiv, trim, series_inv, series_mul

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
results = []


def report(cid, ok, desc):
    results.append(ok)
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


t0 = time.time()


# ---------------------------------------------------------------- N 三角（已证明的递推）
def N_triangle(K):
    """N[k][q]，0<=q<=k<=K。k=0,1,2 三行直接给出，k>=3 用 (C3) 三角递推。"""
    N = [[0] * (K + 2) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1], N[2][2] = 1, 2

    def g(k, q):
        if k < 0 or q < 0 or q > k:
            return 0
        return N[k][q]

    for k in range(3, K + 1):
        for q in range(1, k + 1):
            r = q - 1
            N[k][q] = g(k - 1, r) + g(k - 1, r + 1) + r * (g(k - 3, r - 1) + 2 * g(k - 3, r) + g(k - 3, r + 1))
    return N


NT = N_triangle(240)
T = U_fast_table(40, 40)
ok = all(NT[k][q] == N_from_U(T, k, q) for k in range(0, 41) for q in range(0, k + 1))
ok = ok and all(NT[k][q] == N_brute(k).get(q, 0) for k in range(0, 9) for q in range(0, k + 1))
report('rv-Ntri-vs-def', ok, 'N 三角递推 == 高度 DP 容斥（k<=40）== DFS 定义（k<=8）；下面大 k 的 N 用该递推（T1.4 已证明）')


def D(k, d):
    q = k - d
    return NT[k][q] if 0 <= q <= k else 0


# ---------------------------------------------------------------- p_d 的单项式系数（以 m=k-2d-1 为变量）
def pd_in_m(d):
    """用 m=1..(2d+1) 处的值（k=2d+2..4d+2，都在多项式区）插值 p_d(2d+1+m)，返回升幂 Fraction 系数。
    另外用后面 6 个点核对次数（Δ^{2d+1} 为 0）。"""
    npts = 2 * d + 1
    vals = [D(2 * d + 1 + m, d) for m in range(1, npts + 7)]
    # 前向差分（整数）
    diffs = []
    row = vals[:]
    for i in range(npts + 6):
        diffs.append(row[0])
        row = [row[j + 1] - row[j] for j in range(len(row) - 1)]
        if not row:
            break
    # 次数核对：所有阶 >= 2d+1 的差分在可用位置上为 0
    deg_ok = all(x == 0 for x in diffs[npts:])
    # p(m) = Σ_i diffs[i]·C(m-1, i)
    poly = [Fraction(0)]
    for i in range(npts):
        if diffs[i] == 0:
            continue
        # C(m-1,i) = Π_{r=0}^{i-1} (m-1-r) / i!
        c = [Fraction(1)]
        for r in range(i):
            c = pmul(c, [Fraction(-1 - r), Fraction(1)])
        c = pscale(c, Fraction(diffs[i], factorial(i)))
        poly = padd(poly, c)
    return trim(poly), deg_ok


neg47 = None
ok_small = True
first_bad = None
all_bad_47_57 = True
lead_ratio = None
for d in range(1, 58):
    poly, deg_ok = pd_in_m(d)
    nonpos = [i for i, c in enumerate(poly) if c <= 0]
    if not deg_ok or len(poly) != 2 * d + 1:
        ok_small = False
    if nonpos and first_bad is None:
        first_bad = d
    if d >= 47 and not nonpos:
        all_bad_47_57 = False
    if d == 47:
        neg47 = nonpos
        lead_ratio = poly[91] / poly[94]
ok = ok_small and first_bad == 47 and neg47 == [91] and lead_ratio == -122153 and all_bad_47_57
report('rv-c4-shiftpos-cex', ok,
       'p_d(2d+1+m) 的单项式系数：1<=d<=46 全正；47<=d<=57 每个都有非正系数，d=47 恰为 m^91，系数为首项的 %s 倍。'
       '所以 c4 的「以 m=k-2d-1 表示系数全正」一般不成立（N 由已证明的三角递推算到 k=240）' % lead_ratio)

# ---------------------------------------------------------------- 基点 2d+1 的第 0 个 Newton 系数
d = 69
p_at = D(2 * d + 1, d) - (-1) ** (d + 1) * factorial(d + 1)      # 定理 T4.1：e_d(2d+1) = (-1)^{d+1}(d+1)!
ok = (p_at < 0 and D(139, 69) < factorial(70)
      and all(D(2 * e + 1, e) > factorial(e + 1) for e in range(1, 68, 2))
      and all(D(2 * e + 1, e) < factorial(e + 1) for e in range(69, 102, 2)))
report('rv-c4-newton-cex', ok,
       '基点 2d+1 的第 0 个 Newton 系数 p_d(2d+1) = D(2d+1,d) − (−1)^{d+1}(d+1)!：奇数 d<=67 为正，奇数 69<=d<=101 全为负；'
       'd=69 时为 N(139,70)−70! = %.4e' % float(p_at))

# ---------------------------------------------------------------- Num_q 的同余与 Laguerre 恒等式
def W_poly(m):
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
    return W


def Num_poly(q, K=None):
    """Num_q = P_{q-1}·Σ_k N(k,q)x^k（N 取自三角递推），截断到 3q-2 次（T1.8：它是 3q-2 次多项式）。"""
    deg = 3 * q - 2
    ser = [NT[k][q] if k <= 200 else 0 for k in range(deg + 1)]
    prod = series_mul(ser, P_poly(q - 1), deg + 1)
    return trim([Fraction(c) for c in prod])


ok = True
for q in range(1, 21):
    Nq = Num_poly(q)
    for i in range(0, q):
        n = q - 1 - i
        S = [0] * (3 * n + 1)
        for t in range(n + 1):
            fall = 1
            for r in range(t):
                fall *= (n - r)
            S[3 * t] = comb(q, t) * fall
        rhs = pmul(W_poly(i), S)
        diff = padd(Nq, pscale(rhs, -1))
        if trim(pdiv(diff, b_poly(i))[1]) if diff else []:
            ok = False
report('rv-num-cong', ok, 'Num_q ≡ W_i·S_{q,i} (mod b_i)，S_{q,i}=Σ_t C(q,t)·[(q-1-i) 的 t 次下降阶乘]·x^{3t}，1<=q<=20，全部 0<=i<q（精确带余除法）')

ok = True
for q in range(1, 31):
    for i in range(0, q):
        n, a = q - 1 - i, i + 1
        # 左边：Σ_t C(q,t)(n)_t v^t；右边：n! v^n Σ_k (-1)^k C(n+a, n-k) (-1/v)^k / k! = Σ_k n! C(n+a,n-k) v^{n-k}/k!
        for t in range(n + 1):
            fall = 1
            for r in range(t):
                fall *= (n - r)
            lhs = comb(q, t) * fall
            k = n - t
            rhs = Fraction(factorial(n) * comb(n + a, n - k), factorial(k))
            if lhs != rhs:
                ok = False
report('rv-num-laguerre', ok, 'S_{q,i}(x) = n!·v^n·L_n^{(i+1)}(−1/v)（v=x^3, n=q−1−i，广义 Laguerre），逐系数核对 1<=q<=30')


# ---------------------------------------------------------------- U_k 的负整数零点（严格有限验证）
def U_int_poly(k):
    """k!·u_k(x) ∈ Z[x]，由 u_k(x) = Σ_q N(k,q)·C(x+1,q)（T1.4）展开。"""
    P = [0]
    kf = factorial(k)
    for q in range(0, k + 1):
        v = NT[k][q]
        if v == 0:
            continue
        p = [1]
        for r in range(q):
            p = pmul(p, [1 - r, 1])                # (x+1-r)
        P = padd(P, [c * v * (kf // factorial(q)) for c in p])
    return [int(c) for c in trim(P)]


def primes_upto(n):
    s = [True] * (n + 1)
    s[0:2] = [False, False]
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = [False] * len(s[i * i::i])
    return [i for i in range(n + 1) if s[i]]


def divisors_of_factorial_upto(k, B):
    ps = primes_upto(k)

    def vp(p):
        v, q = 0, p
        while q <= k:
            v += k // q
            q *= p
        return v
    lim = [vp(p) for p in ps]
    out = []

    def rec(i, cur):
        if i == len(ps):
            out.append(cur)
            return
        x = cur
        for _ in range(lim[i] + 1):
            if x > B:
                break
            rec(i + 1, x)
            x *= ps[i]
    rec(0, 1)
    return out


def fujiwara_bound(P):
    """所有复根 |z| <= 2·max(|a_{n-i}/a_n|^{1/i}, |a_0/(2a_n)|^{1/n})，返回向上取整的整数界。"""
    n = len(P) - 1
    an = abs(P[n])
    best = Fraction(0)
    for i in range(1, n + 1):
        a = abs(P[n - i])
        if a == 0:
            continue
        r = Fraction(a, an) if i < n else Fraction(a, 2 * an)
        # 求最小整数 c 使 c^i >= r
        c = 1
        while Fraction(c) ** i < r:
            c *= 2
        lo, hi = c // 2, c
        while lo + 1 < hi:
            mid = (lo + hi) // 2
            if Fraction(mid) ** i >= r:
                hi = mid
            else:
                lo = mid
        best = max(best, hi)
    return int(2 * best) + 1


KNZ = 40
ok = True
maxB = 0
for k in range(1, KNZ + 1):
    P = U_int_poly(k)
    assert P[0] == factorial(k)                     # 常数项 = k!·U_k(0) = k!
    B = fujiwara_bound(P)
    maxB = max(maxB, B)
    zeros = []
    for j in divisors_of_factorial_upto(k, B):
        x = -j
        val = 0
        for c in reversed(P):
            val = val * x + c
        if val == 0:
            zeros.append(j)
    if sorted(zeros) != list(range(1, (k + 2) // 3 + 1)):
        ok = False
report('rv-negzeros', ok,
       '1<=k<=%d：U_k 的负整数零点恰为 -1..-floor((k+2)/3)（有理根定理：整数根整除 k!；Fujiwara 界内逐个精确求值，最大界 %d）'
       % (KNZ, maxB))

# ---------------------------------------------------------------- c2a 失败方向中的恒等式（补 s=0）
S2 = stirling2_table(40)
h_ = lambda s_, lo, hi: h_complete(s_, lo, hi) if s_ >= 0 else 0   # core.h_complete 不处理负 s
ok = all(sum(j * h_(s - 1, j, m) for j in range(1, m + 1)) == S2[m + s][m] - (1 if s == 0 else 0)
         for m in range(1, 16) for s in range(0, 20))
report('rv-sum-identity', ok, 'Σ_{j=1}^m j·h_{s−1}(j..m) = S(m+s,m) − [s=0]（1<=m<=15, 0<=s<=19；c2a 原文漏了 s=0）')

npass = sum(results)
nfail = len(results) - npass
print('SUMMARY rv pass=%d fail=%d (%.1fs)' % (npass, nfail, time.time() - t0))
sys.exit(0 if nfail == 0 else 1)
