# -*- coding: utf-8 -*-
"""s5：固定 k 一侧。T9（N 三角递推）、T10（N(k,k-d) 的多项式与精确门槛）、T11/T12（m 的次首项系数）、T23。

数据来源：
  * U 表：引理 1 递推（复核者已独立重证，并在 s1 中与自写 DP 对照到 k<=90, m<=40）。k<=130。
  * N(k,q)：由 U 表做容斥（二项式基的定义），不经三角递推；另用自写 DFS 按定义枚举锚定到 k<=8。
  * m 的系数：对 U_k(0..k) 做 Newton 插值（与 N 无关）。
"""
import sys, os, time
from fractions import Fraction as Fr
from math import factorial, comb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rlib import U_rec_table, U_dp, ok3, interp_newton, peval, pmul, padd, pscale, trim

t0 = time.time()
K = 130
T = U_rec_table(K, K + 2)


def Uval(k, m):
    if m == -1:
        return 1 if k == 0 else 0
    return T[k][m]


N = {}
for k in range(0, K + 1):
    for q in range(0, k + 1):
        N[(k, q)] = sum((-1) ** (q - i) * comb(q, i) * Uval(k, i - 1) for i in range(0, q + 1))


def Nv(k, q):
    if k < 0 or q < 0 or q > k:
        return 0
    return N[(k, q)]


# 锚定：DFS 按定义（值域恰为 {1..q} 的合法词）
def N_dfs(k):
    res = {}
    seq = []

    def rec():
        if len(seq) == k:
            s = set(seq)
            q = len(s)
            if s == set(range(1, q + 1)):
                res[q] = res.get(q, 0) + 1
            return
        for v in range(1, k + 1):
            if len(seq) >= 2 and not ok3(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec()
            seq.pop()
    rec()
    return res


ok_dfs = all(N_dfs(k).get(q, 0) == Nv(k, q) for k in range(1, 9) for q in range(1, k + 1))
print('N via inclusion-exclusion == DFS by definition (k<=8):', ok_dfs)
# U 表与自写 DP 抽查
ok_dp = all(U_dp(m, 130) == [T[k][m] for k in range(131)] for m in (0, 1, 2, 5, 9))
print('Lemma-1 table == own DP for m in {0,1,2,5,9}, k<=130:', ok_dp)

# T9：三角递推 3<=k<=130
ok_tri = all(Nv(k, r + 1) == Nv(k - 1, r) + Nv(k - 1, r + 1) + r * (Nv(k - 3, r - 1) + 2 * Nv(k - 3, r) + Nv(k - 3, r + 1))
             for k in range(3, K + 1) for r in range(0, k))
print('T9 triangle recurrence, 3<=k<=130:', ok_tri)

# T10：d<=3 显式
P = {0: [Fr(2)], 1: [Fr(-4), Fr(-1), Fr(1)], 2: [Fr(c, 4) for c in (164, -98, 43, -10, 1)],
     3: [Fr(c, 24) for c in (11088, -17392, 8560, -2225, 331, -27, 1)]}
ok_p = True
for d in range(0, 4):
    for k in range(2 * d + 2, K + 1):
        if peval(P[d], k) != Nv(k, k - d):
            ok_p = False
    if peval(P[d], 2 * d + 1) - Nv(2 * d + 1, d + 1) != (-1) ** d * factorial(d + 1):
        ok_p = False
print('T10 explicit p_0..p_3 on [2d+2,130] and defect (-1)^d (d+1)! at 2d+1:', ok_p)

# T10：一般 d<=12：插值 [2d+2,4d+2]，在 [2d+2,130] 上逐点相等；首项 2/(2^d d!)；缺口；以及 2d 处是否偶然相等
gen = []
ok_gen = True
for d in range(1, 13):
    xs = list(range(2 * d + 2, 4 * d + 3))
    p = interp_newton(xs, [Nv(x, x - d) for x in xs])
    good = all(peval(p, k) == Nv(k, k - d) for k in range(2 * d + 2, K + 1))
    lc = (len(p) - 1 == 2 * d) and p[-1] == Fr(2, 2 ** d * factorial(d))
    dfc = peval(p, 2 * d + 1) - Nv(2 * d + 1, d + 1)
    ok_gen = ok_gen and good and lc and dfc == (-1) ** d * factorial(d + 1)
    # 在更小的 k 处是否也相等（门槛“精确”只要求 2d+1 处失效）
    also = [k for k in range(d, 2 * d + 1) if peval(p, k) == Nv(k, k - d)]
    gen.append((d, good, lc, dfc, also))
print('T10 general d<=12 (k<=130): all good/lc/defect ok:', ok_gen)
print('   (d, extra small k where p_d(k)==N(k,k-d) coincidentally):', [(d, a) for d, _, _, _, a in gen])

# T11/T12：U_k 关于 m 的系数（Newton 插值，与 N 无关）
COEF = {}
for k in range(0, K + 1):
    xs = list(range(0, k + 1))
    COEF[k] = interp_newton(xs, [T[k][m] for m in xs]) if k > 0 else [Fr(1)]
    COEF[k] = COEF[k] + [Fr(0)] * (k + 1 - len(COEF[k]))
ok_top = all(COEF[k][k] == Fr(2, factorial(k)) for k in range(2, K + 1))
B = {1: [Fr(-1), Fr(-2), Fr(1)], 2: [Fr(c, 12) for c in (422, -313, 162, -36, 3)],
     3: [Fr(c, 24) for c in (13380, -19331, 9570, -2533, 379, -30, 1)]}
ok_B = True
for d in (1, 2, 3):
    for k in range(2 * d + 2, K + 1):
        if COEF[k][k - d] * factorial(k - d) != peval(B[d], k):
            ok_B = False
    if COEF[2 * d + 1][d + 1] * factorial(d + 1) - peval(B[d], 2 * d + 1) != (-1) ** (d + 1) * factorial(d + 1):
        ok_B = False
print('T11 [m^k]U_k=2/k! (2<=k<=130):', ok_top, '; T11/T12 explicit B_1..B_3 on [2d+2,130] + defects:', ok_B)
print('   small-k actual (k-1)![m^{k-1}]U_k for k=1..3:', [COEF[k][k - 1] * factorial(k - 1) for k in (1, 2, 3)],
      ' formula k^2-2k-1:', [k * k - 2 * k - 1 for k in (1, 2, 3)])


# ẽ_j(n) 直接按定义算（不用笔记里的显式式），检查恒等式 B_d(k) = sum_e (-1)^{d-e} N(k,k-e) ẽ_{d-e}(k-e)
def esym_set(j, n):
    row = [1] + [0] * j
    for v in range(-1, n - 1):
        for t in range(j, 0, -1):
            row[t] += v * row[t - 1]
    return row[j]


def etil(j, n):
    ff = 1
    for i in range(j):
        ff *= (n - i)
    return Fr(esym_set(j, n), ff)


ok_id = True
for d in range(1, 7):
    for k in range(d, K + 1):
        lhs = COEF[k][k - d] * factorial(k - d)
        rhs = sum((-1) ** (d - e) * Nv(k, k - e) * etil(d - e, k - e) for e in range(0, d + 1))
        if lhs != rhs:
            ok_id = False
print('T12 identity B_d(k)=sum_e(-1)^{d-e}N(k,k-e)etilde_{d-e}(k-e), etilde by definition, d<=6, d<=k<=130:', ok_id)
ET = {1: [Fr(-3, 2), Fr(1, 2)], 2: pscale(pmul([Fr(-2), Fr(1)], [Fr(-13), Fr(3)]), Fr(1, 24)),
      3: pscale(pmul([Fr(-3), Fr(1)], [Fr(8), Fr(-7), Fr(1)]), Fr(1, 48))}
ok_et = all(etil(j, n) == peval(ET[j], n) for j in (1, 2, 3) for n in range(j, 200))
print('   explicit etilde_1..3 == definition for n<=199:', ok_et)

okg = True
for d in range(1, 13):
    xs = list(range(2 * d + 2, 4 * d + 3))
    Bv = {k: COEF[k][k - d] * factorial(k - d) for k in range(d, K + 1)}
    p = interp_newton(xs, [Bv[x] for x in xs])
    good = all(peval(p, k) == Bv[k] for k in range(2 * d + 2, K + 1))
    lc = len(p) - 1 == 2 * d and p[-1] == Fr(1, 2 ** (d - 1) * factorial(d))
    dfc = Bv[2 * d + 1] - peval(p, 2 * d + 1) == (-1) ** (d + 1) * factorial(d + 1)
    okg = okg and good and lc and dfc
print('T12 general d<=12: B_d degree-2d polynomial on [2d+2,130], lc 1/(2^(d-1)d!), defect (-1)^(d+1)(d+1)!:', okg)

# T23：U_k(m) / ((2/k!)(m+mu_k)^k) - 1 = O(m^-2)
print('T23 check  m^2 * (U_k(m)/((2/k!)(m+mu)^k) - 1)  for k=8, 12:')
for k in (8, 12):
    mu = Fr(k * k - 2 * k - 1, 2)
    out = []
    for m in (10 ** 3, 10 ** 4, 10 ** 5):
        val = peval(COEF[k], m)
        approx = Fr(2, factorial(k)) * (m + mu) ** k
        out.append('m=%d: %.6f' % (m, float((val / approx - 1) * m * m)))
    print('   k=%d: ' % k + ', '.join(out))
print('elapsed %.1fs' % (time.time() - t0))
