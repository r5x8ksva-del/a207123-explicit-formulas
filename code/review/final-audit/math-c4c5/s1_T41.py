# -*- coding: utf-8 -*-
"""T4.1 / T4.2(3) 的数字与门槛核对（final-audit math-c4c5）。"""
import time
from fractions import Fraction
from math import comb, factorial

from alib import (say, check, U_col, N_tri, interp_newton, peval, padd, pmul, pscale, ptrim,
                  pshiftarg, fwd_diffs, falling_poly, dfact, write_log)
from core import U_fast_table, N_from_U, N_brute

t0 = time.time()
KMAX = 250
NT = N_tri(KMAX)

# ---- 0. 底座：自写三角 == core 的 DP 容斥（k<=40）== 自写 DP 容斥（k<=22）== DFS 定义（k<=8）
T = U_fast_table(40, 40)
ok = all(NT[k][q] == N_from_U(T, k, q) for k in range(41) for q in range(k + 1))
cols = [U_col(m, 22) for m in range(23)]


def N_own(k, q):
    s = 0
    for i in range(q + 1):
        u = (1 if k == 0 else 0) if i == 0 else cols[i - 1][k]
        s += (-1) ** (q - i) * comb(q, i) * u
    return s


ok2 = all(NT[k][q] == N_own(k, q) for k in range(23) for q in range(k + 1))
ok3 = all(NT[k][q] == N_brute(k).get(q, 0) for k in range(9) for q in range(k + 1))
check('base.N', ok and ok2 and ok3, '自写 N 三角 == core DP 容斥 (k<=40) == 自写字面 DP 容斥 (k<=22) == core.N_brute (k<=8)')


def D(k, d):
    q = k - d
    if q < 0 or q > k:
        return 0
    return NT[k][q]


# ---- 1. 报告 T4.1 的 p_0..p_5（逐字抄录）
F = Fraction
P_REPORT = {
    0: ([2], 1),
    1: ([-4, -1, 1], 1),
    2: ([164, -98, 43, -10, 1], 4),
    3: ([11088, -17392, 8560, -2225, 331, -27, 1], 24),
    4: ([5014464, -5702176, 2926356, -845644, 151217, -17280, 1242, -52, 1], 192),
    5: ([2686170240, -3158022432, 1637903536, -498528820, 98708360, -13308173, 1241073, -79370, 3350, -85, 1], 1920),
}
pr = {d: [F(c, den) for c in cs] for d, (cs, den) in P_REPORT.items()}
bad = []
for d in range(6):
    for k in range(2 * d + 2, 41):          # core 真值
        if peval(pr[d], k) != N_from_U(T, k, k - d):
            bad.append(('core', d, k))
    for k in range(2 * d + 2, KMAX + 1):     # 自写三角
        if peval(pr[d], k) != D(k, d):
            bad.append(('tri', d, k))
    exc = [k for k in range(d + 1, 2 * d + 2) if peval(pr[d], k) == D(k, d)]
    if exc:
        bad.append(('exception-equal', d, exc))
    if peval(pr[d], 2 * d + 1) == D(2 * d + 1, d):
        bad.append(('2d+1', d))
check('T4.1.p0-5', not bad, 'p_0..p_5（报告原文系数）在 2d+2<=k<=40 等于 core 的 N(k,k-d)，在 2d+2<=k<=%d 等于三角递推值；'
      'd+1<=k<=2d+1 每点都不等（门槛 2d+2 精确）; bad=%s' % (KMAX, bad[:5]))


# ---- 2. d<=60：由数据插值 p_d，核对次数、首项、次首项、两个缺陷
def pd_poly(d):
    xs = list(range(2 * d + 2, 4 * d + 3))          # 2d+1 个点
    p = interp_newton(xs, [D(k, d) for k in xs])
    return p


bad_lead, bad_def, bad_extra = [], [], []
PD = {}
for d in range(0, 61):
    p = pd_poly(d)
    PD[d] = p
    # 多余点核对（k 到 4d+12，<= KMAX）
    for k in range(4 * d + 3, min(4 * d + 13, KMAX + 1)):
        if peval(p, k) != D(k, d):
            bad_extra.append((d, k))
    lead = F(2, 2 ** d * factorial(d))
    if len(p) != 2 * d + 1 or p[-1] != lead:
        bad_lead.append(d)
    if d >= 1 and p[-2] != -(4 * d * d - 3 * d) * lead:
        bad_lead.append(('2nd', d))
    e1 = D(2 * d + 1, d) - peval(p, 2 * d + 1)
    e0 = D(2 * d, d) - peval(p, 2 * d)
    if e1 != (-1) ** (d + 1) * factorial(d + 1) or e0 != F((-1) ** (d + 1) * factorial(d + 2), 2):
        bad_def.append(d)
check('T4.1.degree-lead-second', not bad_lead and not bad_extra,
      'd<=60：插值多项式在多余点上与数据一致，deg=2d，首项 2/(2^d d!)，次首项 = -(4d^2-3d)*首项; bad=%s %s' % (bad_lead[:5], bad_extra[:5]))
check('T4.1.defects', not bad_def, 'd<=60：e_d(2d+1)=(-1)^{d+1}(d+1)!，e_d(2d)=(-1)^{d+1}(d+2)!/2; bad=%s' % bad_def[:5])

# r_d 递推（符号）
okr = all((2 * d - 1) * (-(4 * d * d - 3 * d)) == 2 * d * (-(4 * (d - 1) ** 2 - 3 * (d - 1))) - 12 * d * d + 11 * d
          for d in range(1, 200)) and -(4 - 3) == -1
check('T4.1.r-rec', okr, 'r_d=-(4d^2-3d) 满足 (2d-1)r_d=2d r_{d-1}-12d^2+11d（d<200），r_1=-1')

# ---- 3. p_2 的 m 形式
p2m = pshiftarg(pr[2], 5)
check('T4.1.p2-m', p2m == [F(124, 4), F(82, 4), F(43, 4), F(10, 4), F(1, 4)],
      'p_2(m+5) = (m^4+10m^3+43m^2+82m+124)/4；实算 %s' % [str(c) for c in p2m])

# ---- 4. p_d(2d+1+m) 的单项式系数符号（d<=60）
neg_info = {}
first_bad = None
for d in range(1, 61):
    pm = pshiftarg(PD[d], 2 * d + 1)
    nonpos = [i for i, c in enumerate(pm) if c <= 0]
    zeros = [i for i, c in enumerate(pm) if c == 0]
    if nonpos and first_bad is None:
        first_bad = d
    if d >= 47:
        neg_info[d] = (nonpos, zeros, len(pm) - 1)
    if d == 47:
        ratio47 = pm[91] / pm[94]
say('INFO 非正系数位置（m 的次数）d=47..60:')
for d in sorted(neg_info):
    nonpos, zeros, deg = neg_info[d]
    say('   d=%d (deg %d): nonpos=%s zeros=%s low(<=d)=%s' % (d, deg, nonpos, zeros, [i for i in nonpos if i <= d]))
ok = (first_bad == 47 and neg_info[47][0] == [91] and ratio47 == -122153
      and all(neg_info[d][0] for d in range(47, 61)))
check('T4.1.shiftpos', ok, 'd<=46 全正；d=47 首个失败且只有 m^91（比值 %s）；47<=d<=60 每个 d 都有非正系数' % ratio47)
low_first = min(d for d in neg_info if any(i <= d for i in neg_info[d][0]))
only_high = all(all(i > d for i in neg_info[d][0]) for d in range(47, 57))
low_57_60 = all(any(i <= d for i in neg_info[d][0]) for d in range(57, 61))
check('T4.1.low-vs-high', only_high and low_57_60 and low_first == 57 and [i for i in neg_info[57][0] if i <= 57] == [8, 10],
      'd<=56 的非正系数次数都 > d（高次端）；d=57..60 都有次数 <= d 的非正系数；d=57 的低次为 m^8、m^10')

# ---- 5. Newton 系数（基点 2d+2）
bad = []
for d in range(0, 41):
    vals = [D(2 * d + 2 + n, d) for n in range(2 * d + 1)]
    T_ = fwd_diffs(vals)
    if not all(t > 0 for t in T_) or T_[2 * d] != 2 * dfact(2 * d - 1):
        bad.append(d)
    # 次数核对：再多取 3 点，2d+1 阶差分为 0
    vals2 = [D(2 * d + 2 + n, d) for n in range(2 * d + 4)]
    if any(x != 0 for x in fwd_diffs(vals2)[2 * d + 1:]):
        bad.append(('deg', d))
T2 = fwd_diffs([D(6 + n, 2) for n in range(5)])
check('T4.2.3-newton', not bad and T2 == [65, 74, 64, 30, 6],
      'd<=40：Δ^i p_d(2d+2) 全为正整数、末项 2(2d-1)!!；d=2 为 %s; bad=%s' % (T2, bad[:5]))

# ---- 6. 证明中的恒等式 Δp_d(2d+2+n) = p_{d-1}(2d+2+n) + (d+2+n)[p_{d-1}(2d+n)+2p_{d-2}(2d+n)+p_{d-3}(2d+n)]
def pv(d, k):
    if d < 0:
        return 0
    return peval(PD[d], k)


bad = []
for d in range(1, 30):
    for n in range(-3, 15):
        lhs = pv(d, 2 * d + 3 + n) - pv(d, 2 * d + 2 + n)
        rhs = pv(d - 1, 2 * d + 2 + n) + (d + 2 + n) * (pv(d - 1, 2 * d + n) + 2 * pv(d - 2, 2 * d + n) + pv(d - 3, 2 * d + n))
        if lhs != rhs:
            bad.append((d, n))
# 平移量：p_{d'} 的基点 2d'+2
shifts = [(2 * d + 2) - (2 * (d - 1) + 2), (2 * d) - (2 * (d - 1) + 2), (2 * d) - (2 * (d - 2) + 2), (2 * d) - (2 * (d - 3) + 2)]
check('T4.2.3-identity', not bad and shifts == [2, 0, 2, 4],
      '恒等式（多项式，d<30，n in [-3,15)）成立；四项相对各自基点 2d\'+2 的右移量 = %s; bad=%s' % (shifts, bad[:5]))


# 乘 (α+n) 的 Newton 系数规则：f_l -> f_l(α+l) + l f_{l-1}
def newton_coeffs(poly_in_n, deg):
    return fwd_diffs([peval(poly_in_n, n) for n in range(deg + 1)])


okm = True
import random
random.seed(1)
for _ in range(50):
    deg = random.randint(0, 6)
    f = [F(random.randint(-5, 5)) for _ in range(deg + 1)]
    al = random.randint(1, 9)
    g = pmul([al, 1], f)
    fl = newton_coeffs(f, deg + 1)
    gl = newton_coeffs(g, deg + 1)
    pred = [fl[l] * (al + l) + (l * fl[l - 1] if l >= 1 else 0) for l in range(deg + 2)]
    if gl != pred:
        okm = False
check('T4.2.3-mult-rule', okm, '乘 (α+n) 时 Newton 系数 f_l -> f_l(α+l)+l f_{l-1}（50 个随机多项式）')

# ---- 7. 基点 2d+1 的第 0 个 Newton 系数 p_d(2d+1) = D(2d+1,d) - (-1)^{d+1}(d+1)!
pos_odd = [d for d in range(1, 102, 2) if D(2 * d + 1, d) - factorial(d + 1) > 0]
neg_odd = [d for d in range(1, 102, 2) if D(2 * d + 1, d) - factorial(d + 1) < 0]
even_ok = all(D(2 * d + 1, d) + factorial(d + 1) > 0 for d in range(0, 102, 2))
v69 = D(139, 69) - factorial(70)
# 对 d<=60 直接与插值多项式比
cons = all(peval(PD[d], 2 * d + 1) == D(2 * d + 1, d) - (-1) ** (d + 1) * factorial(d + 1) for d in range(0, 61))
check('T4.2.3-base2d1', pos_odd == list(range(1, 68, 2)) and neg_odd == list(range(69, 102, 2)) and even_ok and cons,
      '奇数 d<=67 为正、奇数 69<=d<=101 为负；偶数 d 时 D(2d+1,d)+(d+1)!>0；d<=60 与插值多项式一致；'
      'd=69: N(139,70)-70! = %.4e (%d 位)' % (float(v69), len(str(abs(v69)))))
say('INFO N(139,70) =', NT[139][70])
say('INFO 70!       =', factorial(70))
say('INFO diff      =', v69)
# 比值 D(2d+1,d)/(d+1)! 的峰
ratios = {d: D(2 * d + 1, d) // factorial(d + 1) for d in range(1, 102, 2)}
say('INFO floor(D(2d+1,d)/(d+1)!) 奇数 d:', [(d, ratios[d]) for d in range(1, 72, 2)])

# ---- 8. 锚点
check('T4.1.anchors', [D(2 * d + 2, d) for d in range(6)] == [2, 8, 65, 574, 6012, 70674],
      'D(2d+2,d) d=0..5 = %s' % [D(2 * d + 2, d) for d in range(6)])

say('elapsed %.1fs' % (time.time() - t0))
write_log('final_audit_math-c4c5_s1.log')
