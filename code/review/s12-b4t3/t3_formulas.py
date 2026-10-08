# -*- coding: utf-8 -*-
"""s12-b4t3：notes/12 定理 3 的显式式子、递推论证、约化（部分分式）与措辞（m=3 的混合原子表示）。
不导入项目的任何模块；真值 U 按定义计数（t3_common.U_dp，另用全枚举核对 DP）。
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_common import (setup_utf8, Reporter, U_dp, U_brute, P_poly, W_poly, Wt_dict, series_div,
                       c_seq, CBar, KField, in_span2, pmul, b_poly, det3cols)

setup_utf8()
R = Reporter('s12-b4t3-formulas')
t0 = time.time()
KMAX = 300

# ---- F0：DP 与全枚举
ok = all(U_dp(m, 9)[k] == U_brute(m, k) for m in range(0, 4) for k in range(0, 10))
R.check('F0-dp-brute', ok, 'U_k(m) 的 DP 与全枚举一致（0<=m<=3，0<=k<=9）')

U = {m: U_dp(m, KMAX) for m in range(0, 9)}

# ---- F1：G_m = W_m/P_m
ok = True
for m in range(0, 7):
    s = series_div(W_poly(m), P_poly(m), 80)
    ok &= all(s[k] == U[m][k] for k in range(81))
R.check('F1-gf', ok, 'sum_k U_k(m)x^k = W_m/P_m（m<=6，k<=80）')

# ---- c 与 c~
cs = {i: c_seq(i, KMAX + 40) for i in range(0, 9)}
cb = {i: CBar(i, KMAX + 40, 80) for i in range(1, 9)}


def c(i, n):
    return cs[i][n] if n >= 0 else 0


R.check('F2-cbar-vals', cb[1](-1) == 0 and cb[1](-2) == 0 and cb[1](-3) == 1 and cb[1](-4) == 0
        and cb[2](-1) == 0 and cb[2](-2) == 0 and cb[2](-3) == Fr(1, 2),
        'c~_1(-1..-4) = 0,0,1,0；c~_2(-1)=c~_2(-2)=0，c~_2(-3)=1/2')

# ---- F3：m=1 式子
bad1 = [k for k in range(KMAX + 1) if c(1, k + 2) + c(1, k + 1) - 1 != U[1][k]]
R.check('F3-m1', bad1 == [], 'U_k(1) = c_1(k+2)+c_1(k+1)-1 对 0<=k<=%d 全部成立（不符的 k：%s）' % (KMAX, bad1))


# ---- F4：m=2 式子（c 与 c~）
def rhs2(k, f1, f2):
    return Fr(1, 2) - Fr(1, 4) * f1(k + 10) + Fr(1, 4) * f1(k - 4) + Fr(5, 2) * f2(k + 3) + 6 * f2(k - 2)


bad2 = [k for k in range(KMAX + 1) if rhs2(k, lambda n: c(1, n), lambda n: c(2, n)) != U[2][k]]
diff1 = U[2][1] - rhs2(1, lambda n: c(1, n), lambda n: c(2, n))
R.check('F4-m2-c', bad2 == [1] and diff1 == Fr(1, 4),
        'U_k(2) 两原子式（c，负下标取 0）在 0<=k<=%d 中只在 k=%s 不成立；k=1 处 U - 右边 = %s' % (KMAX, bad2, diff1))
bad2b = [k for k in range(KMAX + 1) if rhs2(k, cb[1], cb[2]) != U[2][k]]
R.check('F4-m2-cbar', bad2b == [], 'c 换成双向延拓 c~ 后 0<=k<=%d 全部成立（不符：%s）' % (KMAX, bad2b))
# 哪些 k 用到负下标、c 与 c~ 在那里是否不同
negs = [(k, n, cb[1](n)) for k in range(0, 8) for n in (k - 4,) if n < 0] + \
       [(k, n, cb[2](n)) for k in range(0, 8) for n in (k - 2,) if n < 0]
diffpos = [(k, n) for (k, n, v) in negs if v != 0]
R.check('F4-neg-index', diffpos == [(1, -3)],
        'k>=0 时用到的负下标及 c~ 的值：%s；c 与 c~ 不同的只有 (k, 下标)=%s' % (negs, diffpos))

# ---- F5：递推论证
okL = True
tight = []
for m in range(0, 7):
    P = P_poly(m)
    d = len(P) - 1          # = 3m+1
    rec = [sum(P[j] * U[m][k - j] for j in range(d + 1)) for k in range(d, KMAX + 1)]
    okL &= all(v == 0 for v in rec)                 # k >= 3m+1
    if m >= 1:
        # k = 3m 时（下标仍都 >=0 的部分和）不为零：说明窗口 0..3m 不能再缩
        v3m = sum(P[j] * U[m][3 * m - j] for j in range(0, 3 * m + 1))
        tight.append(v3m)
R.check('F5-rec-lhs', okL and all(v != 0 for v in tight),
        'U_k(m) 对 k>=3m+1 满足以 P_m 为特征的递推（m<=6，k<=%d）；k=3m 处 [x^{3m}]W_m != 0：%s' % (KMAX, tight))


def rec_ok_all(f, m, lo, hi):
    P = P_poly(m)
    return all(sum(P[j] * f(k - j) for j in range(len(P))) == 0 for k in range(lo, hi + 1))


okR1 = rec_ok_all(lambda k: cb[1](k + 2) + cb[1](k + 1) - 1, 1, -40, KMAX)
okR2 = rec_ok_all(lambda k: rhs2(k, cb[1], cb[2]), 2, -40, KMAX)
R.check('F5-rec-rhs', okR1 and okR2,
        '用 c~ 的右边对 -40<=k<=%d 的一切 k 满足同一递推（m=1 阶 4、m=2 阶 7）：%s, %s' % (KMAX, okR1, okR2))
# 负对照：改动一个系数/平移后，0..3m 窗口里就能看出不符
pert = {
    '6->7': lambda k: Fr(1, 2) - Fr(1, 4) * cb[1](k + 10) + Fr(1, 4) * cb[1](k - 4) + Fr(5, 2) * cb[2](k + 3) + 7 * cb[2](k - 2),
    'c2(k-2)->c2(k-1)': lambda k: Fr(1, 2) - Fr(1, 4) * cb[1](k + 10) + Fr(1, 4) * cb[1](k - 4) + Fr(5, 2) * cb[2](k + 3) + 6 * cb[2](k - 1),
    '1/2->1/3': lambda k: Fr(1, 3) - Fr(1, 4) * cb[1](k + 10) + Fr(1, 4) * cb[1](k - 4) + Fr(5, 2) * cb[2](k + 3) + 6 * cb[2](k - 2),
}
pinfo = {name: [k for k in range(0, 7) if f(k) != U[2][k]] for name, f in pert.items()}
R.check('F5-negctrl', all(v for v in pinfo.values()), '改坏的式子在窗口 0<=k<=6 内不符的 k：%s' % pinfo)

# ---- F6：K_1、K_2 中的纤维恒等式与系数
K1, K2, K3 = KField(1), KField(2), KField(3)
W1, W2, W3 = K1.from_dict(Wt_dict(1)), K2.from_dict(Wt_dict(2)), K3.from_dict(Wt_dict(3))
okA = W1 == (Fr(0), Fr(1), Fr(1))
okB, coefB = in_span2(K1, W1, -4, 10)
okC, coefC = in_span2(K2, W2, 3, 8)
R.check('F6-fiber', okA and okB and coefB == (Fr(1, 4), Fr(-1, 4)) and okC and coefC == (5, 12),
        'K_1：W~_1 = x + x^2；W~_1 = %s x^-4 + %s x^10；K_2：W~_2 = %s x^3 + %s x^8' % (coefB[0], coefB[1], coefC[0], coefC[1]))


def kappa(m, i):
    return Fr((-1) ** (m - i), factorial(i) * factorial(m - i))


# m=2：lam_i x^{-a} + mu_i x^{-a'} = kappa x^{-6} W~_i，即原子 kappa*alpha*c_i(k+6-e)
lam = {(1, 6 - (-4)): kappa(2, 1) * coefB[0], (1, 6 - 10): kappa(2, 1) * coefB[1],
       (2, 6 - 3): kappa(2, 2) * coefC[0], (2, 6 - 8): kappa(2, 2) * coefC[1]}
expect = {(1, 10): Fr(-1, 4), (1, -4): Fr(1, 4), (2, 3): Fr(5, 2), (2, -2): Fr(6)}
R.check('F6-coeffs', lam == expect and kappa(2, 0) == Fr(1, 2),
        'm=2 的系数由 kappa_{2,i}=%s,%s 与纤维恒等式得出：%s；gamma=(-1)^2/2!=1/2' % (kappa(2, 1), kappa(2, 2), lam))

# ---- F7：约化——直接对 W_m/P_m 做部分分式，与 kappa x^{-3m} W~_i 比较；x=1 处的留数
ok7 = True
cnt7 = 0
for m in range(1, 9):
    Wm = W_poly(m)
    for i in range(1, m + 1):
        Ki = KField(i)
        other = [1]
        for v in range(m + 1):
            if v != i:
                other = pmul(other, b_poly(v))
        Ri = Ki.mul(Ki.reduce_poly(Wm), Ki.inv(Ki.reduce_poly(other)))     # R_i = W_m (P_m/b_i)^{-1} mod b_i
        Wti = Ki.from_dict(Wt_dict(i))
        target = tuple(kappa(m, i) * t for t in Ki.mul(Ki.xpow(-3 * m), Wti))
        ok7 &= (Ri == target)
        cnt7 += 1
    # x=1：W_m(1)/prod_{v>=1} b_v(1)
    r0 = Fr(sum(Wm), 1)
    for v in range(1, m + 1):
        r0 /= sum(b_poly(v))
    ok7 &= (r0 == Fr((-1) ** m, factorial(m)))
R.check('F7-partfrac', ok7, '部分分式分子 R_i = W_m*(P_m/b_i)^{-1} mod b_i 等于 kappa_{m,i} x^{-3m} W~_i（%d 对 (m,i)，m<=8）；x=1 处留数 (-1)^m/m!' % cnt7)

# ---- F8：引理 2.1
ok8 = True
for m in range(0, 9):
    for k in range(0, 61):
        s = Fr((-1) ** m, factorial(m))
        for i in range(1, m + 1):
            A = KField(i).from_dict(Wt_dict(i))
            s += kappa(m, i) * sum(A[r] * c(i, k + 3 * m - r) for r in range(3))
        ok8 &= (s == U[m][k])
R.check('F8-lemma21', ok8, '引理 2.1：U_k(m) = (-1)^m/m! + sum_i kappa_{m,i} sum_r A_i^(r) c_i(k+3m-r)（0<=m<=8，0<=k<=60）')

# ---- F9：措辞——m>=3 时纤维 1、2 两个原子就够，纤维 3 起用三个相邻原子（字面「每个 i 至少三个原子」不成立）
pairs12 = {1: (-4, 10, coefB), 2: (3, 8, coefC)}
info9 = []
ok9 = True
for m in (3, 4, 5, 6):
    def rhs_mixed(k, use_bar):
        f = (lambda i, n: cb[i](n)) if use_bar else (lambda i, n: c(i, n))
        s = Fr((-1) ** m, factorial(m))
        for i in (1, 2):
            e1, e2, (al, be) = pairs12[i]
            s += kappa(m, i) * (al * f(i, k + 3 * m - e1) + be * f(i, k + 3 * m - e2))
        for i in range(3, m + 1):
            A = KField(i).from_dict(Wt_dict(i))
            s += kappa(m, i) * sum(A[r] * f(i, k + 3 * m - r) for r in range(3))
        return s
    badc = [k for k in range(0, 201) if rhs_mixed(k, False) != U[m][k]]
    badb = [k for k in range(0, 201) if rhs_mixed(k, True) != U[m][k]]
    natoms = 2 + 2 + 3 * (m - 2)
    info9.append('m=%d：原子数 2+2+%s=%d，c 版不符的 k=%s，c~ 版不符 %s' % (m, '+'.join(['3'] * (m - 2)), natoms, badc, badb))
    ok9 &= (badb == [] and all(k < 3 * m for k in badc))
R.check('F9-mixed', ok9, '；'.join(info9))

# ---- F10：|a|,|a'|<=40 的两原子搜索与单原子搜索（数据），与 notes/12 注 3.2、notes/08 b2-small 对照
cntp = {}
lst = {}
for i in range(1, 9):
    Ki = KField(i)
    Wi = Ki.from_dict(Wt_dict(i))
    pr = []
    for a in range(-40, 41):
        for b in range(a + 1, 41):
            if det3cols(Wi, Ki.xpow(a), Ki.xpow(b)) == 0:
                pr.append((a, b))
    cntp[i] = len(pr)
    lst[i] = pr
nb2 = sorted({(-a, b - a) for (a, b) in lst[2]} | {(-b, a - b) for (a, b) in lst[2]})
R.check('F10-window', cntp[1] == 14 and lst[2] == [(3, 8), (5, 15)] and all(cntp[i] == 0 for i in range(3, 9))
        and nb2 == [(-15, -10), (-8, -5), (-5, 10), (-3, 5)],
        '两原子对数 %s；i=2 的对 %s 对应 (n,b)=%s（= notes/08 b2-small 纤维 2 的 4 个解）' % (cntp, lst[2], nb2))
single = {}
for i in range(1, 9):
    Ki = KField(i)
    Wi = Ki.from_dict(Wt_dict(i))
    sol = [a for a in range(-300, 301) if Ki.mul(Wi, Ki.xpow(-a))[1:] == (0, 0)]
    single[i] = sol
R.check('F10-single', all(not v for v in single.values()), '单原子 W~_i ∈ Q x^a（|a|<=300，1<=i<=8）的解：%s' % single)

# ---- F11：b_3 的性质与 W~_3 非零
cands = [Fr(1), Fr(-1), Fr(1, 3), Fr(-1, 3)]
vals = [1 - r - 3 * r ** 3 for r in cands]
disc = 0 * 0 * 1 * 1 - 4 * 3 * 1 ** 3 - 0 - 27 * 9 * 1 + 0     # i x^3 + x - 1，i=3
nW3 = K3.norm(W3)
R.check('F11-b3', all(v != 0 for v in vals) and disc == -255 and nW3 != 0,
        'b_3 在 ±1、±1/3 处的值 %s（无有理根，不可约）；disc(3x^3+x-1)=%d（=-3*5*17，非零，三根互异）；N(W~_3)=%s != 0' % (vals, disc, nW3))

print('time %.1fs' % (time.time() - t0))
R.finish()
