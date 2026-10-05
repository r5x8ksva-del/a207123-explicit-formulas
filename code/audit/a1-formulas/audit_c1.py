# -*- coding: utf-8 -*-
"""审计 a1-formulas：报告 C-1 部分（T1.0–T1.9）的显式公式/数值。"""
import time
from fractions import Fraction
from decimal import Decimal, getcontext
from common import *  # noqa

t0 = time.time()
K, M = 60, 20
T = own_U_table(K, M)                       # 自写定义 DP
Tc = core.U_fast_table(K, 62)               # core 定义 DP（后缀和），用于 m 更大
report(all(T[k][m] == Tc[k][m] for k in range(K + 1) for m in range(M + 1)),
       'base.own-vs-core', 'own height DP == core.U_fast_table, k<=60, m<=20')
ref_ok = all(core.U_list(m, 12)[k] == T[k][m] for m in range(0, 9) for k in range(13))
report(ref_ok, 'base.own-vs-reflist', 'own DP == core.U_list (参考实现), k<=12, m<=8')
mc_ok = all(core.U_multichain(k, m) == T[k][m] for k in range(0, 8) for m in range(0, 6))
report(mc_ok, 'T1.0c.multichain', 'U_k(m) == 多重链数 core.U_multichain, k<=7, m<=5')

# ---------------- T1.0 (a) a_k(n)=U_k(ceil(n/2))U_k(floor(n/2)) ----------------
ok = True
bad = []
for k in range(1, 7):
    for n in range(0, 11 if k <= 5 else 9):
        a = core.a_direct(n, k)
        b = T[k][(n + 1) // 2] * T[k][n // 2]
        if a != b:
            ok = False
            bad.append((k, n, a, b))
for k in range(1, 5):
    for n in range(0, 6):
        if n * k <= 16 and core.a_brute(n, k) != T[k][(n + 1) // 2] * T[k][n // 2]:
            ok = False
            bad.append(('brute', k, n))
report(ok, 'T1.0a.product', 'a_k(n)=U_k(ceil n/2)U_k(floor n/2) vs core.a_direct (k<=6,n<=10) & a_brute (nk<=16); bad=%s' % bad[:3])
report([core.a_direct(n, 3) for n in range(1, 7)] == [6, 36, 102, 289, 612, 1296], 'T1.0a.a3', 'a_3(1..6)=6,36,102,289,612,1296')

# ---------------- T1.1 引理 1 ----------------
def Uc(k, m):
    if k == 0:
        return 1
    if k == -1:
        return 1
    if k == -2:
        return 0
    if m == -1:
        return 0
    return T[k][m]

ok = all(T[k][m] == Uc(k, m - 1) + Uc(k - 1, m) + m * Uc(k - 3, m) for k in range(1, K + 1) for m in range(0, M + 1))
report(ok, 'T1.1.lemma1', 'U_k(m)=U_k(m-1)+U_{k-1}(m)+m U_{k-3}(m)，约定 U_0=U_{-1}=1,U_{-2}=0,U_k(-1)=0; 1<=k<=60, 0<=m<=20')

# ---------------- T1.2 (C1) 与多项式 u_k ----------------
ok = all(T[k][m] == sum(Uc(k - 1, j) + j * Uc(k - 3, j) for j in range(m + 1)) for k in range(1, K + 1) for m in range(M + 1))
report(ok, 'T1.2.C1-sum', '(C1) U_k(m)=sum_{j<=m}[U_{k-1}(j)+j U_{k-3}(j)], k<=60, m<=20')
U = {}
KP = 24
TP = core.U_fast_table(KP, KP + 8)
for k in range(0, KP + 1):
    U[k] = interp(list(range(k + 1)), [TP[k][m] for m in range(k + 1)])
ok_fit = all(peval(U[k], m) == TP[k][m] for k in range(KP + 1) for m in range(KP + 9))
report(ok_fit, 'T1.2.poly-fit', 'u_k (k<=24) 用 m=0..k 插值，并在 m<=k+8 与定义 DP 吻合（deg<=k 得证）')
lead_ok = all(pdeg(U[k]) == k and U[k][-1] == (Fraction(2, factorial(k)) if k >= 2 else 1) for k in range(KP + 1))
report(lead_ok, 'T1.2.deg-lead', 'deg u_k=k，首项 2/k!（k>=2），k=0,1 为 1；k<=24')
report(all(peval(U[k], -1) == 0 for k in range(1, KP + 1)), 'T1.2.u(-1)', 'u_k(-1)=0, 1<=k<=24')
um1 = [Fraction(1)]
um2 = []
def uu(k):
    if k == -1:
        return um1
    if k == -2:
        return um2
    return U[k]
ok = True
for k in range(1, KP + 1):
    lhs = psub(U[k], pcompose_linear(U[k], 1, -1))
    rhs = padd(uu(k - 1), pshift(uu(k - 3), 1))
    if trim(psub(lhs, rhs)):
        ok = False
report(ok, 'T1.2.poly-diff', 'u_k(x)-u_k(x-1)=u_{k-1}(x)+x u_{k-3}(x)（u_{-1}=1,u_{-2}=0）多项式恒等, 1<=k<=24')
f1 = padd(uu(0), pshift(uu(-2), 1))
f2 = padd(uu(1), pshift(uu(-1), 1))
f3 = padd(uu(2), pshift(uu(0), 1))
report(f1 == [1] and f2 == [1, 2] and f3 == padd(ppow([1, 1], 2), [0, 1]), 'T1.2.f123', 'f_1=1, f_2=2x+1, f_3=(x+1)^2+x')

# ---------------- T1.3 (C2) ----------------
N_X = 61
ok_rec = True
for m in range(0, M + 1):
    for k in range(0, K + 1):
        lhs = T[k][m] - (T[k - 1][m] if k >= 1 else 0) - (m * T[k - 3][m] if k >= 3 else 0)
        rhs = (T[k][m - 1] if m >= 1 else (1 if k == 0 else 0)) + (m if k == 2 else 0)
        if lhs != rhs:
            ok_rec = False
report(ok_rec, 'T1.3.1-rec', '(1-x-m x^3)G_m=G_{m-1}+m x^2 (G_{-1}=1) 逐系数, k<=60, m<=20')
ok_cl = True
ok_id = True
for m in range(0, M + 1):
    Pm = P_poly(m)
    Wm = W_poly(m)
    ser = series_of_rational(Wm, Pm, N_X)
    if any(ser[k] != T[k][m] for k in range(N_X)):
        ok_cl = False
    sumP = []
    for j in range(m):
        sumP = padd(sumP, P_poly(j))
    rhs = psub(psub([1], Pm), pshift(sumP, 1))
    if trim(psub(pshift(Wm, 1), rhs)):
        ok_id = False
report(ok_cl, 'T1.3.1-closed', 'G_m=W_m/P_m 展开到 x^60 与 DP 一致, m<=20')
report(ok_id, 'T1.3.1-xW', 'x W_m = 1 - P_m - x sum_{j<m} P_j 多项式恒等, m<=20')

ok = True
for m in range(0, M + 1):
    Pm, Wm = P_poly(m), W_poly(m)
    g = pgcd(Wm, Pm)
    if not (len(g) == 1 and pdeg(Pm) == 3 * m + 1 and (m == 0 or pdeg(Wm) == 3 * m) and Pm[0] == 1
            and (m == 0 or Wm[-1] == (-1) ** m * factorial(m)) and peval(Wm, 1) == 1):
        ok = False
report(ok, 'T1.3.2-gcd', 'gcd(W_m,P_m)=1, deg P_m=3m+1, deg W_m=3m, lc W_m=(-1)^m m!, P_m(0)=1, W_m(1)=1; m<=20')
# BM：最小递推阶恰为 3m+1，连接多项式恰为 P_m
TB = own_U_table(70, 9)
ok = True
info = []
for m in range(0, 10):
    L_need = 3 * m + 1
    seq = [TB[k][m] for k in range(0, min(71, 2 * L_need + 12))]
    Cx, L = bm_rational(seq)
    Pm = P_poly(m)
    if L != L_need or trim(psub(Cx, [Fraction(c) for c in Pm])):
        ok = False
        info.append((m, L))
report(ok, 'T1.3.2-BM', 'Berlekamp-Massey(Q) 作用于定义 DP：线性复杂度=3m+1、连接多项式=P_m, m<=9; bad=%s' % info)
# 可约 b_i
red = [i for i in range(1, 3001) if any(y ** 3 - y ** 2 - i == 0 for y in range(1, 16))]
report(red == [y * y * (y - 1) for y in range(2, 16) if y * y * (y - 1) <= 3000], 'T1.3.2-reducible',
       'b_i (1<=i<=3000) 有有理根 ⇔ i=y^2(y-1): %s' % red[:6])
ok = True
for y in range(2, 30):
    i = y * y * (y - 1)
    f = pmul([1, -y], [1, y - 1, y * (y - 1)])
    disc = (y - 1) ** 2 - 4 * y * (y - 1)
    if f != b_poly(i) or disc != -(y - 1) * (3 * y + 1) or peval(b_poly(i), 1) != -i or 1 - y != peval([1, -y], 1) or peval([1, y - 1, y * (y - 1)], 1) != y * y:
        ok = False
report(ok, 'T1.3.2-factor', 'b_i=(1-yx)(1+(y-1)x+y(y-1)x^2)、判别式 -(y-1)(3y+1)、x=1 处值 -i,1-y,y^2（y<30）')
report(psub(W_poly(1), b_poly(1)) == [0, 1, 1], 'T1.3.2-W1b1', 'W_1-b_1=x+x^2')
report(peval(W_poly(4), Fraction(1, 2)) == Fraction(645, 512), 'T1.3.2-W4half', 'W_4(1/2)=645/512 (实算 %s)' % peval(W_poly(4), Fraction(1, 2)))
# (3) 无重因子、判别式
ok = True
for i in range(1, 31):
    for j in range(i + 1, 31):
        if len(pgcd(b_poly(i), b_poly(j))) != 1:
            ok = False
    # z^3 - z^2 - i 的判别式：a=-1,b=0,c=-i
    a_, b_, c_ = -1, 0, -i
    disc = a_ * a_ * b_ * b_ - 4 * b_ ** 3 - 4 * a_ ** 3 * c_ - 27 * c_ * c_ + 18 * a_ * b_ * c_
    if disc != -i * (4 + 27 * i):
        ok = False
    if len(pgcd(b_poly(i), pderiv(b_poly(i)))) != 1:
        ok = False
report(ok, 'T1.3.3-sqfree', 'b_i 两两互素、各自无重根、disc(z^3-z^2-i)=-i(4+27i), i<=30')

# (4) 增长率与 c_m 数值
getcontext().prec = 60
def rho(mm):
    lo, hi = Decimal(1), Decimal(mm + 2)
    for _ in range(250):
        mid = (lo + hi) / 2
        if mid ** 3 - mid ** 2 - mm > 0:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2
rhos = [rho(mm) for mm in range(0, 21)]
ok_inc = all(rhos[i + 1] > rhos[i] for i in range(1, 20))
ok_cplx = all(Decimal(mm) / rhos[mm] < rhos[mm] ** 2 for mm in range(1, 21))
report(ok_inc and ok_cplx, 'T1.3.4-rho', 'ρ_m 严格增；复根模长平方 m/ρ_m < ρ_m^2 (m<=20)')
# c_m 由留数式 (G_{m-1}(x_m)+m x_m^2)/(x_m(1+3m x_m^2))；与 U_k(m)/ρ^k 对比
TK = core.U_fast_table(900, 8)
ok = True
msgs = []
for mm in range(1, 9):
    r = rhos[mm]
    xm = 1 / r
    # G_{m-1}(x_m) 用闭式 W/P 求值
    Wv = sum(Decimal(int(c)) * xm ** i for i, c in enumerate(W_poly(mm - 1)))
    Pv = sum(Decimal(c) * xm ** i for i, c in enumerate(P_poly(mm - 1)))
    G = Wv / Pv
    cm = (G + mm * xm * xm) / (xm * (1 + 3 * mm * xm * xm))
    est = Decimal(TK[900][mm]) / r ** 900
    rel = abs(est / cm - 1)
    msgs.append('m=%d c=%.10f rel=%.1e' % (mm, cm, rel))
    if not (cm > 0 and rel < Decimal('1e-6')):
        ok = False
report(ok, 'T1.3.4-cm', 'c_m 留数式 vs U_900(m)/ρ^900 (m<=8)：' + '; '.join(msgs[:3]))

# ---------------- T1.4 (C3) ----------------
NT = N_table_from_U(T, 21)
ok = True
for k in range(0, 10):
    d = own_N_dfs(k)
    for q in range(0, k + 1):
        if d.get(q, 0) != NT[k][q]:
            ok = False
report(ok, 'T1.4.1-NIE', 'N(k,q) 容斥式 == 自写 DFS 满射合法词计数, k<=9')
ok = all(T[k][m] == sum(NT[k][q] * C(m + 1, q) for q in range(k + 1)) for k in range(0, 21) for m in range(0, M + 1))
report(ok, 'T1.4.1-basis', 'U_k(m)=sum_q N(k,q) C(m+1,q), k<=20, m<=20')
# 大范围 N（引理 1 + 容斥），先比对
TL = lemma1_table(240, 240)
report(all(TL[k][m] == Tc[k][m] for k in range(61) for m in range(63)), 'base.lemma1-vs-core', 'lemma1_table == core.U_fast_table, k<=60, m<=62')
NB = [[N_from_table(TL, k, q) for q in range(0, k + 1)] + [0] * 3 for k in range(0, 121)]
def Nb(k, q):
    if k < 0 or q < 0 or q > k:
        return 0
    return NB[k][q]
ok = True
for k in range(3, 121):
    for r in range(0, k):
        lhs = Nb(k, r + 1)
        rhs = Nb(k - 1, r) + Nb(k - 1, r + 1) + r * (Nb(k - 3, r - 1) + 2 * Nb(k - 3, r) + Nb(k - 3, r + 1))
        if lhs != rhs:
            ok = False
report(ok, 'T1.4.2-tri', '三角递推 N(k,r+1)=N(k-1,r)+N(k-1,r+1)+r[...], 3<=k<=120')
report(Nb(1, 1) == 1 and Nb(2, 1) == 1 and Nb(2, 2) == 2, 'T1.4.2-init', 'N(1,1)=1, N(2,1)=1, N(2,2)=2')
# 只给 N(0,0)=1 + 零边界：递推从 k=1 起
def build_tri(conv, KK=12):
    Nt = {}
    def g(k, q):
        if (k, q) in Nt:
            return Nt[(k, q)]
        if q < 0:
            return 0
        if k == 0:
            return 1 if q == 0 else 0
        if k < 0:
            if conv == 'ext' and k == -1:
                return 1 if q == 0 else 0
            return 0
        if q == 0:
            return 0
        r = q - 1
        v = g(k - 1, r) + g(k - 1, r + 1) + r * (g(k - 3, r - 1) + 2 * g(k - 3, r) + g(k - 3, r + 1))
        Nt[(k, q)] = v
        return v
    return g
g0 = build_tri('zero')
g1 = build_tri('ext')
report(g0(2, 2) == 1, 'T1.4.2-zero-conv', '只给 N(0,0)=1 加零边界时 k=2 得 N(2,2)=%d（报告说 1）' % g0(2, 2))
ok = all(g1(k, q) == Nb(k, q) for k in range(1, 40) for q in range(0, k + 3))
report(ok, 'T1.4.2-ext-conv', '约定 N(-1,0)=1,N(-1,q>=1)=0,N(-2,.)=0 时递推对 k>=1（r>=0）全部成立（k<40）')
report(all(Nb(k, k) == 2 for k in range(2, 121)), 'T1.4.3-Nkk', 'N(k,k)=2, 2<=k<=120')
ok = all(Nb(k, k - 1) == k * k - k - 4 for k in range(4, 121)) and Nb(3, 2) == 4 and Nb(2, 1) == 1 and Nb(4, 3) == 8
report(ok, 'T1.4.4-Nkk1', 'N(k,k-1)=k^2-k-4 (4<=k<=120)；N(3,2)=4, N(2,1)=1, N(4,3)=8')
ok = all(Nb(k, k - 1) - Nb(k - 1, k - 2) == 2 * k - 2 for k in range(5, 121))
report(ok, 'T1.4.4-incr', 'k>=5 时增量 2k-2')
prompt_rows = {1: [1], 2: [1, 2], 3: [1, 4, 2], 4: [1, 7, 8, 2], 5: [1, 12, 25, 16, 2], 6: [1, 19, 59, 65, 26, 2],
               7: [1, 29, 124, 199, 139, 38, 2], 8: [1, 44, 253, 557, 574, 277, 52, 2],
               9: [1, 66, 493, 1416, 1991, 1446, 509, 68, 2], 10: [1, 98, 925, 3337, 6051, 6012, 3257, 871, 86, 2]}
report(all([Nb(k, q) for q in range(1, k + 1)] == prompt_rows[k] for k in prompt_rows), 'T1.4.prompt-tri', '提示词 N 三角 k<=10 与定义一致')

# ---------------- T1.5 (C4) ----------------
NN = 61
ok = True
for i in range(0, 21):
    cs = c_seq(i, NN)
    if any(cs[n] != sum(C(n - 2 * j, j) * i ** j for j in range(0, n // 3 + 1)) for n in range(NN + 1)):
        ok = False
report(ok, 'T1.5.1-c', 'c_i(n)=sum_{j<=n/3} C(n-2j,j) i^j, i<=20, n<=61')
ok1 = True
ok2 = True
for m in range(0, M + 1):
    ser = sinv(P_poly(m), NN)
    for n in range(NN):
        v = sum(stirling2(m + s, m) * C(n + m - 2 * s, m + s) for s in range(0, n // 3 + 1))
        if v != ser[n]:
            ok1 = False
        w = sum((-1) ** (m - i) * comb(m, i) * c_seq(i, n + 3 * m)[n + 3 * m] for i in range(m + 1))
        if w != factorial(m) * ser[n]:
            ok2 = False
report(ok1, 'T1.5.2-S', '[x^n]1/P_m=sum_s S(m+s,m)C(n+m-2s,m+s), m<=20, n<=60')
report(ok2, 'T1.5.3-pf', 'm![x^n]1/P_m=sum_i (-1)^{m-i}C(m,i)c_i(n+3m), m<=20, n<=60')
# Θ 公式（k>=0）
def Theta(t, n, m, cache):
    s = 0
    for r in range(t + 1):
        cs = cache.setdefault(m - r, c_seq(m - r, 400))
        s += (-1) ** r * comb(t, r) * (cs[n] if n >= 0 else 0)
    assert s % factorial(t) == 0
    return s // factorial(t)
ok = True
ok_inner = True
cache = {}
for m in range(0, M + 1):
    for k in range(0, K + 1):
        v = Theta(m, k + 1 + 3 * m, m, cache) - sum(Theta(t, k + 3 * t, m, cache) for t in range(m))
        if v != T[k][m]:
            ok = False
    for t in range(0, m + 1):
        num = P_poly(m - t - 1) if m - t - 1 >= 0 else [1]
        ser = series_of_rational(num, P_poly(m), 31)
        prod = [1]
        for i in range(m - t, m + 1):
            prod = pmul(prod, b_poly(i))
        ser2 = sinv(prod, 31)
        for n in range(31):
            if not (Theta(t, n + 3 * t, m, cache) == ser[n] == ser2[n]):
                ok_inner = False
report(ok, 'T1.5.4-theta', 'Θ 公式 U_k(m)=Θ_m(k+1+3m)-sum_{t<m}Θ_t(k+3t) 对 0<=k<=60, m<=20 成立（含 k=0）')
report(ok_inner, 'T1.5.4-theta-inner', 'Θ_t(n+3t)=[x^n]prod_{i=m-t}^m b_i^{-1}=[x^n]P_{m-t-1}/P_m, m<=20, n<=30')
# 注的反例数值
v1 = stirling2(2, 1) * Cgen(-1, 2)
v2 = sum(Cgen(1 - 2 * j, j) * 5 ** j for j in range(0, 2))
report(v1 == 1 and v2 == -4, 'T1.5.note', 'S(2,1)C(-1,2)=%s；c_5(1) 按广义二项式取 j=0,1 得 %s（真值 %d）' % (v1, v2, c_seq(5, 1)[1]))

# ---------------- T1.6 PDE ----------------
ok = True
for k in range(0, K + 1):
    for m in range(0, M + 1):
        def UU(kk, mm):
            return T[kk][mm] if kk >= 0 and mm >= 0 else 0
        lhs = UU(k, m) - UU(k - 1, m) - UU(k, m - 1) - m * UU(k - 3, m)
        rhs = (1 if k == 0 and m == 0 else 0) + (m if k == 2 else 0)
        if lhs != rhs:
            ok = False
report(ok, 'T1.6.pde', '(1-x-t)F-x^3 t F_t=1+x^2t/(1-t)^2 逐系数, k<=60, m<=20')

# ---------------- T1.7 h 多项式 ----------------
def h_from_U(k):
    return trim([sum((-1) ** (i - j) * comb(k + 1, i - j) * T[k][j] for j in range(0, i + 1)) for i in range(0, min(k, M) + 1)])
H = {k: h_from_U(k) for k in range(0, 21)}
# 检查 h_k 次数 <= k（用 M=20 足够 k<=20）：(1-t)^{k+1} f_k 的更高系数应为 0
ok = True
for k in range(0, 21):
    full = [sum((-1) ** (i - j) * comb(k + 1, i - j) * T[k][j] for j in range(0, i + 1)) for i in range(0, M + 1)]
    if any(full[i] != 0 for i in range(k + 1, M + 1)):
        ok = False
report(ok, 'T1.7.deg', 'h_k=(1-t)^{k+1}sum_m U_k(m)t^m 是 <=k 次多项式 (k<=19 由 m<=20 判定)')
ok = True
for k in range(1, 21):
    s = []
    for q in range(1, k + 1):
        s = padd(s, pscale(pmul(pshift([1], q - 1), ppow([1, -1], k - q)), NT[k][q]))
    if trim(psub(s, H[k])):
        ok = False
report(ok and H[0] == [1], 'T1.7.Nform', 'h_k=sum_q N(k,q)t^{q-1}(1-t)^{k-q} (1<=k<=20), h_0=1')
def hrec(h0, h1, h2, KK):
    hs = [h0, h1, h2]
    for k in range(3, KK + 1):
        a = hs[k - 3]
        term = padd(pmul([1, -1], pderiv(a)), pscale(a, k - 2))
        hs.append(padd(hs[k - 1], pmul([0, 1, -1], term)))
    return hs
hs = hrec([1], [1], [1, 1], 20)
report(all(trim(psub(hs[k], H[k])) == [] for k in range(0, 21)), 'T1.7.rec', '递推 h_k=h_{k-1}+t(1-t)[(1-t)h_{k-3}\'+(k-2)h_{k-3}] 初值 h_0=1,h_1=1,h_2=1+t, k<=20')
hs_bad = hrec([1], [1], [1], 4)
report(hs_bad[3] == [1, 1, -1], 'T1.7.badinit', '若 h_2=1 则 h_3=%s（报告：1+t-t^2）' % hs_bad[3])
given = {3: [1, 2, -1], 4: [1, 4, -3], 5: [1, 8, -5, -2], 6: [1, 14, -7, -8, 2]}
report(all(H[k] == given[k] for k in given), 'T1.7.h3-6', 'h_3..h_6 = %s' % [H[k] for k in range(3, 7)])
report(all(peval(H[k], 1) == 2 for k in range(2, 21)) and peval(H[1], 1) == 1, 'T1.7.h1', 'h_k(1)=2 (2<=k<=20)')

# ---------------- T1.8 (C7) 分子 ----------------
TN = core.U_fast_table(48, 12)
ok = True
nums = {}
for q in range(1, 11):
    Fq = [N_from_table(TN, k, q) for k in range(0, 49)]
    num = smul(Fq, P_poly(q - 1), 49)
    nums[q] = trim(num)
    deg = 3 * q - 2
    if any(num[i] != 0 for i in range(deg + 1, 49)):
        ok = False
    if nums[q][-1] != factorial(q - 1) or pdeg(nums[q]) != deg:
        ok = False
    low = next(i for i, c in enumerate(nums[q]) if c != 0)
    if q >= 2 and not (low == q and nums[q][q] == 2):
        ok = False
report(ok, 'T1.8.poly', 'Num_q=P_{q-1} sum_k N(k,q)x^k 是多项式、次数 3q-2、首项 (q-1)!、最低项 2x^q（2<=q<=10，截断到 x^48）')
report(nums[1] == [0, 1], 'T1.8.Num1', 'Num_1=x')
given = {2: [0, 0, 2, 0, 1], 3: [0, 0, 0, 2, 2, 7, 0, 2], 4: [0, 0, 0, 0, 2, 8, 13, 15, 29, 0, 6]}
report(all(nums[q] == given[q] for q in given), 'T1.8.Num234', 'Num_2..Num_4 = 提示词给出的多项式')

# ---------------- T1.9 (C8) ----------------
ok = True
for k in range(1, 9):
    u = U[k]
    c = u[-1]
    E = pcompose_linear(pmul(u, u), Fraction(1, 2), 0)                          # u(n/2)^2
    O = pmul(pcompose_linear(u, Fraction(1, 2), Fraction(1, 2)), pcompose_linear(u, Fraction(1, 2), Fraction(-1, 2)))
    p = pscale(padd(E, O), Fraction(1, 2))
    qq = pscale(psub(E, O), Fraction(1, 2))
    if not (pdeg(p) == 2 * k and p[-1] == c * c / 4 ** k and pdeg(qq) == 2 * k - 2 and qq[-1] == c * c * k / (2 * 4 ** k)):
        ok = False
report(ok, 'T1.9.pq', 'a_k=p+(-1)^n q：deg p=2k 首项 c^2/4^k；deg q=2k-2 首项 c^2k/(2·4^k)（1<=k<=8）')
ok = True
for k in range(1, 5):
    TT = core.U_fast_table(k, 40)
    a = [TT[k][(n + 1) // 2] * TT[k][n // 2] for n in range(0, 2 * (4 * k) + 20)]
    Cx, L = bm_rational(a)
    den = pmul(ppow([1, -1], 2 * k + 1), ppow([1, 1], 2 * k - 1))
    if L != 4 * k or trim(psub(Cx, [Fraction(v) for v in den])):
        ok = False
report(ok, 'T1.9.order', 'a_k(n) 的最小递推阶=4k，连接多项式=(1-x)^{2k+1}(1+x)^{2k-1}（BM，k<=4）')

summary('audit_c1')
print('elapsed %.1fs' % (time.time() - t0))
