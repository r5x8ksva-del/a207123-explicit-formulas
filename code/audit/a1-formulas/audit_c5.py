# -*- coding: utf-8 -*-
"""审计 a1-formulas：报告 C-5 部分（T5.1–T5.4）的显式公式/数值。"""
import os
import time
from fractions import Fraction
from decimal import Decimal, getcontext
from math import comb, factorial, floor, ceil
from common import *  # noqa

t0 = time.time()
getcontext().prec = 80

# ---------------- Q[σ]/(σ^3-σ^2-j) ----------------
class Cub:
    """Q[σ]/(σ^3 - σ^2 - j)。"""
    def __init__(self, a, j):
        a = [Fraction(v) for v in a] + [Fraction(0)] * 3
        self.a, self.j = a[:3], j
    def _c(self, o):
        return o if isinstance(o, Cub) else Cub([o], self.j)
    def __add__(s, o):
        o = s._c(o)
        return Cub([s.a[i] + o.a[i] for i in range(3)], s.j)
    __radd__ = __add__
    def __sub__(s, o):
        o = s._c(o)
        return Cub([s.a[i] - o.a[i] for i in range(3)], s.j)
    def __rsub__(s, o):
        return s._c(o) - s
    def __mul__(s, o):
        o = s._c(o)
        r = [Fraction(0)] * 5
        for i in range(3):
            for k in range(3):
                r[i + k] += s.a[i] * o.a[k]
        for d in (4, 3):          # σ^3 = σ^2 + j
            c = r[d]
            r[d] = 0
            r[d - 1] += c
            r[d - 3] += s.j * c
        return Cub(r[:3], s.j)
    __rmul__ = __mul__
    def __pow__(s, e):
        r = Cub([1], s.j)
        b = s
        while e:
            if e & 1:
                r = r * b
            b = b * b
            e >>= 1
        return r
    def inv(s):
        cols = [(s * Cub(v, s.j)).a for v in ([1], [0, 1], [0, 0, 1])]
        m = [[cols[c][r] for c in range(3)] + [Fraction(1 if r == 0 else 0)] for r in range(3)]
        for c in range(3):
            p = next(r for r in range(c, 3) if m[r][c] != 0)
            m[c], m[p] = m[p], m[c]
            pv = m[c][c]
            m[c] = [v / pv for v in m[c]]
            for r in range(3):
                if r != c and m[r][c] != 0:
                    f = m[r][c]
                    m[r] = [m[r][i] - f * m[c][i] for i in range(4)]
        return Cub([m[i][3] for i in range(3)], s.j)
    def __truediv__(s, o):
        return s * s._c(o).inv()
    def trace(s):
        # Tr(1)=3, Tr(σ)=e1=1, Tr(σ^2)=e1^2-2e2=1
        return 3 * s.a[0] + s.a[1] + s.a[2]
    def __eq__(s, o):
        return s.a == s._c(o).a

def gamma1(j):
    s = Cub([0, 1], j)
    inner = s ** (3 * j + 1) * Fraction(1, factorial(j))
    for i in range(j):
        inner = inner - s ** (3 * i) * Fraction(1, factorial(i))
    return s * inner / (3 * s - 2)
def gamma2(j):
    s = Cub([0, 1], j)
    num = s ** (3 * j + 3) * Fraction(1, factorial(j))
    for i in range(j):
        num = num + s ** (3 * i + 1) * Fraction(j - i, factorial(i))
    return num / (s * s + 3 * j)

K, M = 40, 10
T = own_U_table(K, M)
ok_g = all(gamma1(j) == gamma2(j) for j in range(1, 25))
report(ok_g, 'T5.1.1-gamma-forms', 'γ_j 的两种写法在 Q[σ]/(σ^3-σ^2-j) 中相等（1<=j<=24，含可约 j=4,18）')
G1 = {j: gamma1(j) for j in range(1, M + 1)}
ok = True
for m in range(0, M + 1):
    for k in range(0, K + 1):
        tot = Fraction((-1) ** m, factorial(m))          # j=0：σ=1，γ_0(1)=1
        for j in range(1, m + 1):
            s = Cub([0, 1], j)
            tot += Fraction((-1) ** (m - j), factorial(m - j)) * (G1[j] * s ** (k + 3 * (m - j))).trace()
        if tot != T[k][m]:
            ok = False
report(ok, 'T5.1.1-binet', 'Binet 型精确公式（按共轭求和=迹，精确有理）对 0<=k<=40, 0<=m<=10 与定义 DP 一致')

# ---------------- 数值：ρ_m、c_m ----------------
def rho(mm, prec=80):
    getcontext().prec = prec
    lo, hi = Decimal(1), Decimal(mm + 2)
    for _ in range(int(prec * 3.4) + 10):
        mid = (lo + hi) / 2
        if mid ** 3 - mid ** 2 - mm > 0:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2
R = {mm: rho(mm) for mm in range(0, 41)}
def cm_forms(mm):
    r = R[mm]
    x = 1 / r
    # 形式 1：留数式
    if mm >= 1:
        Wv = sum(Decimal(int(c)) * x ** i for i, c in enumerate(W_poly(mm - 1)))
        Pv = sum(Decimal(int(c)) * x ** i for i, c in enumerate(P_poly(mm - 1)))
        f1 = (Wv / Pv + mm * x * x) / (x * (1 + 3 * mm * x * x))
    else:
        f1 = Decimal(1)
    f2 = r * (r ** (3 * mm + 1) / factorial(mm) - sum(r ** (3 * i) / factorial(i) for i in range(mm))) / (3 * r - 2)
    f3 = r ** (3 * mm + 3) / (factorial(mm) * (r * r + 3 * mm)) * (1 + sum(Decimal(j * factorial(mm) // factorial(mm - j)) * r ** (-3 * j - 2) for j in range(1, mm + 1)))
    return f1, f2, f3
ok = True
cms = {}
for mm in range(1, 21):
    f1, f2, f3 = cm_forms(mm)
    cms[mm] = f2
    if abs(f1 / f2 - 1) > Decimal('1e-60') or abs(f3 / f2 - 1) > Decimal('1e-60'):
        ok = False
report(ok, 'T5.1.3-cm-forms', 'c_m 三种闭式数值相等（1<=m<=20，相对差<1e-60）')
vals = ('%.10f' % cms[1], '%.10f' % cms[2], '%.9f' % cms[3])
report(vals == ('2.2096081318', '7.8411192294', '28.976857317'), 'T5.1.3-c123', 'c_1,c_2,c_3 = %s（报告 2.2096081318, 7.8411192294, 28.976857317）' % (vals,))
r1 = Cub([0, 1], 1)
report(gamma1(1) == Cub([Fraction(10, 31), Fraction(15, 31), Fraction(17, 31)], 1), 'T5.1.3-c1-Qrho', 'c_1=γ_1(ρ_1)=(10+15ρ+17ρ^2)/31 在 Q(ρ) 中精确成立')
# c_m 与 DP 渐近比较：U_k(m)/ρ^k
TK = core.U_fast_table(1500, 8)
ok = True
for mm in range(1, 9):
    est = Decimal(TK[1500][mm]) / R[mm] ** 1500
    if abs(est / cms[mm] - 1) > Decimal('1e-20'):
        ok = False
report(ok, 'T5.1.3-cm-vs-DP', 'U_1500(m)/ρ_m^1500 与 c_m 相对差 <1e-20（1<=m<=8）')
# (4) 整数 ρ：m=ρ^2(ρ-1)
def gamma_rat(mm, r):
    return Fraction(r) * (Fraction(r ** (3 * mm + 1), factorial(mm)) - sum(Fraction(r ** (3 * i), factorial(i)) for i in range(mm))) / (3 * r - 2)
c4 = gamma_rat(4, 2)
c18 = gamma_rat(18, 3)
report(c4 == Fraction(215, 2) and c18 == Fraction(37105325714711350249401, 6830759936000), 'T5.1.4-c4-c18', 'c_4=%s, c_18=%s' % (c4, c18))
ints = [mm for mm in range(0, 200) if any(y ** 3 - y ** 2 == mm for y in range(1, 10))]
report(ints == [0, 4, 18, 48, 100, 180], 'T5.1.4-int', 'ρ_m 为整数的 m<200：%s（报告 0,4,18,48,…）' % ints)
# 用定义 DP 独立确认 c_4、c_18（大 k）
getcontext().prec = 120
col4 = core.U_fast_column(4, 3000)
col18 = core.U_fast_column(18, 9000)
e4 = Decimal(col4[3000]) / Decimal(2) ** 3000
e18 = Decimal(col18[9000]) / Decimal(3) ** 9000
d4 = abs(e4 - Decimal(215) / 2)
d18 = abs(e18 / (Decimal(c18.numerator) / Decimal(c18.denominator)) - 1)
report(d4 < Decimal('1e-60') and d18 < Decimal('1e-40'), 'T5.1.4-c4-c18-DP', 'U_3000(4)/2^3000 - 215/2 = %.2e；U_9000(18)/3^9000 / c_18 - 1 = %.2e' % (d4, d18))
getcontext().prec = 80
# (2) τ_m、θ_m、复根模长
tau1 = (R[1] * (R[1] - 1)).sqrt()
report(abs(tau1 - Decimal('0.826')) < Decimal('0.0005'), 'T5.1.2-tau1', 'τ_1=√(ρ_1(ρ_1-1))=%.6f（报告 ≈0.826）' % tau1)
ok = True
for mm in range(2, 41):
    sig2 = Decimal(mm) / R[mm]
    if not (sig2 < R[mm - 1] ** 2):
        ok = False
    tau = max(R[mm - 2], (R[mm] * (R[mm] - 1)).sqrt())
    if not tau < R[mm - 1]:
        ok = False
mods = [(Decimal(j) / R[j]).sqrt() for j in range(1, 41)]
ok = ok and all(mods[i + 1] > mods[i] for i in range(len(mods) - 1))
report(ok, 'T5.1.2-tau', '|σ_m|^2=m/ρ_m<ρ_{m-1}^2，τ_m<ρ_{m-1}，|σ_j| 关于 j 递增（m,j<=40）')
# 1-θ_m ~ 1/(3m)
getcontext().prec = 60
rr = {}
for mm in (10, 100, 1000, 10000, 100000):
    a, b = rho(mm, 60), rho(mm - 1, 60)
    rr[mm] = float(3 * mm * (1 - b / a))
report(abs(rr[100000] - 1) < 0.01 and abs(rr[10000] - 1) < abs(rr[100] - 1), 'T5.1.2-theta', '3m(1-θ_m) → 1：%s' % {k: round(v, 4) for k, v in rr.items()})
getcontext().prec = 80
# 主项+次项，误差 O(τ^k)
ok = True
msg = []
TK2 = core.U_fast_table(600, 6)
getcontext().prec = 450
R = {mm: rho(mm, 450) for mm in range(0, 41)}
cms = {mm: R[mm] * (R[mm] ** (3 * mm + 1) / factorial(mm) - sum(R[mm] ** (3 * i) / factorial(i) for i in range(mm))) / (3 * R[mm] - 2) for mm in range(1, 21)}
for mm in range(1, 7):
    cm, cm1 = cms[mm], (cms[mm - 1] if mm >= 2 else Decimal(1))
    tau = max(R[mm - 2] if mm >= 2 else Decimal(0), (R[mm] * (R[mm] - 1)).sqrt())
    ratios = []
    for k in (200, 400, 600):
        err = Decimal(TK2[k][mm]) - cm * R[mm] ** k + cm1 * R[mm - 1] ** (k + 3)
        ratios.append(abs(err) / tau ** k)
    msg.append('m=%d:%.3g/%.3g/%.3g' % (mm, ratios[0], ratios[1], ratios[2]))
    if not (ratios[2] < 10 * max(ratios[0], Decimal(1)) + 10):
        ok = False
report(ok, 'T5.1.2-second-term', '|U_k-c_mρ_m^k+c_{m-1}ρ_{m-1}^{k+3}|/τ_m^k 在 k=200,400,600 有界（450 位精度）：%s' % '; '.join(msg))
getcontext().prec = 80
R = {mm: rho(mm) for mm in range(0, 41)}
# (5) 提示词 k=40 的数值
out = []
TT40 = core.U_fast_table(41, 4)
for mm in (2, 3):
    U40, U41 = Decimal(TT40[40][mm]), Decimal(TT40[41][mm])
    adj = U41 / U40 / R[mm] - 1
    root = U40 ** (Decimal(1) / 40) / R[mm] - 1
    main = U40 / (cms[mm] * R[mm] ** 40) - 1
    th = R[mm - 1] / R[mm]
    kappa = cms[mm - 1] * R[mm - 1] ** 3 / cms[mm]
    theo = kappa * (1 - th) * th ** 40
    out.append((mm, float(adj), float(theo), float(theo / adj - 1), float(root), float(main)))
print('INFO k=40：(m, U41/U40/ρ-1, κ(1-θ)θ^40, 理论/实测-1, U40^(1/40)/ρ-1, U40/(c ρ^40)-1) = ')
for o in out:
    print('   m=%d: %.4e, %.4e, %.3f, %.4f, %.4f' % o[:1 + 5])
ok = (abs(out[0][1] - 3.5e-4) < 0.05e-4 and abs(out[1][1] - 2.8e-3) < 0.05e-3
      and abs(abs(out[0][4]) - 0.053) < 0.001 and abs(abs(out[1][4]) - 0.087) < 0.001
      and abs(abs(out[0][5]) - 0.0026) < 0.0001 and abs(abs(out[1][5]) - 0.030) < 0.001
      and abs(abs(out[0][3]) - 0.003) < 0.002 and abs(abs(out[1][3]) - 0.03) < 0.01)
report(ok, 'T5.1.5-prompt-k40', 'm=2,3：相邻比 0.035%%/0.28%%、理论吻合 0.3%%/3%%、U^(1/40) 5.3%%/8.7%%、U/(cρ^40) 0.26%%/3.0%%（实算见 INFO）')

# ---------------- T5.2 ----------------
KP = 40
TP = lemma1_table(KP, KP + 2)
UP = {k: interp(list(range(k + 1)), [TP[k][m] for m in range(k + 1)]) for k in range(0, KP + 1)}
def coef(k, e):
    return UP[k][e] if 0 <= e < len(UP[k]) else Fraction(0)
f1 = lambda k: Fraction(2, factorial(k))
f2 = lambda k: Fraction(k * k - 2 * k - 1, factorial(k - 1))
f3 = lambda k: Fraction(3 * k ** 4 - 36 * k ** 3 + 162 * k ** 2 - 313 * k + 422, 12 * factorial(k - 2))
f4 = lambda k: Fraction(k ** 6 - 30 * k ** 5 + 379 * k ** 4 - 2533 * k ** 3 + 9570 * k ** 2 - 19331 * k + 13380, 24 * factorial(k - 3))
res = {}
for d, f, thr in ((0, f1, 2), (1, f2, 4), (2, f3, 6), (3, f4, 8)):
    good_all = all(coef(k, k - d) == f(k) for k in range(thr, KP + 1))
    fail_below = coef(thr - 1, thr - 1 - d) != f(thr - 1) if thr - 1 - d >= 0 else True
    res[d] = (good_all, fail_below)
report(all(v[0] for v in res.values()), 'T5.2.formulas', '[m^k],[m^{k-1}],[m^{k-2}],[m^{k-3}] 的四个公式在各自门槛以上成立（k<=40）')
report(all(v[1] for v in res.values()), 'T5.2.thresholds', '门槛精确：d=0..3 在 k=2d+1 处公式失效 %s' % {d: v[1] for d, v in res.items()})
report(coef(3, 2) == 2 and f2(3) == 1, 'T5.2.k3', '[m^2]U_3=%s（报告 2），公式给 %s（报告 1）' % (coef(3, 2), f2(3)))
# B_d(k) 一般式
NTP = N_table_from_U(TP, KP)
def etil(jj, nn):
    # e_j(-1,0,...,n-2)/n^(j下降)
    vals = list(range(-1, nn - 1))
    e = [Fraction(1)] + [Fraction(0)] * jj
    for v in vals:
        for t in range(jj, 0, -1):
            e[t] += v * e[t - 1]
    return e[jj] / falling(nn, jj) if falling(nn, jj) != 0 else None
ok = True
for k in range(2, KP + 1):
    for d in range(0, min(k, 10)):
        B = factorial(k - d) * coef(k, k - d)
        s = Fraction(0)
        for e_ in range(0, d + 1):
            et = etil(d - e_, k - e_)
            s += (-1) ** (d - e_) * NTP[k][k - e_] * et
        if B != s:
            ok = False
report(ok, 'T5.2.Bd', 'B_d(k)=(k-d)![m^{k-d}]U_k=sum_e(-1)^{d-e}N(k,k-e)ẽ_{d-e}(k-e)，2<=k<=40, d<10')
ok = True
for d in range(0, 8):
    pts = [(k, factorial(k - d) * coef(k, k - d)) for k in range(2 * d + 2, 4 * d + 3)]
    pB = interp([p[0] for p in pts], [p[1] for p in pts])
    if pdeg(pB) != 2 * d and d > 0:
        ok = False
    if not all(peval(pB, k) == factorial(k - d) * coef(k, k - d) for k in range(2 * d + 2, KP + 1)):
        ok = False
    if factorial(2 * d + 1 - d) * coef(2 * d + 1, d + 1) == peval(pB, 2 * d + 1):
        ok = False
report(ok, 'T5.2.Bd-poly', 'B_d(k) 在 k>=2d+2 为 2d 次多项式、k=2d+1 处失效（d<=7）')
mu_ok = all(Fraction(2, factorial(k)) * k * Fraction(k * k - 2 * k - 1, 2) == f2(k) for k in range(2, 40))
report(mu_ok, 'T5.2.mu', '(2/k!)(m+μ_k)^k 的 m^{k-1} 系数 = [m^{k-1}]U_k，μ_k=(k^2-2k-1)/2')

# ---------------- T5.3 ----------------
KH = 60
TH = lemma1_table(KH, KH + 1)
def hpoly(k):
    return trim([sum((-1) ** (i - j) * comb(k + 1, i - j) * TH[k][j] for j in range(0, i + 1)) for i in range(0, k + 1)])
HP = {k: hpoly(k) for k in range(0, KH + 1)}
NTH = N_table_from_U(TH, KH)
ok = all(HP[k][0] == 1 for k in range(KH + 1)) and all(peval(HP[k], 1) == 2 for k in range(2, KH + 1))
t1 = [HP[k][1] if len(HP[k]) > 1 else 0 for k in range(KH + 1)]
ok_t1 = all(t1[k] == TH[k][1] - k - 1 for k in range(KH + 1)) and all(t1[k] > 0 for k in range(2, KH + 1)) and t1[0] == 0 and t1[1] == 0
gf = series_of_rational([0, 0, 1, -1, 1], pmul(ppow([1, -1], 2), [1, -1, 0, -1]), KH + 1)
report(ok and ok_t1 and gf == t1, 'T5.3.1-basic', 'h_k(0)=1、h_k(1)=2(k>=2)、[t^1]h_k=R_k-k-1（k>=2 时 >0；k=0,1 为 0）、g.f. x^2(1-x+x^2)/((1-x)^2(1-x-x^3))，k<=60')
ok = True
for k in range(1, KH + 1):
    for d in range(0, 6):
        val = peval(HP[k], 1) if d == 0 else None
        # 第 d 阶导数在 1 处
        p = HP[k]
        for _ in range(d):
            p = pderiv(p)
        lhs = peval(p, 1) if p else 0
        rhs = factorial(d) * sum((-1) ** e_ * C(k - 1 - e_, d - e_) * (NTH[k][k - e_] if k - e_ >= 0 else 0) for e_ in range(0, d + 1))
        if lhs != rhs:
            ok = False
report(ok, 'T5.3.1-deriv', 'h_k^{(d)}(1)=d! sum_{e<=d}(-1)^e C(k-1-e,d-e)N(k,k-e)，1<=k<=60, d<=5')
hp1 = [peval(pderiv(HP[k]), 1) if len(HP[k]) > 1 else 0 for k in range(KH + 1)]
report(all(hp1[k] == -(k * k - 3 * k - 2) for k in range(4, KH + 1)), 'T5.3.1-h1', "h_k'(1)=-(k^2-3k-2)（4<=k<=60）；k=2,3 实为 %s,%s（公式 %s,%s）" % (hp1[2], hp1[3], -(4 - 6 - 2), -(9 - 9 - 2)))
ok = True
for k in range(1, 31):
    # (1+z)^{k-1} h_k(z/(1+z)) = sum_q N(k,q) z^{q-1}
    acc = []
    for i, c in enumerate(HP[k]):
        acc = padd(acc, pscale(pmul(pshift([1], i), ppow([1, 1], k - 1 - i)), c))
    want = trim([NTH[k][q] for q in range(1, k + 1)])
    if trim(acc) != want:
        ok = False
report(ok, 'T5.3.1-nk', 'n_k(z)=(1+z)^{k-1}h_k(z/(1+z))=sum_q N(k,q)z^{q-1}，k<=30')
# (2) 负整数处
GN = {1: [1]}
for j in range(1, 25):
    GN[j + 1] = padd(pmul([1, -1, 0, j], GN[j]), [0, 0, j])
ok = all(pdeg(GN[j]) == 3 * j - 3 for j in range(1, 26))
UPH = {k: interp(list(range(k + 1)), [TH[k][m] for m in range(k + 1)]) for k in range(0, 41)}
ok2 = all(peval(UPH[k], -j) == (GN[j][k] if k < len(GN[j]) else 0) for j in range(1, 22) for k in range(0, 41))
report(ok and ok2, 'T5.3.2-Gneg', 'G_{-j}=sum_k U_k(-j)x^k 是 3j-3 次多项式，G_{-j-1}=(1-x+jx^3)G_{-j}+jx^2，与插值多项式 u_k(-j) 一致（j<=21,k<=40）')
ok = True
for k in range(1, 41):
    sk = (k + 2) // 3
    if not all(peval(UPH[k], -j) == 0 for j in range(1, sk + 1)) or peval(UPH[k], -sk - 1) == 0:
        ok = False
    prod_ = [1]
    for j in range(1, sk + 1):
        prod_ = pmul(prod_, [j, 1])
    _, r = pdivmod(UPH[k], prod_)
    if r:
        ok = False
report(ok and all(peval(UPH[3 * j], -j - 1) == factorial(j) for j in range(1, 14)), 'T5.3.2-zeros', 'U_k(-j)=0 (1<=j<=floor((k+2)/3))、U_k(-s_k-1)≠0、(m+1)…(m+s_k)|U_k、U_{3j}(-j-1)=j!（k<=40）')
# 其他负整数零点：整数根 r 满足 |r| <= 1 + max|a_i/a_n|（Cauchy 界）
ok = True
bmax = 0
for k in range(1, 41):
    p = UPH[k]
    n_ = len(p) - 1
    # Fujiwara 界：2*max_i |a_{n-i}/a_n|^{1/i}
    bound = 2 * max(float(abs(p[n_ - i] / p[n_])) ** (1.0 / i) for i in range(1, n_ + 1)) if n_ >= 1 else 1
    bmax = max(bmax, bound)
    sk = (k + 2) // 3
    for j in range(sk + 1, int(bound) + 2):
        if peval(p, -j) == 0:
            ok = False
report(ok, 'T5.3.2-noother', 'U_k 在 -(s_k+1) 至 -(Fujiwara 界) 之间无整数零点（1<=k<=40；最大界 %.1f）' % bmax)
# (3) deg h_k 与首项
ok = True
for k in range(0, KH + 1):
    a, r = divmod(k, 3)
    lead = HP[k][-1]
    want = (-1) ** a * (factorial(a) if r == 0 else (stirling1u(a + 2, 2) if r == 1 else factorial(a + 1)))
    if pdeg(HP[k]) != (2 * k) // 3 or lead != want:
        ok = False
report(ok, 'T5.3.3-deg-lead', 'deg h_k=floor(2k/3)，首项 (-1)^a a! / (-1)^a c(a+2,2) / (-1)^a (a+1)!（k=3a,3a+1,3a+2；k<=60）')
# (4) Möbius：按偏序集直接计算
from itertools import product as iprod
def mobius_poset(k):
    rows = [r for r in iprod((0, 1), repeat=k) if core.row_ok(r)]
    leq = lambda a, b: all(x <= y for x, y in zip(a, b))
    bot, top = tuple([0] * k), tuple([1] * k)
    order = sorted(rows, key=sum)
    mu = {}
    for r in order:
        if not leq(bot, r):
            continue
        if r == bot:
            mu[r] = 1
        else:
            mu[r] = -sum(mu[s] for s in order if s in mu and s != r and leq(s, r))
    return mu[top]
mob = [mobius_poset(k) for k in range(1, 10)]
alt = [sum((-1) ** q * NTH[k][q] for q in range(0, k + 1)) for k in range(1, 10)]
u2 = [peval(UPH[k], -2) for k in range(1, 10)]
report(mob == alt == u2 and mob[:3] == [-1, 1, 1] and all(v == 0 for v in mob[3:]), 'T5.3.4-mobius', 'μ(0̂,1̂)（偏序集直接计算）=sum_q(-1)^qN(k,q)=U_k(-2)：%s（k=1..9）' % mob)
ok = True
for k in range(1, KH + 1):
    nk = trim([NTH[k][q] for q in range(1, k + 1)])
    mult = 0
    p = nk
    while p and peval(p, -1) == 0:
        p, r = pdivmod(p, [1, 1])
        mult += 1
    if mult != ceil(k / 3) - 1:
        ok = False
report(ok, 'T5.3.4-nk-root', 'n_k(z) 在 z=-1 的根重数 = ceil(k/3)-1（1<=k<=60）')
# (5)/(6)：Sturm 计数
def sturm_count(p, a, b):
    seq = [p, pderiv(p)]
    while seq[-1] and pdeg(seq[-1]) > 0:
        _, r = pdivmod(seq[-2], seq[-1])
        seq.append(pscale(r, -1))
    seq = [s for s in seq if s]
    def var(x):
        vals = [peval(s, x) for s in seq]
        vals = [v for v in vals if v != 0]
        return sum(1 for i in range(len(vals) - 1) if (vals[i] > 0) != (vals[i + 1] > 0))
    return var(a) - var(b)
ok01 = all(sturm_count([Fraction(c) for c in HP[k]], Fraction(0), Fraction(1)) == 0 for k in range(2, 31))
big = Fraction(10 ** 6)
okreal = all(sturm_count([Fraction(c) for c in HP[k]], -big, big) == pdeg(HP[k]) for k in range(2, 31))
report(ok01, 'T5.3.5-no01', 'h_k 在 [0,1] 上无根（Sturm，2<=k<=30）')
report(okreal, 'T5.3.6-real', 'h_k 的根全为实且两两不同（Sturm 计数=次数，2<=k<=30；报告猜想 k<=60）')
# 固定位置系数转正门槛
TH2 = lemma1_table(170, 12)
thr = []
for i in range(1, 9):
    vals = [sum((-1) ** (i - j) * comb(k + 1, i - j) * TH2[k][j] for j in range(0, i + 1)) for k in range(0, 171)]
    last_nonpos = max([k for k in range(0, 171) if vals[k] <= 0 and k >= i], default=None)
    thr.append(None if last_nonpos is None else last_nonpos + 1)
report(thr == [2, 8, 16, 24, 33, 41, 50, 59], 'T5.3.thresholds', '固定位置 i=1..8 的 h_{k,i} 自 k=K_i 起恒正（k<=170 内）：K_i=%s（④.6：2,8,16,24,33,41,50,59）' % thr)

# ---------------- T5.4 ----------------
DATA = os.path.join(ROOT, 'data', 'oeis')
def bfile(name):
    out = {}
    with open(os.path.join(DATA, name), encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            a, b = line.split()[:2]
            out[int(a)] = int(b)
    return out
Rk = [TH[k][1] if k <= KH else None for k in range(0, KH + 1)]
b718 = bfile('b038718.txt')
ok = all(Rk[k] == b718[k + 2] for k in range(0, KH - 1))
ser1 = series_of_rational([1, -1, 1], pmul([1, -1], [1, -1, 0, -1]), 30)
ser2 = series_of_rational([1, 0, 1, -1], pmul([1, -1], [1, -1, 0, -1]), 30)
okg = ser1 == [1] + Rk[:29] and ser2 == Rk[:30] and ser1[1] == 1 and Rk[1] == 2
report(ok and okg, 'T5.4.3-R', 'R_k=A038718(k+2)（b 文件，k<=58）；(1-x+x^2)/((1-x)(1-x-x^3))=1+x·ΣR_kx^k，ΣR_kx^k=(1+x^2-x^3)/((1-x)(1-x-x^3))')
b990 = bfile('b084990.txt')
ok = all(TH[3][m] == Fraction((m + 1) * (m * m + 5 * m + 3), 3) == 2 * comb(m + 3, 3) - (m + 1) == b990[m + 1] for m in range(0, 61))
mono4 = sum(1 for t in iprod(range(2), repeat=4) if all(t[i] <= t[i + 1] for i in range(3)) or all(t[i] >= t[i + 1] for i in range(3)))
report(ok and mono4 == 8 and TH[4][1] == 9, 'T5.4.4-U3', 'U_3(m)=(m+1)(m^2+5m+3)/3=2C(m+3,3)-(m+1)=A084990(m+1)（m<=60）；[2]^4 单调 4 元组=%d≠U_4(1)=9' % mono4)
b247 = bfile('b326247.txt')
ok = all(TH[4][m] == Fraction((m + 1) * (m + 2) * (m * m + 11 * m + 6), 12) == comb(m + 2, 2) ** 2 - 4 * comb(m + 2, 4) == b247[m + 2] for m in range(0, 39))
# A326247 n=3：2-子集有序对，既不交叉也不嵌套
def cross_or_nest(e, f):
    (a, b), (c, d) = sorted(e), sorted(f)
    if (a, b) == (c, d):
        return False
    if a > c or (a == c and b > d):
        (a, b), (c, d) = (c, d), (a, b)
    return (a < c < b < d) or (a < c < d < b)
from itertools import combinations
edges = list(combinations(range(1, 4), 2))
ordered = sum(1 for e in edges for f in edges if not cross_or_nest(e, f))
unordered = sum(1 for i, e in enumerate(edges) for f in edges[i:] if not cross_or_nest(e, f))
report(ok and ordered == 9 and unordered == 6, 'T5.4.5-U4', 'U_4(m)=(m+1)(m+2)(m^2+11m+6)/12=C(m+2,2)^2-4C(m+2,4)=A326247(m+2)（m<=38）；n=3 有序对 %d、无序 %d' % (ordered, unordered))
# c_2, c_3 与 A077949/A084386（快照）
def snap_terms(fname, anum):
    terms = []
    with open(os.path.join(DATA, fname), encoding='utf-8') as f:
        for line in f:
            if line[:3] in ('%S ', '%T ', '%U ') and line.split()[1] == anum:
                terms += [int(v) for v in line.split()[2].strip(',').split(',') if v]
    return terms
t2 = snap_terms('search_c2.txt', 'A077949')
t3 = snap_terms('search_c3.txt', 'A084386')
report(t2 == c_seq(2, len(t2) - 1) and t3 == c_seq(3, len(t3) - 1), 'T5.4.6-c2c3', 'c_2=A077949（%d 项）、c_3=A084386（%d 项）与快照一致' % (len(t2), len(t3)))
# 家族数据：A207118..A207122 列 k=3..7；A207117 对角；A207124..A207127 行 n=4..7；A207123 反对角
TBig = lemma1_table(12, 110)
def a_kn(k, nn):
    return TBig[k][(nn + 1) // 2] * TBig[k][nn // 2]
ok = True
for k, an in zip(range(3, 8), ('207118', '207119', '207120', '207121', '207122')):
    bf = bfile('b%s.txt' % an)
    if not all(bf[nn] == a_kn(k, nn) for nn in bf):
        ok = False
TD = lemma1_table(215, 110)
bf = bfile('b207117.txt')
if not all(bf[nn] == TD[nn][(nn + 1) // 2] * TD[nn][nn // 2] for nn in bf):
    ok = False
for nn, an in zip(range(4, 8), ('207124', '207125', '207126', '207127')):
    bf = bfile('b%s.txt' % an)
    if not all(bf[kk] == TD[kk][(nn + 1) // 2] * TD[kk][nn // 2] for kk in bf):
        ok = False
bf = bfile('b207123.txt')
seq = []
d = 2
while len(seq) < len(bf):
    for nn in range(1, d):
        kk = d - nn
        seq.append(TD[kk][(nn + 1) // 2] * TD[kk][nn // 2])
    d += 1
if not all(bf[i + 1] == seq[i] for i in range(len(bf))):
    ok = False
report(ok, 'T5.4.1-data', 'b 文件：A207118–A207122（列 k=3..7）、A207117（对角）、A207124–A207127（行 n=4..7）、A207123（%d 项，按反对角）全部 = U_k(ceil n/2)U_k(floor n/2)' % len(bf))

summary('audit_c5')
print('elapsed %.1fs' % (time.time() - t0))
