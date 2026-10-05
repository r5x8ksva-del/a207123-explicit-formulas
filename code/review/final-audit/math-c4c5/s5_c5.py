# -*- coding: utf-8 -*-
"""C-5（T5.1–T5.4）数字核对（final-audit math-c4c5）。U 取自 core.U_fast_table（原始定义的高度 DP），并与自写字面 DP 抽查一致。"""
import os
import re
import time
from decimal import Decimal, getcontext
from fractions import Fraction
from math import comb, factorial
from itertools import product

import numpy as np

from alib import (say, check, U_col, ptrim, padd, pmul, pscale, peval, pdivmod, interp_newton,
                  stirling1_unsigned, ROOT, write_log)
from core import U_fast_table

t0 = time.time()
F = Fraction
getcontext().prec = 120

KT, MT = 45, 33
T = U_fast_table(KT, MT)                      # T[k][m]
ok = all(U_col(m, 20)[k] == T[k][m] for m in range(9) for k in range(21))
check('base.U', ok, 'core.U_fast_table == 自写字面 DP（k<=20, m<=8）')


def U(k, m):
    return T[k][m]


# ---------------------------------------------------------------- ρ_m、c_m
def rho(m):
    if m == 0:
        return Decimal(1)
    x = Decimal(2)
    for _ in range(200):
        fx = x ** 3 - x ** 2 - m
        x2 = x - fx / (3 * x * x - 2 * x)
        if abs(x2 - x) < Decimal(10) ** -110:
            x = x2
            break
        x = x2
    return x


R = {m: rho(m) for m in range(0, 61)}


def b(i):
    return ptrim([1, -1, 0, -i])


def Ppoly(m):
    p = [1]
    for i in range(m + 1):
        p = pmul(p, b(i))
    return p


def Wpoly(m):
    w = [1]
    for j in range(1, m + 1):
        w = padd(w, [0, 0] + pscale(Ppoly(j - 1), j))
    return w


def dev(p, x):
    r = Decimal(0)
    for a in reversed(p):
        r = r * x + Decimal(a.numerator) / Decimal(a.denominator) if isinstance(a, Fraction) else r * x + Decimal(a)
    return r


def c_form1(m):
    x = 1 / R[m]
    G = dev(Wpoly(m - 1), x) / dev(Ppoly(m - 1), x)
    return (G + m * x * x) / (x * (1 + 3 * m * x * x))


def c_form2(m):
    r = R[m]
    s = sum(r ** (3 * i) / factorial(i) for i in range(m))
    return r * (r ** (3 * m + 1) / factorial(m) - s) / (3 * r - 2)


def c_form3(m):
    r = R[m]
    s = 1 + sum(j * Decimal(factorial(m) // factorial(m - j)) * r ** (-3 * j - 2) for j in range(1, m + 1))
    return r ** (3 * m + 3) / (factorial(m) * (r * r + 3 * m)) * s


C = {0: Decimal(1)}
bad = []
for m in range(1, 21):
    a1, a2, a3 = c_form1(m), c_form2(m), c_form3(m)
    if abs(a1 - a2) > Decimal(10) ** -90 * a2 or abs(a3 - a2) > Decimal(10) ** -90 * a2:
        bad.append(m)
    C[m] = a2
check('T5.1.3-cm-forms', not bad, 'c_m 三种闭式（G_{m-1} 式、ρ(ρ^{3m+1}/m!-Σ)/(3ρ-2)、ρ^{3m+3}/(m!(ρ^2+3m))(1+Σ j m!/(m-j)! ρ^{-3j-2})）相对差 <1e-90（1<=m<=20）; bad=%s' % bad)
s123 = (format(C[1], '.10f'), format(C[2], '.10f'), format(C[3], '.9f'))
check('T5.1.3-c123', s123 == ('2.2096081318', '7.8411192294', '28.976857317'), 'c_1,c_2,c_3 舍入 = %s' % (s123,))
r1 = R[1]
check('T5.1.3-c1', abs((10 + 15 * r1 + 17 * r1 * r1) / 31 - C[1]) < Decimal(10) ** -100, 'c_1=(10+15ρ+17ρ^2)/31（数值 1e-100）')

# c_4、c_18 精确
def c_exact(m, r):
    s = sum(F(r ** (3 * i), factorial(i)) for i in range(m))
    return F(r) * (F(r ** (3 * m + 1), factorial(m)) - s) / (3 * r - 2)


c4e, c18e = c_exact(4, 2), c_exact(18, 3)
okint = [m for m in range(0, 2000) if any(r * r * (r - 1) == m for r in range(1, 14))]
check('T5.1.4-c4-c18', c4e == F(215, 2) and c18e == F(37105325714711350249401, 6830759936000)
      and R[4] == 2 and abs(R[18] - 3) < Decimal(10) ** -100 and abs(C[4] - Decimal(215) / 2) < Decimal(10) ** -90,
      'c_4=%s，c_18=%s（ρ=2,3 精确代入第二式）；ρ_m 为整数的 m<2000: %s' % (c4e, c18e, okint))

# γ_j 两式在 Q[y]/(f_j) 中相等：y·(y^{3j+1}/j!-e_{j-1}(y^3))·y^2 ≡ y^{3j+3}/j!+Σ(j-i)y^{3i+1}/i!，且 y^2+3j ≡ y^2(3y-2)
bad = []
for j in range(1, 25):
    f = [F(-j), F(0), F(-1), F(1)]
    lhs = [0] * (3 * j + 5)
    lhs[3 * j + 4] = F(1, factorial(j))
    for i in range(j):
        lhs[3 * i + 3] -= F(1, factorial(i))
    rhs = [0] * (3 * j + 4)
    rhs[3 * j + 3] = F(1, factorial(j))
    for i in range(j):
        rhs[3 * i + 1] += F(j - i, factorial(i))
    d1 = pdivmod(padd(lhs, pscale(rhs, -1)), f)[1]
    d2 = pdivmod(padd([3 * j, 0, 1], pscale([0, 0, -2, 3], -1)), f)[1]
    if d1 or d2:
        bad.append(j)
check('T5.1.1-gamma-forms', not bad, 'γ_j 的两种写法在 Q[y]/(y^3-y^2-j) 中相等（1<=j<=24，含 j=4,18）; bad=%s' % bad)

# Binet 型公式：numpy 求根 + γ 第一式，m<=6，k<=30
bad = []
maxrel = 0.0
for m in range(0, 7):
    for k in range(0, 31):
        tot = 0j
        for j in range(0, m + 1):
            pre = (-1) ** (m - j) / factorial(m - j)
            if j == 0:
                roots = [1.0 + 0j]
            else:
                roots = np.roots([1, -1, 0, -j])
            for s in roots:
                s = complex(s)
                if j == 0:
                    gam = 1.0
                else:
                    gam = s * (s ** (3 * j + 1) / factorial(j) - sum(s ** (3 * i) / factorial(i) for i in range(j))) / (3 * s - 2)
                tot += pre * gam * s ** (k + 3 * (m - j))
        true = U(k, m)
        rel = abs(tot - true) / max(1, true)
        maxrel = max(maxrel, rel)
        if rel > 1e-7:
            bad.append((m, k))
check('T5.1.1-binet', not bad, 'Binet 型公式（γ_j 用第一式，numpy 求根，双精度）与 DP 相符，0<=m<=6, 0<=k<=30，最大相对误差 %.2e; bad=%s' % (maxrel, bad[:4]))

# 关键不等式 & τ_m < ρ_{m-1}
bad = []
for m in range(1, 60):
    sig2 = m / R[m]
    if not (sig2 < R[m - 1] ** 2):
        bad.append(('key', m))
    A_ = R[m] * R[m - 1] ** 2 > R[m - 1] ** 3
    B_ = abs(R[m - 1] ** 3 - R[m - 1] ** 2 - (m - 1)) < Decimal(10) ** -100
    C_ = R[m - 1] ** 2 + (m - 1) >= m
    if not (A_ and B_ and C_):
        bad.append(('chain', m))
    if m >= 2:
        tau = max(R[m - 2], (R[m] * (R[m] - 1)).sqrt())
        if not tau < R[m - 1]:
            bad.append(('tau', m))
    # |σ|^2 = m/ρ = ρ(ρ-1)
    if abs(sig2 - R[m] * (R[m] - 1)) > Decimal(10) ** -100:
        bad.append(('sig', m))
incr = all(R[j] * (R[j] - 1) < R[j + 1] * (R[j + 1] - 1) for j in range(1, 59))
# numpy 检查复根模长
for m in range(1, 30):
    rts = np.roots([1, -1, 0, -m])
    cr = [r for r in rts if abs(r.imag) > 1e-9]
    if abs(abs(cr[0]) ** 2 - m / float(R[m])) > 1e-9:
        bad.append(('np', m))
tau1 = (R[1] * (R[1] - 1)).sqrt()
check('T5.1.2-key', not bad and incr, '|σ_m|^2=m/ρ_m=ρ_m(ρ_m-1)<ρ_{m-1}^2、τ_m<ρ_{m-1}、|σ_j| 递增（m<60）；τ_1=%s; bad=%s' % (format(tau1, '.4f'), bad[:4]))

# κ_m 与误差率：e_k=U_k/(c ρ^k)-1 ≈ -κ θ^k
UB = {m: U_col(m, 3) for m in range(0)}   # 占位
from core import U_fast_column
bad = []
info = []
for m in range(1, 6):
    col = U_fast_column(m, 420)
    kap = C[m - 1] * R[m - 1] ** 3 / C[m]
    th = R[m - 1] / R[m]
    for k in (300, 400):
        ek = Decimal(col[k]) / (C[m] * R[m] ** k) - 1
        ratio = ek / (-kap * th ** k)
        info.append((m, k, float(ratio)))
        if not (ek < 0 and abs(ratio - 1) < Decimal('1e-4')):
            bad.append((m, k))
check('T5.1.2-kappa', not bad, 'e_k/(−κ_mθ_m^k) → 1（κ_m=c_{m-1}ρ_{m-1}^3/c_m，θ_m=ρ_{m-1}/ρ_m），m=1..5，k=300/400：%s' % [(a, b_, round(c, 6)) for a, b_, c in info])

# (5) 百分比
res = {}
for m in (2, 3):
    col = U_fast_column(m, 41)
    adj = Decimal(col[41]) / Decimal(col[40]) / R[m] - 1
    th = R[m - 1] / R[m]
    kap = C[m - 1] * R[m - 1] ** 3 / C[m]
    theo = kap * (1 - th) * th ** 40
    root = Decimal(col[40]) ** (Decimal(1) / 40) / R[m] - 1
    lead = Decimal(col[40]) / (C[m] * R[m] ** 40) - 1
    res[m] = (adj, theo, adj / theo - 1, root, lead)
    say('INFO m=%d: U41/U40/ρ-1=%.4e  κ(1-θ)θ^40=%.4e  实测/理论-1=%.4f  U40^(1/40)/ρ-1=%.4e  U40/(cρ^40)-1=%.4e' % ((m,) + tuple(float(v) for v in res[m])))
ok = (round(float(res[2][0]) * 100, 3) == 0.035 and round(float(res[3][0]) * 100, 2) == 0.28
      and abs(float(res[2][2])) < 0.0035 and abs(float(res[3][2])) < 0.035
      and round(float(res[2][3]) * 100, 1) == 5.3 and round(float(res[3][3]) * 100, 1) == 8.7
      and round(abs(float(res[2][4])) * 100, 2) == 0.26 and round(abs(float(res[3][4])) * 100, 1) == 3.0)
check('T5.1.5-k40', ok, '相邻比 0.035%%/0.28%%，与理论吻合到 0.3%%/3%%；U^(1/40) 5.3%%/8.7%%；U/(cρ^40) 0.26%%/3.0%%')

# ---------------------------------------------------------------- T5.2：m 的高次系数
def Upoly(k):
    xs = list(range(0, k + 2))
    return interp_newton(xs, [U(k, m) for m in xs])


UP = {k: Upoly(k) for k in range(0, 31)}
forms = {
    0: lambda k: F(2, factorial(k)),
    1: lambda k: F(k * k - 2 * k - 1, factorial(k - 1)),
    2: lambda k: F(3 * k ** 4 - 36 * k ** 3 + 162 * k * k - 313 * k + 422, 12 * factorial(k - 2)),
    3: lambda k: F(k ** 6 - 30 * k ** 5 + 379 * k ** 4 - 2533 * k ** 3 + 9570 * k * k - 19331 * k + 13380, 24 * factorial(k - 3)),
}
thr = {0: 2, 1: 4, 2: 6, 3: 8}
bad = []
for d in range(4):
    for k in range(max(d, 1), 31):
        coef = UP[k][k - d] if k - d < len(UP[k]) else 0
        if k >= thr[d] and coef != forms[d](k):
            bad.append((d, k))
        if k == thr[d] - 1 and coef == forms[d](k):
            bad.append(('thr', d, k))
k3 = (UP[3][2], forms[1](3))
check('T5.2-formulas', not bad and k3 == (2, 1), '[m^k],[m^{k-1}],[m^{k-2}],[m^{k-3}] 四式在各自门槛以上成立、门槛前一点失效（k<=30）；k=3: 实际 %s，公式 %s; bad=%s' % (k3[0], k3[1], bad[:4]))

# ---------------------------------------------------------------- T5.3
def hcoef(k):
    """h_{k,i}=Σ_j(-1)^{i-j}C(k+1,i-j)U_k(j)，i<=k+1。"""
    return ptrim([sum((-1) ** (i - j) * comb(k + 1, i - j) * U(k, j) for j in range(i + 1)) for i in range(k + 2)])


HK = {k: hcoef(k) for k in range(0, 31)}
Rk = [U(k, 1) for k in range(0, 31)]
t1 = [HK[k][1] if len(HK[k]) > 1 else 0 for k in range(31)]
ok1 = all(t1[k] == Rk[k] - k - 1 for k in range(31)) and t1[0] == 0 and t1[1] == 0 and all(t1[k] > 0 for k in range(2, 31))
# g.f. x^2(1-x+x^2)/((1-x)^2(1-x-x^3))
den = pmul(pmul([1, -1], [1, -1]), [1, -1, 0, -1])
num = [0, 0, 1, -1, 1]
ser = [0] * 31
# 级数除法
rem = [F(x) for x in num] + [F(0)] * 40
for n in range(31):
    ser[n] = rem[n]
    for i, dv in enumerate(den):
        if i and n + i < len(rem):
            rem[n + i] -= ser[n] * dv
ok2 = ser == [F(x) for x in t1]
ok3 = all(peval(HK[k], 0) == 1 for k in range(31)) and all(peval(HK[k], 1) == 2 for k in range(2, 31))
c1s = stirling1_unsigned(40)
N_ = {}


def Nkq(k, q):
    s = 0
    for i in range(q + 1):
        u = (1 if k == 0 else 0) if i == 0 else U(k, i - 1)
        s += (-1) ** (q - i) * comb(q, i) * u
    return s


def hderiv1(k, dd):
    p = HK[k]
    for _ in range(dd):
        p = ptrim([i * p[i] for i in range(1, len(p))])
    return peval(p, 1)


ok4 = all(hderiv1(k, dd) == factorial(dd) * sum((-1) ** e * (comb(k - 1 - e, dd - e) if k - 1 - e >= 0 else 0) * Nkq(k, k - e) for e in range(dd + 1))
          for k in range(1, 31) for dd in range(0, 4))
ok5 = all(hderiv1(k, 1) == -(k * k - 3 * k - 2) for k in range(4, 31)) and hderiv1(3, 1) != -(9 - 9 - 2)
check('T5.3.1-basic', ok1 and ok2 and ok3 and ok4 and ok5,
      '[t^1]h_k=R_k-k-1（k<=30；k=0,1 为 0，k>=2 为正）、其 g.f.=x^2(1-x+x^2)/((1-x)^2(1-x-x^3))、h_k(0)=1、h_k(1)=2（k>=2）、h_k^{(d)}(1) 公式（d<=3）、h_k\'(1)=-(k^2-3k-2)（k>=4）')

bad = []
for k in range(0, 31):
    p = HK[k]
    deg = len(p) - 1
    a, r = divmod(k, 3)
    want = [(-1) ** a * factorial(a), (-1) ** a * c1s[a + 2][2], (-1) ** a * factorial(a + 1)][r]
    if deg != (2 * k) // 3 or p[-1] != want:
        bad.append((k, deg, p[-1], want))
check('T5.3.3-deg-lead', not bad, 'deg h_k=floor(2k/3)，首项 (-1)^a a! / (-1)^a c(a+2,2) / (-1)^a (a+1)!（k=3a,3a+1,3a+2；0<=k<=30）; bad=%s' % bad[:3])

# T5.3(2)：负整数处的值
bad = []
for k in range(1, 31):
    s = (k + 2) // 3
    for j in range(1, s + 2):
        v = peval(UP[k], -j)
        if j <= s and v != 0:
            bad.append((k, j))
        if j == s + 1 and v == 0:
            bad.append(('nz', k))
ok = not bad and all(peval(UP[3 * j], -j - 1) == factorial(j) for j in range(1, 11))
# G_{-j} 递推
G = {1: [1]}
for j in range(1, 10):
    G[j + 1] = padd(pmul([1, -1, 0, j], G[j]), [0, 0, j])
okG = all(all((peval(UP[k], -j) == (G[j][k] if k < len(G[j]) else 0)) for k in range(0, 31)) for j in range(1, 11))
okG = okG and all(len(G[j]) - 1 == 3 * j - 3 for j in range(1, 11))
check('T5.3.2-neg', ok and okG, 'U_k(-j)=0（1<=j<=floor((k+2)/3)）、U_k(-s_k-1)≠0、U_{3j}(-j-1)=j!、G_{-j} 递推与次数 3j-3（k<=30，j<=10）; bad=%s' % bad[:3])

# T5.3(4)：Möbius（直接在允许行偏序集上计算）
def mobius(k):
    rows = [r for r in product((0, 1), repeat=k) if all(not (r[i:i + 3] == (0, 0, 1) or r[i:i + 3] == (0, 1, 0)) for i in range(k - 2))]
    le = lambda a, c: all(x <= y for x, y in zip(a, c))
    bot, top = tuple([0] * k), tuple([1] * k)
    mu = {bot: 1}
    order = sorted(rows, key=sum)
    for r in order:
        if r == bot:
            continue
        mu[r] = -sum(mu[s] for s in order if s != r and le(s, r) and s in mu)
    return mu[top]


mus = [mobius(k) for k in range(1, 10)]
check('T5.3.4-mobius', mus == [-1, 1, 1, 0, 0, 0, 0, 0, 0] and all(peval(UP[k], -2) == mus[k - 1] for k in range(1, 10)),
      'μ(0̂,1̂)（允许行偏序集直接计算）= U_k(-2)：%s（k=1..9）' % mus)

# ---------------------------------------------------------------- T5.4(3)：A038718
txt = open(os.path.join(ROOT, 'data', 'oeis', 'A038718.txt'), encoding='utf-8').read()
off = re.search(r'%O A038718 (\d+),', txt).group(1)
bf = {}
for line in open(os.path.join(ROOT, 'data', 'oeis', 'b038718.txt'), encoding='utf-8'):
    line = line.strip()
    if line and not line.startswith('#'):
        n_, v_ = line.split()
        bf[int(n_)] = int(v_)
    if len(bf) > 80:
        break
Rcol = U_col(1, 70)
ok_shift = all(bf[k + 2] == Rcol[k] for k in range(0, 70)) and bf[1] == 1
NS = 70


def ser_div(num, den, n):
    num = [F(x) for x in num] + [F(0)] * n
    out = []
    for i in range(n):
        c = num[i] / den[0]
        out.append(c)
        for j, dv in enumerate(den):
            if i + j < len(num):
                num[i + j] -= c * dv
    return out


den = pmul([1, -1], [1, -1, 0, -1])
g1 = ser_div([1, -1, 1], den, NS)
g2 = ser_div([1, 0, 1, -1], den, NS)
ok_g1 = all(g1[n - 1] == bf[n] for n in range(1, NS + 1))          # Σ_{n>=1} A(n) x^{n-1}
ok_g1b = g1[0] == 1 and all(g1[i + 1] == Rcol[i] for i in range(NS - 1))   # 1 + x ΣR_k x^k
ok_g2 = all(g2[k] == Rcol[k] for k in range(NS))
check('T5.4.3-A038718', off == '1' and ok_shift and ok_g1 and ok_g1b and ok_g2 and g1[1] == 1 and Rcol[1] == 2
      and den == [1, -2, 1, -1, 1],
      '条目 offset=%s；b 文件 a(k+2)=R_k（k<70），a(1)=1；(1-x+x^2)/((1-x)(1-x-x^3)) = Σ_{n>=1}a(n)x^{n-1} = 1+xΣR_kx^k；'
      'ΣR_kx^k=(1+x^2-x^3)/((1-x)(1-x-x^3))；前者 x^1 系数 1 ≠ R_1=2；分母展开 1-2x+x^2-x^3+x^4' % off)

# ---------------------------------------------------------------- T5.4(4)(5)
def oeis_data(aid):
    t = open(os.path.join(ROOT, 'data', 'oeis', aid + '.txt'), encoding='utf-8').read()
    s = ''.join(re.findall(r'%[STU] ' + aid + r' ([0-9,\-]+)', t))
    return [int(x) for x in s.split(',') if x], int(re.search(r'%O ' + aid + r' (-?\d+),', t).group(1))


d3, o3 = oeis_data('A084990')
d4, o4 = oeis_data('A326247')
ok3 = all(U(3, m) == F((m + 1) * (m * m + 5 * m + 3), 3) == 2 * comb(m + 3, 3) - (m + 1) for m in range(0, 31))
ok3 = ok3 and o3 == 0 and all(d3[m + 1 - o3] == U(3, m) for m in range(0, min(len(d3) - 1, MT + 1))) and all(d3[m + 1] == F((m + 1) * (m * m + 5 * m + 3), 3) for m in range(0, len(d3) - 1))
ok4 = all(U(4, m) == F((m + 1) * (m + 2) * (m * m + 11 * m + 6), 12) == comb(m + 2, 2) ** 2 - 4 * comb(m + 2, 4) for m in range(0, 31))
ok4 = ok4 and o4 == 0 and all(d4[m + 2 - o4] == U(4, m) for m in range(0, min(len(d4) - 2, MT + 1))) and all(d4[m + 2] == F((m + 1) * (m + 2) * (m * m + 11 * m + 6), 12) for m in range(0, len(d4) - 2))
mono4 = 2 * comb(2 + 3, 4) - 2
check('T5.4.4-5', ok3 and ok4 and mono4 == 8 and U(4, 1) == 9 and d4[3] == 9,
      'U_3=(m+1)(m^2+5m+3)/3=2C(m+3,3)-(m+1)=A084990(m+1)（offset %d）；U_4=(m+1)(m+2)(m^2+11m+6)/12=C(m+2,2)^2-4C(m+2,4)=A326247(m+2)（offset %d）；[2]^4 单调 4 元组 8≠U_4(1)=9' % (o3, o4))

say('elapsed %.1fs' % (time.time() - t0))
write_log('final_audit_math-c4c5_s5.log')
