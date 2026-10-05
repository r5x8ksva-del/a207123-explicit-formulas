# -*- coding: utf-8 -*-
"""r-c1 独立复核 3：(C2) 全部（C2-rec-closed、C2-order、C2-minimal、C2-sqfree、C2-growth、Rk-gf）。

真值：自写高度 DP（U_k(m)，k<=200, m<=30；增长率部分 k<=1500, m<=20）。
  G1  (1-x-m x^3)G_m = G_{m-1} + m x^2，逐项到 x^200，m<=30
  G2  P_m*G_m == W_m（逐项到 x^200，m<=30）；x W_m = 1-P_m-x sum_{j<m}P_j 精确多项式恒等式 m<=60；deg/lc（m<=60）
  G3  以 P_m 为连接多项式的递推作用于 DP 数据：3m+1<=k<=200，m<=30
  G4  最简性：
      (a) 精确：W_i mod b_i（Fraction）与 b_i 的 gcd=1，0<=i<=150；W_m ≡ W_i (mod b_i) 精确核对 i<=m<=24
      (b) 模 p 证书：p ∤ i 时 gcd_{F_p}(W_i mod b_i, b_i)=1 ⇒ Q 上互素（论证见报告），0<=i<=1000
      (c) 有理根逐个试除（b_i(±1/s)，s|i）：i<=3000 中可约的恰为 i=y^2(y-1)
      (d) Berlekamp–Massey：模两个大素数作用于 DP 数据，线性复杂度恰为 3m+1 且连接多项式 ≡ P_m，m<=30
  G5  无重因子：精确 gcd(b_i,b_i')=1（i<=200）；模 p gcd(P_m,P_m')=1（m<=60，p>m）
  G6  增长率与 c_m（decimal 数值，容差写明）：rho_m 用二分法；c_m 三种算法互比：
      (A) 留数公式 -W_m(x_m)/(x_m P_m'(x_m))（P_m' 直接对多项式求导），(B) c1 的化简式，(C) U_1500(m)/rho^1500
      另：m=4（rho=2）、m=18（rho=3）时 c_m 为有理数，精确核对 V_k=U_k(m)-c_m rho^k 被 P_m/(1-rho x) 零化（k<=200）
  G7  R_k 的 g.f.：sum R_k x^k = (1+x^2-x^3)/((1-x)(1-x-x^3))，R_k=[x^{k+1}](1-x+x^2)/((1-x)(1-x-x^3))，k<=200
"""
import os
import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction
from math import factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rc1lib import (U_column, Reporter, trim, add, sub, scal, mul, shiftx, ev, deriv, divmod_poly, gcd_poly,  # noqa: E402
                    bpoly, ser_mul, ser_inv, bm_mod)

rep = Reporter('r-c1-C2')
T0 = time.time()
KC, MC = 200, 30
COL = {m: U_column(m, KC) for m in range(MC + 1)}
print('INFO DP k<=%d m<=%d [%.1fs]' % (KC, MC, time.time() - T0), flush=True)
NS = KC + 1

PC = {-1: [1]}
for i in range(0, 61):
    PC[i] = mul(PC[i - 1], bpoly(i))
WC = {-1: [1]}
for m in range(0, 61):
    WC[m] = add(WC[m - 1], shiftx(scal(PC[m - 1], m), 2)) if m >= 1 else [1]


def pad(p, n):
    p = list(p)[:n]
    return p + [0] * (n - len(p))


# ---------------- G1 ----------------
t = time.time()
bad = []
for m in range(MC + 1):
    lhs = ser_mul(bpoly(m), COL[m], NS)
    rhs = list(COL[m - 1]) if m >= 1 else [1] + [0] * (NS - 1)
    rhs = pad(rhs, NS)
    rhs[2] += m
    if lhs != rhs:
        bad.append(m)
rep('G1-rec', not bad, '(C2) (1-x-m x^3)G_m=G_{m-1}+m x^2（G_{-1}=1），逐项到 x^200，0<=m<=30 [%.1fs] %s' % (time.time() - t, bad[:3]))

# ---------------- G2 ----------------
t = time.time()
bad = []
for m in range(MC + 1):
    if ser_mul(PC[m], COL[m], NS) != pad(WC[m], NS):
        bad.append(('PG=W', m))
for m in range(0, 61):
    S = []
    for j in range(m):
        S = add(S, PC[j])
    if shiftx(WC[m], 1) != sub(sub([1], PC[m]), shiftx(S, 1)):
        bad.append(('xW', m))
    if len(PC[m]) - 1 != 3 * m + 1 or len(WC[m]) - 1 != 3 * m:
        bad.append(('deg', m))
    if PC[m][-1] != (-1) ** (m + 1) * factorial(m) or WC[m][-1] != (-1) ** m * factorial(m):
        bad.append(('lc', m))
rep('G2-closed', not bad, '(C2) P_m G_m == W_m（逐项到 x^200，m<=30）；x W_m = 1-P_m-x sum_{j<m}P_j（精确，m<=60）；'
    'deg P_m=3m+1, deg W_m=3m, lc P_m=(-1)^{m+1}m!, lc W_m=(-1)^m m!（m<=60） [%.1fs] %s' % (time.time() - t, bad[:3]))

# ---------------- G3 ----------------
t = time.time()
bad = []
for m in range(MC + 1):
    P = PC[m]
    d = len(P) - 1
    for k in range(d, KC + 1):
        if sum(P[i] * COL[m][k - i] for i in range(d + 1)) != 0:
            bad.append((m, k))
            break
rep('G3-order', not bad, '(C2) sum_i [x^i]P_m * U_{k-i}(m) = 0 对 3m+1<=k<=200（DP 数据），0<=m<=30 [%.1fs] %s' % (time.time() - t, bad[:3]))

# ---------------- G4 最简性 ----------------
t = time.time()


def W_mod_b_exact(i):
    """W_i mod b_i，用 Fraction，在 Q[x]/(b_i) 中迭代（不展开整个 W_i）。"""
    b = bpoly(i)

    def red(p):
        return divmod_poly(p, b)[1] if len(trim(p)) >= len(b) else [Fraction(c) for c in trim(p)]

    W = [Fraction(1)]
    P = [Fraction(1)]          # P_{j-1} mod b_i，从 P_{-1}=1 开始
    for j in range(1, i + 1):
        P = red(mul(P, bpoly(j - 1)))
        W = add(W, red(shiftx(scal(P, j), 2)))
    return red(W)


bad = []
for i in range(0, 151):
    r = W_mod_b_exact(i)
    if not r:
        bad.append(('zero', i))
        continue
    g = gcd_poly(r, bpoly(i))
    if g != [1]:
        bad.append(('gcd', i, g))
# W_m ≡ W_i (mod b_i)
for m in range(0, 25):
    for i in range(0, m + 1):
        if divmod_poly(sub(WC[m], WC[i]), bpoly(i))[1]:
            bad.append(('cong', m, i))
rep('G4a-gcd-exact', not bad, '(C2 最简性) 精确：gcd(W_i mod b_i, b_i)=1 对 0<=i<=150；W_m≡W_i (mod b_i) 对 0<=i<=m<=24 '
    '（两者合起来给出 gcd(W_m,P_m)=1 对 m<=150） [%.1fs] %s' % (time.time() - t, bad[:3]))

t = time.time()


def polymod_p(a, b, p):
    """F_p 上 a mod b（系数列表，低次在前）。"""
    a = [x % p for x in a]
    while a and a[-1] == 0:
        a.pop()
    b = [x % p for x in b]
    while b and b[-1] == 0:
        b.pop()
    inv = pow(b[-1], p - 2, p)
    while len(a) >= len(b):
        c = a[-1] * inv % p
        d = len(a) - len(b)
        for j, bj in enumerate(b):
            a[j + d] = (a[j + d] - c * bj) % p
        while a and a[-1] == 0:
            a.pop()
    return a


def polygcd_p(a, b, p):
    a = [x % p for x in a]
    b = [x % p for x in b]
    while a and a[-1] == 0:
        a.pop()
    while b and b[-1] == 0:
        b.pop()
    while b:
        a, b = b, polymod_p(a, b, p)
    return len(a) - 1 if a else -1     # gcd 的次数


def mulmod_p(a, b, mod, p):
    r = [0] * (len(a) + len(b) - 1) if a and b else []
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % p
    return polymod_p(r, mod, p) if r else []


PRIMES = [1_000_000_007, 998_244_353]
IMAX_P = 1000
bad, certified = [], 0
for i in range(0, IMAX_P + 1):
    okp = False
    for p in PRIMES:                       # 两个素数都 > IMAX_P，所以 p ∤ i；第一个失败才用第二个
        b = bpoly(i)
        P = [1]
        W = [1]
        for j in range(1, i + 1):
            P = mulmod_p(P, bpoly(j - 1), b, p)
            term = [0, 0] + [(c * j) % p for c in P]
            W = polymod_p([(W[t] if t < len(W) else 0) + (term[t] if t < len(term) else 0) for t in range(max(len(W), len(term)))], b, p)
        if polygcd_p(W, b, p) == 0:
            okp = True
            break
        bad.append((i, p))
    if okp:
        certified += 1
rep('G4b-gcd-modp', certified == IMAX_P + 1, '(C2 最简性，模 p 证书) 0<=i<=%d：F_p 上 gcd(W_i mod b_i, b_i)=1（p=1e9+7，失败才换 998244353；p ∤ i），'
    '从而 Q 上 W_i 与 b_i 互素，gcd(W_m,P_m)=1 对 m<=%d [certified=%d; 未在第一个素数上通过的: %s; %.1fs]'
    % (IMAX_P, IMAX_P, certified, bad[:3], time.time() - t))

t = time.time()
bad, red = [], []
for i in range(1, 3001):
    divs = [s for s in range(1, i + 1) if i % s == 0]
    has_root = any(ev(bpoly(i), Fraction(sg, s)) == 0 for s in divs for sg in (1, -1))
    y = round(i ** (1 / 3)) + 2
    form = any(yy * yy * (yy - 1) == i for yy in range(2, y + 2))
    if has_root != form:
        bad.append(i)
    if has_root:
        red.append(i)
rep('G4c-reducible', not bad and red == [4, 18, 48, 100, 180, 294, 448, 648, 900, 1210, 1584, 2028, 2548],
    '(C2) 有理根逐个试除 b_i(±1/s)（s|i）：1<=i<=3000 中 b_i 可约的恰为 i=y^2(y-1)：%s [%.1fs] %s' % (red, time.time() - t, bad[:3]))

t = time.time()
bad = []
for m in range(0, MC + 1):
    L0 = 3 * m + 1
    seq = COL[m][:2 * L0 + 10]
    for p in PRIMES:
        C, L = bm_mod(seq, p)
        Pm = [c % p for c in PC[m]]
        if L != L0 or C != Pm:
            bad.append((m, p, L))
rep('G4d-BM', not bad, '(C2 最简性，独立于闭式) 模 1e9+7 与 998244353 的 Berlekamp–Massey 作用于 DP 数据 U_0..U_{6m+11}(m)：'
    '线性复杂度恰为 3m+1、连接多项式 ≡ P_m，0<=m<=30（模 p 复杂度 <= Q 上复杂度 <= 3m+1，故 Q 上恰为 3m+1） [%.1fs] %s'
    % (time.time() - t, bad[:3]))

# ---------------- G5 无重因子 ----------------
t = time.time()
bad = []
for i in range(0, 201):
    if gcd_poly(bpoly(i), deriv(bpoly(i))) != [1]:
        bad.append(('b', i))
for m in range(0, 61):
    p = PRIMES[0]
    if polygcd_p(PC[m], deriv(PC[m]), p) != 0:
        bad.append(('P', m))
rep('G5-sqfree', not bad, '(C2) 无重因子：精确 gcd(b_i,b_i\')=1（0<=i<=200）；F_p 上 gcd(P_m,P_m\')=1（m<=60，p=1e9+7>m，lc P_m=±m! 非零）'
    ' [%.1fs] %s' % (time.time() - t, bad[:3]))

# ---------------- G6 增长率 ----------------
t = time.time()
getcontext().prec = 220
KG = 1500
bad = []
worst = {'AB': Decimal(0), 'AC': Decimal(0)}
rhos = [Decimal(1)]
for m in range(1, 21):
    f = lambda y: y * y * y - y * y - m  # noqa: E731
    lo, hi = Decimal(1), Decimal(m + 2)
    if not (f(lo) < 0 < f(hi)):
        bad.append(('bracket', m))
    for _ in range(700):
        mid = (lo + hi) / 2
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    rho = (lo + hi) / 2
    rhos.append(rho)
    x = 1 / rho
    # (A) 留数公式
    Pm = PC[m]
    dPm = deriv(Pm)
    A = -ev(WC[m], x) / (x * ev(dPm, x))
    # (B) c1 的化简式
    Gm1 = ev(WC[m - 1], x) / ev(PC[m - 1], x)
    B = (Gm1 + m * x * x) / (x * (1 + 3 * m * x * x))
    # (C) 数据
    col = U_column(m, KG)
    C = Decimal(col[KG]) / rho ** KG
    eAB = abs(A / B - 1)
    eAC = abs(C / A - 1)
    worst['AB'] = max(worst['AB'], eAB)
    worst['AC'] = max(worst['AC'], eAC)
    if eAB > Decimal('1e-150') or eAC > Decimal('1e-6') or not (A > 0):
        bad.append(('cm', m, float(eAB), float(eAC)))
    # 复根模长 |w|^2 = rho(rho-1)：由 z^3-z^2-m=(z-rho)(z^2+(rho-1)z+rho(rho-1)) 的商式
    q0 = rho * (rho - 1)
    if abs(rho * q0 - m) > Decimal('1e-150') or not (q0 < rho * rho) or not ((rho - 1) ** 2 - 4 * q0 < 0):
        bad.append(('roots', m))
    # P_{m-1}(x_m) = m! x_m^{3m}
    if abs(ev(PC[m - 1], x) / (factorial(m) * x ** (3 * m)) - 1) > Decimal('1e-150'):
        bad.append(('Pm1', m))
if any(not (rhos[i] < rhos[i + 1]) for i in range(20)):
    bad.append('rho-monotone')
rep('G6-growth-num', not bad, '(C2 增长率，数值 decimal 220 位) 1<=m<=20：二分求 rho_m；留数公式 (A) 与 c1 化简式 (B) 相对差<1e-150（实测 %.1e）；'
    'U_1500(m)/rho^1500 与 (A) 相对差<1e-6（实测 %.1e）；c_m>0；|w_m|^2=rho(rho-1)<rho^2 且二次因子判别式<0；P_{m-1}(x_m)=m! x_m^{3m}；rho_m 严格增 [%.1fs] %s'
    % (worst['AB'], worst['AC'], time.time() - t, bad[:3]))

t = time.time()
bad = []
for (m, r) in ((4, 2), (18, 3)):
    x = Fraction(1, r)
    if ev(bpoly(m), x) != 0:
        bad.append(('root', m))
    cm = -ev(WC[m], x) / (x * ev(deriv(PC[m]), x))
    Gm1 = ev(WC[m - 1], x) / ev(PC[m - 1], x)
    cm2 = (Gm1 + m * x * x) / (x * (1 + 3 * m * x * x))
    if cm != cm2:
        bad.append(('cm-formulas', m))
    Q, R = divmod_poly(PC[m], [1, -r])
    if R:
        bad.append(('div', m))
    V = [COL[m][k] - cm * r ** k for k in range(KC + 1)]
    d = len(Q) - 1
    for k in range(d, KC + 1):
        if sum(Q[i] * V[k - i] for i in range(d + 1)) != 0:
            bad.append(('annih', m, k))
            break
    if m == 4 and cm != Fraction(645, 6):
        bad.append(('c4', cm))
    if ev(PC[m - 1], x) != factorial(m) * x ** (3 * m):
        bad.append(('Pm1', m))
    print('INFO exact c_%d = %s' % (m, cm), flush=True)
rep('G6-exact', not bad, '(C2) 有理情形精确核对：m=4（rho=2）c_4=645/6，m=18（rho=3）；V_k=U_k(m)-c_m rho^k 被 P_m/(1-rho x) 精确零化（k<=200），'
    '留数公式 == c1 化简式；P_{m-1}(x_m)=m! x_m^{3m} [%.1fs] %s' % (time.time() - t, bad[:3]))

# ---------------- G7 R_k ----------------
t = time.time()
R = COL[1]
den = mul([1, -1], [1, -1, 0, -1])
inv = ser_inv(den, KC + 2)
ok1 = ser_mul([1, 0, 1, -1], inv, KC + 1) == R[:KC + 1]
s2 = ser_mul([1, -1, 1], inv, KC + 2)
ok2 = all(s2[k + 1] == R[k] for k in range(KC + 1))
ok3 = all(R[k] == 1 + R[k - 1] + (R[k - 3] if k >= 3 else (1 if k == 2 else 0)) for k in range(1, KC + 1))
ok4 = gcd_poly([1, 0, 1, -1], den) == [1]
rep('G7-Rk-gf', ok1 and ok2 and ok3 and ok4, 'R_k=U_k(1)：sum R_k x^k=(1+x^2-x^3)/((1-x)(1-x-x^3))（既约）；R_k=[x^{k+1}](1-x+x^2)/((1-x)(1-x-x^3))；'
    'R_k=1+R_{k-1}+R_{k-3}（R_{-1}=1,R_{-2}=0），k<=200 [%s %s %s %s; %.1fs]' % (ok1, ok2, ok3, ok4, time.time() - t))

print('TIME r3 total %.1fs' % (time.time() - T0), flush=True)
sys.exit(0 if rep.summary() else 1)
