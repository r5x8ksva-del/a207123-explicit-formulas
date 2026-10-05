# -*- coding: utf-8 -*-
"""a2-consistency 审计脚本：核对报告正文里抄写的公式 / 数值，以及几处疑点。
只读：不导入 core.py 以外的项目模块；真值用第 1 节参考实现（good 规则）与已证明的引理 1 / 三角递推自行计算。
运行：py -3.14 code/audit/a2-consistency/audit_checks.py
"""
import sys
from fractions import Fraction as Fr
from math import comb, factorial
from decimal import Decimal, getcontext

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def rep(cid, ok, msg):
    RES.append(ok)
    print(('PASS ' if ok else 'FAIL ') + cid + ' ' + msg, flush=True)


# ---------------------------------------------------------------- 真值：参考实现 U_list（第 1 节原文）
def good(a, b, c):
    return b == c or (a >= b and a >= c)


def U_list(m, K):
    out = [1, m + 1]
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    out.append(sum(cnt.values()))
    for k in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
        cnt = new
        out.append(sum(cnt.values()))
    return out


# 引理 1（已证明）扩展整表；先与参考实现交叉
def lemma1_table(K, M):
    T = [[0] * (M + 1) for _ in range(K + 1)]

    def g(k, m):
        if k == 0 or k == -1:
            return 1
        if k == -2:
            return 0
        return T[k][m]
    for m in range(M + 1):
        T[0][m] = 1
    for k in range(1, K + 1):
        for m in range(M + 1):
            T[k][m] = (T[k][m - 1] if m >= 1 else 0) + g(k - 1, m) + m * g(k - 3, m)
    return T


KR, MR = 24, 8
ref = [U_list(m, KR) for m in range(MR + 1)]
T = lemma1_table(130, 30)
ok = all(ref[m][k] == T[k][m] for m in range(MR + 1) for k in range(KR + 1))
rep('anchor', ok, 'lemma-1 table == prompt reference U_list (k<=%d, m<=%d)' % (KR, MR))


# N 三角（已证明）+ 与 U 的容斥交叉
def N_tri(K):
    N = [[0] * (K + 3) for _ in range(K + 1)]
    N[0][0] = 1
    N[1][1] = 1
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


NT = N_tri(160)


def N_from_U(k, q):
    def Um1(kk, i):
        if i == -1:
            return 1 if kk == 0 else 0
        return T[kk][i]
    return sum((-1) ** (q - i) * comb(q, i) * Um1(k, i - 1) for i in range(0, q + 1))


ok = all(NT[k][q] == N_from_U(k, q) for k in range(0, 31) for q in range(0, k + 1))
rep('anchor-N', ok, 'triangle-recurrence N == inclusion-exclusion from DP U (k<=30)')


def D(k, d):
    q = k - d
    return NT[k][q] if 0 <= q <= k else 0


def pev(coefs_desc, x, den):
    v = 0
    for c in coefs_desc:
        v = v * x + c
    return Fr(v, den)


# ---------------------------------------------------------------- A1：报告 T4.1 中抄写的 p_2..p_5
P_REPORT = {
    2: ([1, -10, 43, -98, 164], 4),
    3: ([1, -27, 331, -2225, 8560, -17392, 11088], 24),
    4: ([1, -52, 1242, -17280, 151217, -845644, 2926356, -5702176, 5014464], 192),
    5: ([1, -85, 3350, -79370, 1241073, -13308173, 98708360, -498528820, 1637903536, -3158022432, 2686170240], 1920),
}
for d, (cf, den) in P_REPORT.items():
    ok_eq = all(pev(cf, k, den) == D(k, d) for k in range(2 * d + 2, 161))
    e1 = D(2 * d + 1, d) - pev(cf, 2 * d + 1, den)
    e0 = D(2 * d, d) - pev(cf, 2 * d, den)
    ok_def = (e1 == (-1) ** (d + 1) * factorial(d + 1)) and (e0 == Fr((-1) ** (d + 1) * factorial(d + 2), 2))
    rep('A1-p%d' % d, ok_eq and ok_def, 'report p_%d == N(k,k-%d) for %d<=k<=160; defects at 2d+1, 2d: %s, %s' % (d, d, 2 * d + 2, e1, e0))

# A2：p_2 以 m=k-5 表示
ok = all(Fr(m ** 4 + 10 * m ** 3 + 43 * m ** 2 + 82 * m + 124, 4) == pev(P_REPORT[2][0], m + 5, 4) for m in range(-10, 40))
rep('A2-p2-in-m', ok, 'p_2 = (m^4+10m^3+43m^2+82m+124)/4 with m=k-5')

# A3：d=2 基点 6 的 Newton 系数
vals = [D(6 + n, 2) for n in range(6)]
newton = []
row = vals[:]
while row:
    newton.append(row[0])
    row = [row[i + 1] - row[i] for i in range(len(row) - 1)]
rep('A3-newton-d2', newton[:5] == [65, 74, 64, 30, 6] and newton[5] == 0, 'Delta^i D(6,2) = %s' % newton[:6])


# ---------------------------------------------------------------- 多项式 u_k(m)（由二项式基 N）
def poly_mul(a, b):
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def u_poly(k):
    """升幂 Fraction 系数：u_k(m) = sum_q N(k,q) C(m+1,q)。"""
    P = [Fr(0)] * (k + 1)
    for q in range(0, k + 1):
        if NT[k][q] == 0:
            continue
        p = [Fr(1)]
        for r in range(q):
            p = poly_mul(p, [Fr(1 - r), Fr(1)])
        for i, c in enumerate(p):
            P[i] += c * NT[k][q] / factorial(q)
    return P


ok = True
for k in range(1, 26):
    P = u_poly(k)
    for m in range(0, 9):
        if sum(c * m ** i for i, c in enumerate(P)) != T[k][m]:
            ok = False
rep('A4-upoly', ok, 'u_k from N-basis reproduces DP (k<=25, m<=8)')

# A4：T5.2 的 m 次首项系数
ok = True
bad = []
for k in range(2, 61):
    P = u_poly(k)
    if P[k] != Fr(2, factorial(k)):
        ok = False; bad.append(('lead', k))
    if k >= 4 and P[k - 1] != Fr(k * k - 2 * k - 1, factorial(k - 1)):
        ok = False; bad.append(('k-1', k))
    if k >= 6 and P[k - 2] != Fr(3 * k ** 4 - 36 * k ** 3 + 162 * k ** 2 - 313 * k + 422, 12 * factorial(k - 2)):
        ok = False; bad.append(('k-2', k))
    if k >= 8 and P[k - 3] != Fr(k ** 6 - 30 * k ** 5 + 379 * k ** 4 - 2533 * k ** 3 + 9570 * k ** 2 - 19331 * k + 13380, 24 * factorial(k - 3)):
        ok = False; bad.append(('k-3', k))
P3 = u_poly(3)
ok = ok and P3[2] == 2 and Fr(9 - 6 - 1, 2) == 1
rep('A4-T5.2', ok, 'report T5.2 coefficient formulas hold for k<=60 (bad=%s); [m^2]U_3=%s (formula gives 1)' % (bad[:5], P3[2]))

# ---------------------------------------------------------------- A5：Num_q（T4.3）
def b_poly(i):
    return [Fr(1), Fr(-1), Fr(0), Fr(-i)]


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def shift(a, s):
    return [Fr(0)] * s + list(a)


def scal(a, c):
    return [c * x for x in a]


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


NUM = {1: [Fr(0), Fr(1)], 2: [Fr(0), Fr(0), Fr(2), Fr(0), Fr(1)]}
for q in range(3, 41):
    t1 = poly_mul([Fr(0), Fr(1), Fr(0), Fr(2 * (q - 1))], NUM[q - 1])
    t2 = scal(shift(poly_mul(b_poly(q - 2), NUM[q - 2]), 3), Fr(q - 1))
    NUM[q] = trim(padd(t1, t2))


def P_poly(m):
    p = [Fr(1)]
    for i in range(m + 1):
        p = poly_mul(p, b_poly(i))
    return p


ok = True
for q in range(1, 16):
    ser = [Fr(NT[k][q]) if k <= 160 else Fr(0) for k in range(3 * q + 3)]
    prod = poly_mul(ser, P_poly(q - 1))[:3 * q + 3]
    if trim(prod) != trim(NUM[q]):
        ok = False
rep('A5-num-anchor', ok, 'Num_q from 3-term recurrence == P_{q-1}*sum_k N(k,q)x^k (q<=15)')


def coef(p, i):
    return p[i] if 0 <= i < len(p) else 0


ok1 = all(coef(NUM[q], q + 1) == q * q - q - 4 for q in range(3, 41)) and coef(NUM[2], 3) != 2 * 2 - 2 - 4
ok2 = all(coef(NUM[q], q + 2) == Fr(q ** 4 - 6 * q ** 3 + 7 * q ** 2 - 2 * q + 76, 4) for q in range(4, 41))
d3 = coef(NUM[3], 5) - Fr(81 - 162 + 63 - 6 + 76, 4)
rep('A5-low', ok1 and ok2 and d3 == -6, 'T4.3(5) examples hold (q<=40); defect at q=3 for j=2: %s (expect (-1)^3 3! = -6)' % d3)


def H(n):
    return sum(Fr(1, i) for i in range(1, n + 1))


ok = all(coef(NUM[q], 3 * q - 4) == factorial(q - 1) * (q - 1 + H(q - 1)) for q in range(2, 41))
ok = ok and all(coef(NUM[q], 3 * q - 5) == (q - 1) * factorial(q - 1) * (H(q - 1) - 1) for q in range(3, 41))
ok = ok and all(coef(NUM[q], 3 * q - 3) == 0 for q in range(2, 41))
rep('A5-high', ok, 'T4.3(6) j=1,2,3 examples hold (q<=40)')
vals = [sum(NUM[q]) for q in range(1, 6)]
rep('A5-at1', vals == [1, 3, 13, 73, 501], 'Num_q(1), q=1..5 = %s' % vals)

# ---------------------------------------------------------------- A6：h_k'(1)、[t^1]h_k（T5.3(1)）
def h_poly(k):
    if k == 0:
        return [Fr(1)]
    h = [Fr(0)] * (k + 1)
    for q in range(1, k + 1):
        if NT[k][q] == 0:
            continue
        p = [Fr(1)]
        for _ in range(k - q):
            p = poly_mul(p, [Fr(1), Fr(-1)])
        p = shift(p, q - 1)
        for i, c in enumerate(p):
            h[i] += c * NT[k][q]
    return trim(h)


ok = True
for k in range(4, 61):
    h = h_poly(k)
    hp1 = sum(i * c for i, c in enumerate(h))
    if hp1 != -(k * k - 3 * k - 2):
        ok = False
    R = T[k][1]
    if coef(h, 1) != R - k - 1:
        ok = False
rep('A6-h', ok, "h_k'(1) = -(k^2-3k-2) and [t^1]h_k = R_k-k-1 (4<=k<=60)")

# ---------------------------------------------------------------- A7：T2.6(ii) 的范数（K_2 = Q[x]/(2x^3+x-1)）
def norm_in(f_monic, a):
    """f_monic: x^3 + c2 x^2 + c1 x + c0 的 [c0,c1,c2]；a: 升幂系数。返回 det(乘 a 的矩阵)。"""
    c0, c1, c2 = f_monic

    def red(p):
        p = list(p) + [Fr(0)] * 3
        for i in range(len(p) - 1, 2, -1):
            t = p[i]
            if t:
                p[i] = Fr(0)
                p[i - 1] -= t * c2
                p[i - 2] -= t * c1
                p[i - 3] -= t * c0
        return p[:3]
    cols = []
    for j in range(3):
        cols.append(red(poly_mul(a, shift([Fr(1)], j))))
    M = [[cols[j][i] for j in range(3)] for i in range(3)]
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def W_tilde(i):
    w = [Fr(0)] * (3 * i + 3)
    w[0] = Fr(1)
    for j in range(1, i + 1):
        ff = 1
        for r in range(j):
            ff *= (i - r)
        w[3 * j + 2] += j * ff
    return w


def vp(fr, p):
    if fr == 0:
        return None
    v = 0
    n, dn = fr.numerator, fr.denominator
    while n % p == 0:
        n //= p; v += 1
    while dn % p == 0:
        dn //= p; v -= 1
    return v


f2 = [Fr(-1, 2), Fr(1, 2), Fr(0)]           # x^3 + x/2 - 1/2  (= (2x^3+x-1)/2)
Nx = norm_in(f2, [Fr(0), Fr(1)])
Wt2 = W_tilde(2)
NW = norm_in(f2, Wt2)
NWm1 = norm_in(f2, padd(Wt2, [Fr(-1)]))
print('   [info] K_2: N(x)=%s, N(W~_2)=N(1+2x^5+4x^8)=%s, N(W~_2 - 1)=%s' % (Nx, NW, NWm1))
print('   [info] v_17(N(W~_2))=%s, v_17(N(W~_2 - 1))=%s, v_103(N(W~_2))=%s' % (vp(NW, 17), vp(NWm1, 17), vp(NW, 103)))
ok = (NWm1 == Fr(17, 8)) and (vp(NW, 17) is not None) and (vp(NW, 17) % 3 == 0)
rep('A7-T2.6ii-norm', ok, 'E-part uses W~_2 - 1 (norm 17/8, v_17=1); the report writes N(W~_2), whose 17-adic valuation is %s (not = 1 mod 3)' % vp(NW, 17))

# ---------------------------------------------------------------- A8：c_1、c_2、c_3（T5.1(3)）
getcontext().prec = 60


def real_root(m):
    lo, hi = Decimal(1), Decimal(3) + Decimal(m)
    for _ in range(300):
        mid = (lo + hi) / 2
        if mid ** 3 - mid ** 2 - m > 0:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2


def c_closed(m):
    r = real_root(m)
    s = sum(r ** (3 * i) / factorial(i) for i in range(m))
    return r * (r ** (3 * m + 1) / factorial(m) - s) / (3 * r - 2)


c1, c2, c3 = c_closed(1), c_closed(2), c_closed(3)
r1 = real_root(1)
c1q = (10 + 15 * r1 + 17 * r1 ** 2) / 31
ok = (abs(c1 - Decimal('2.2096081318')) < Decimal('1e-10') and abs(c2 - Decimal('7.8411192294')) < Decimal('1e-10')
      and abs(c3 - Decimal('28.976857317')) < Decimal('1e-9') and abs(c1 - c1q) < Decimal('1e-50'))
rep('A8-cm', ok, 'c_1=%s c_2=%s c_3=%s; (10+15r+17r^2)/31=%s' % (str(c1)[:14], str(c2)[:14], str(c3)[:14], str(c1q)[:14]))
# 数值对照 DP：U_400(m)/(c_m rho^400)
ok = True
for m, cm in [(1, c1), (2, c2), (3, c3)]:
    col = U_list(m, 400) if m <= 1 else None
for m, cm in [(1, c1), (2, c2), (3, c3)]:
    TT = lemma1_table(400, m)
    rr = real_root(m)
    rel = Decimal(TT[400][m]) / (cm * rr ** 400) - 1
    if abs(rel) > Decimal('1e-6'):
        ok = False
rep('A8-cm-vs-DP', ok, 'U_400(m)/(c_m rho_m^400) - 1 small for m=1,2,3')

# ---------------------------------------------------------------- A9：T3.4(3) 的界 S(3/5,-1/2) <= -1057.810873 + 3.5e-118 ?
x, t = Fr(3, 5), Fr(-1, 2)
G = Fr(1)            # G_{-1}
S = Fr(0)
tp = Fr(1)
for m in range(0, 401):
    bm = 1 - x - m * x ** 3
    G = (G + m * x * x) / bm
    S += tp * G
    tp *= t
getcontext().prec = 40
Sd = Decimal(S.numerator) / Decimal(S.denominator)
claimed = Decimal('-1057.810873') + Decimal('3.5e-118')
print('   [info] exact partial sum (m<=400) S = %s' % Sd)
rep('A9-T3.4(3)-bound', Sd > claimed, 'partial sum %s is LARGER than the claimed upper bound -1057.810873+3.5e-118 (rounding went the wrong way; S<0 still true)' % str(Sd)[:20])

# ---------------------------------------------------------------- A10：T5.4(3) g.f.
def series_div(num, den, n):
    out = []
    num = list(num) + [0] * n
    for i in range(n):
        c = Fr(num[i]) / den[0]
        out.append(c)
        for j in range(1, len(den)):
            if i + j < len(num):
                num[i + j] -= c * den[j]
    return out


Dn = [1, -2, 1, -1, 1]   # (1-x)(1-x-x^3)
s1 = series_div([1, -1, 1], Dn, 30)
s2 = series_div([1, 0, 1, -1], Dn, 30)
Rk = [T[k][1] for k in range(30)]
ok = (s2 == Rk) and (s1[0] == 1) and all(s1[k + 1] == Rk[k] for k in range(29))
rep('A10-Rk-gf', ok, '(1-x+x^2)/D = 1 + x*sum R_k x^k = sum_{n>=1} A038718(n) x^{n-1}; sum R_k x^k = (1+x^2-x^3)/D')

# ---------------------------------------------------------------- A11：③ 中「k=m=100 时 U 有 99 位」
TT = lemma1_table(100, 100)
rep('A11-digits', len(str(TT[100][100])) == 99, 'U_100(100) has %d digits' % len(str(TT[100][100])))

# ---------------------------------------------------------------- A12：R_k = c_1(k+3)+c_1(k-2)-1（T2.5(3)、③）
def c_i(i, n):
    if n < 0:
        return 0
    return sum(comb(n - 2 * j, j) * i ** j for j in range(0, n // 3 + 1))


ok = all(T[k][1] == c_i(1, k + 3) + c_i(1, k - 2) - 1 for k in range(0, 100))
rep('A12-Rk-ci', ok, 'R_k = c_1(k+3)+c_1(k-2)-1 for 0<=k<100')

# ---------------------------------------------------------------- A13：T2.6(iii) 需要 m>=2：m=1 时 F3 型就是两族 u 型表示
ok = True
for k in range(0, 60):
    A = sum(comb(k + 1 + 1 - 2 * s, 1 + s) for s in range(0, (k + 1) // 3 + 1)) if True else 0
    # F3 for m=1: U_k(1) = sum_s S(1+s,1) C(k+2-2s, 1+s) - sum_s H(1,s,1) C(k-2s, s)
    A = sum(comb(k + 2 - 2 * s, 1 + s) for s in range(0, k + 2) if 0 <= 1 + s <= k + 2 - 2 * s)
    B = sum(comb(k - 2 * s, s) for s in range(0, k + 1) if 0 <= s <= k - 2 * s)
    if A - B != T[k][1]:
        ok = False
rep('A13-m1-two-family', ok, 'm=1: U_k(1) = sum_s C(k+2-2s,1+s) - sum_s C(k-2s,s) (two u-type families), k<60 -> T2.6(iii) must say m>=2')

# ---------------------------------------------------------------- A14：T3.8 维数公式在 A<2 时给负数（缺条件）
vals = [(A, B, Dd, (A - 2) * B * Dd * (Dd + 1) // 2) for (A, B, Dd) in [(1, 1, 1), (0, 2, 2), (1, 3, 2)]]
rep('A14-dimformula-cond', all(v[3] < 0 for v in vals), 'formula (A-2)B D(D+1)/2 without the A>=3,B>=1,D>=1 condition gives negative values: %s' % vals)

npass = sum(RES)
print('SUMMARY a2 pass=%d fail=%d' % (npass, len(RES) - npass))
