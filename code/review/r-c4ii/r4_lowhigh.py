# -*- coding: utf-8 -*-
"""r4：低次系数 nu_j（C4-26）、高次系数表 6（C4-27）及其一般形式猜想（C4-28）的独立复核。"""
import sys
import time
from fractions import Fraction
from math import comb, factorial
from rlib import *

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
t0 = time.time()
L = Log('r4_lowhigh')
QM = 220
Num = num_by_recurrence(QM)


def coef(q, e):
    p = Num[q]
    return p[e] if 0 <= e < len(p) else 0


def interp(xs, ys):
    """Lagrange/Newton 插值 → Fraction 升幂系数。"""
    n = len(xs)
    c = [Fraction(y) for y in ys]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            c[i] = (c[i] - c[i - 1]) / (xs[i] - xs[i - j])
    poly = []
    for i in range(n - 1, -1, -1):
        poly = add(mul(poly, [Fraction(-xs[i]), Fraction(1)]), [c[i]])
    return tr(poly)


def evf(p, x):
    return ev([Fraction(a) for a in p], Fraction(x))


# =============== C4-26：低次系数 ===============
NU_TABLE = {   # c4.md 表 5（分母，降幂分子）
    0: (1, [2]),
    1: (1, [1, -1, -4]),
    2: (4, [1, -6, 7, -2, 76]),
    3: (24, [1, -15, 85, -193, 358, -236, -3144]),
    4: (192, [1, -28, 330, -1952, 6481, -12708, 2692, 5184, 223872]),
    5: (1920, [1, -45, 890, -9690, 63513, -260965, 654060, -910900, 1601856, -1138720, -24443520]),
    6: (23040, [1, -66, 1961, -33650, 366603, -2651598, 12951003, -42452550, 93367136, -137063416,
                -12165104, 87679680, 3793098240]),
}
ok_poly, ok_tab, ok_thr, ok_lead = True, True, True, True
for j in range(0, 11):
    xs = list(range(j + 2, 3 * j + 3))            # 2j+1 个点，全部 >= j+2
    nu = interp(xs, [coef(q, q + j) for q in xs])
    if len(nu) - 1 != 2 * j:
        ok_poly = False
    if nu[-1] != Fraction(2, 2 ** j * factorial(j)):
        ok_lead = False
    for q in range(j + 2, QM + 1):
        if evf(nu, q) != coef(q, q + j):
            ok_poly = False
            L.out('  nu_%d fails at q=%d' % (j, q))
            break
    q = j + 1
    if coef(q, q + j) - evf(nu, q) != (-1) ** (j + 1) * factorial(j + 1):
        ok_thr = False
    if j in NU_TABLE:
        den, cs = NU_TABLE[j]
        if tr([Fraction(c, den) for c in reversed(cs)]) != nu:
            ok_tab = False
            L.out('  table5 mismatch j=%d' % j)
L.check('r4-nu-poly', ok_poly, 'j<=10：[x^{q+j}]Num_q 在 q>=j+2 上等于由 2j+1 个点插值出的 2j 次多项式，检验到 q<=%d' % QM)
L.check('r4-nu-lead', ok_lead, 'j<=10：nu_j 的首项系数 = 2/(2^j j!)')
L.check('r4-nu-threshold', ok_thr, 'j<=10：q=j+1 处 真值-多项式值 = (-1)^{j+1}(j+1)!（门槛 j+2 精确）')
L.check('r4-nu-table5', ok_tab, 'c4.md 表 5（nu_0..nu_6）与独立插值结果逐系数一致')

# pi_i(q) = [x^i]P_{q-1} 是 q 的 <=i 次多项式（对一切 q>=0）
ok = True
Pc = {q: Ppoly(q - 1) for q in range(0, 120)}
for i in range(0, 13):
    xs = list(range(0, i + 1))
    pi = interp(xs, [(Pc[q][i] if i < len(Pc[q]) else 0) for q in xs])
    for q in range(0, 120):
        if evf(pi, q) != (Pc[q][i] if i < len(Pc[q]) else 0):
            ok = False
L.check('r4-pi-poly', ok, 'i<=12：pi_i(q)=[x^i]P_{q-1} 在 0<=q<120 上等于由 q=0..i 插值出的 <=i 次多项式（含 q<b 的小 q）')

# 系数提取恒等式 nu_j(q) = sum_i pi_i(q) N(q+j-i, q)（原始定义 DP）
K = 70
Ucols = [U_column_mine(m, K) for m in range(0, 30)]
N = N_table_from_U(Ucols, K, 30)
ok = True
for j in range(0, 9):
    for q in range(1, 30):
        if q + j > K:
            continue
        val = sum((Pc[q][i] if i < len(Pc[q]) else 0) * N[q + j - i][q] for i in range(0, j + 1))
        if val != coef(q, q + j):
            ok = False
L.check('r4-nu-extract', ok, 'j<=8, q<30：[x^{q+j}]Num_q = sum_i pi_i(q) N(q+j-i,q)（N 来自原始定义 DP）')

# =============== C4-27：高次系数表 6 ===============
C1 = stirling1(QM + 2)
HF = {   # c4.md 表 6，键 i -> pi_{j,i}(q) 升幂系数（我按表 6 文字逐项重写，不拷贝核对模块）
    0: {1: [1]},
    1: {},
    2: {1: [-1, 1], 2: [1]},                                   # (q-1)c1 + c2
    3: {1: [1, -1], 2: [-1, 1]},                               # (q-1)(c2-c1)
    4: {1: [-1, 1], 2: [-1], 3: [1]},                          # (q-1)c1 - c2 + c3
    5: {1: scl(mul([-1, 1], [-2, 1]), Fraction(1, 2)), 2: [2, -1], 3: [-2, 1]},          # ½(q-1)(q-2)c1-(q-2)c2+(q-2)c3
    6: {1: scl(mul([-1, 1], [-6, 5]), Fraction(-1, 4)), 2: scl([-4, 1, 1], Fraction(1, 2)), 3: [0, -1], 4: [1]},
    7: {1: scl(mul([-1, 1], [-2, 1]), Fraction(3, 4)), 2: [2, -1], 3: [3, -1], 4: [-3, 1]},
    8: {1: scl(mul([-1, 1], [54, -1, 2]), Fraction(1, 24)), 2: scl([5, -4, 2], Fraction(-1, 2)),
        3: scl([-8, 3, 1], Fraction(1, 2)), 4: [2, -2], 5: [1]},
}


def hval(F, q):
    return sum(evf(pol, q) * C1[q][i] for i, pol in F.items())


ok = True
for j in range(0, 9):
    for q in range(1, QM + 1):
        if hval(HF[j], q) != coef(q, 3 * q - 2 - j):
            ok = False
            L.out('  table6 j=%d fails at q=%d' % (j, q))
            break
L.check('r4-high-values', ok, 'j<=8, 1<=q<=%d：表 6 公式 == [x^{3q-2-j}]Num_q' % QM)

# 独立的符号证明（与核对模块不同的路线）：alpha_{q,j}=a_{q,j}/(q-1)!，E_r(n)=e_r(1,1/2,..,1/n)，
# c(q,i)=(q-1)! E_{i-1}(q-1)；把 (q-1)(q-2)[alpha_q-2alpha_{q-1}+alpha_{q-2}] - (q-2)alpha_{q-1,j-2}
#  - (q-1)(alpha_{q-2,j-3}-alpha_{q-2,j-2}) 全部化到 E_r(q-3) 基，检验系数多项式恒为 0。
def kshift(p, s):
    res = []
    for a in reversed(p):
        res = add(mul(res, [Fraction(s), Fraction(1)]), [Fraction(a)])
    return tr(res)


def residual(HFj, HFm2, HFm3):
    acc = {}

    def put(r, pol):
        if r < 0 or not pol:
            return
        acc[r] = add(acc.get(r, []), pol)
    qm1qm2 = [Fraction(2), Fraction(-3), Fraction(1)]       # (q-1)(q-2)
    for i, pol in HFj.items():
        r = i - 1
        P0 = [Fraction(a) for a in pol]
        # alpha_{q,j}: E_r(q-1) = E_r + (a+b)E_{r-1} + ab E_{r-2}，乘 (q-1)(q-2)
        put(r, mul(P0, qm1qm2))
        put(r - 1, mul(P0, [Fraction(-3), Fraction(2)]))   # 2q-3
        put(r - 2, P0)                                      # 1
        # -2 alpha_{q-1,j}: E_r(q-2) = E_r + a E_{r-1}；(q-1)(q-2)a = q-1
        P1 = kshift(P0, -1)
        put(r, scl(mul(P1, qm1qm2), -2))
        put(r - 1, scl(mul(P1, [Fraction(-1), Fraction(1)]), -2))
        # + alpha_{q-2,j}
        P2 = kshift(P0, -2)
        put(r, mul(P2, qm1qm2))
    for i, pol in HFm2.items():
        r = i - 1
        P0 = [Fraction(a) for a in pol]
        # -(q-2) alpha_{q-1,j-2}：(q-2)E_r(q-2) = (q-2)E_r + E_{r-1}
        P1 = kshift(P0, -1)
        put(r, scl(mul(P1, [Fraction(-2), Fraction(1)]), -1))
        put(r - 1, scl(P1, -1))
        # +(q-1) alpha_{q-2,j-2}
        P2 = kshift(P0, -2)
        put(r, mul(P2, [Fraction(-1), Fraction(1)]))
    for i, pol in HFm3.items():
        r = i - 1
        P2 = kshift([Fraction(a) for a in pol], -2)
        # -(q-1) alpha_{q-2,j-3}
        put(r, scl(mul(P2, [Fraction(-1), Fraction(1)]), -1))
    return {r: tr(p) for r, p in acc.items() if tr(p)}


def symbolic_ok(HFall, jmax):
    good_all = True
    for j in range(0, jmax + 1):
        res = residual(HFall[j], HFall.get(j - 2, {}), HFall.get(j - 3, {}))
        if res:
            good_all = False
            L.out('  symbolic residual nonzero j=%d: %s' % (j, sorted(res)))
        for q in (1, 2):
            if hval(HFall[j], q) != coef(q, 3 * q - 2 - j):
                good_all = False
    return good_all


L.check('r4-high-proof', symbolic_ok(HF, 8),
        'j<=8：表 6 代入归一化递推后在 E_r(q-3) 基下残差系数恒为 0（独立实现，与核对模块的 c(q-2,i) 基路线不同），q=1,2 初值吻合')

# 对照试验：故意改动一个系数，残差应非零（防止“恒真”检验）
HFbad = dict(HF)
HFbad[6] = dict(HF[6])
HFbad[6][4] = [Fraction(2)]
L.check('r4-high-proof-negctl', not symbolic_ok(HFbad, 6) or False, '阴性对照：把表 6 中 j=6 的 c_4 系数 1 改成 2，符号检验应失败（打印的残差即为预期失败）')

# =============== C4-28：j=9..12 的结构检验（模 p 拟合 + 有理重构 + 精确核对 + 符号证明）===============
P1, P2 = (1 << 61) - 1, (1 << 89) - 1


def solve_mod(rows, rhs, p):
    """模 p 高斯消元，返回 (是否相容, 秩, 解或 None)。"""
    n = len(rows[0])
    A = [[x % p for x in r] + [b % p] for r, b in zip(rows, rhs)]
    piv_cols = []
    r = 0
    for c in range(n):
        pr = next((i for i in range(r, len(A)) if A[i][c]), None)
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        piv_cols.append(c)
        r += 1
    consistent = all(not A[i][n] for i in range(r, len(A)))
    sol = [0] * n
    for k, c in enumerate(piv_cols):
        sol[c] = A[k][n]
    return consistent, r, sol


def ratrec(a, m):
    """有理重构：找 u/v ≡ a (mod m)，|u|,v <= sqrt(m/2)。"""
    a %= m
    r0, r1 = m, a
    s0, s1 = 0, 1
    bound = int((m // 2) ** 0.5)
    while r1 > bound:
        qq = r0 // r1
        r0, r1 = r1, r0 - qq * r1
        s0, s1 = s1, s0 - qq * s1
    if s1 == 0 or abs(s1) > bound:
        return None
    return Fraction(r1, s1)


HFext = dict(HF)
fit_ok = True
for j in range(9, 13):
    imax = j // 2 + 1
    D = 5
    cols = [(i, d) for i in range(1, imax + 1) for d in range(0, D + 1)]
    qs = list(range(1, 161))
    rows = [[q ** d * C1[q][i] for (i, d) in cols] for q in qs]
    rhs = [coef(q, 3 * q - 2 - j) for q in qs]
    c1, r1_, s1 = solve_mod(rows, rhs, P1)
    c2, r2_, s2 = solve_mod(rows, rhs, P2)
    L.out('# j=%d：未知数 %d，方程 %d；模 p1 相容=%s 秩=%d；模 p2 相容=%s 秩=%d' % (j, len(cols), len(qs), c1, r1_, c2, r2_))
    if not (c1 and c2 and r1_ == len(cols) and r2_ == len(cols)):
        fit_ok = False
        continue
    # CRT + 有理重构
    M = P1 * P2
    F = {}
    for k, (i, d) in enumerate(cols):
        a = (s1[k] * P2 * pow(P2, -1, P1) + s2[k] * P1 * pow(P1, -1, P2)) % M
        v = ratrec(a, M)
        if v is None:
            fit_ok = False
        F.setdefault(i, [Fraction(0)] * (D + 1))[d] = v if v is not None else Fraction(0)
    F = {i: tr(p) for i, p in F.items() if tr(p)}
    # 精确核对 q<=QM
    for q in range(1, QM + 1):
        if hval(F, q) != coef(q, 3 * q - 2 - j):
            fit_ok = False
            L.out('  j=%d exact check fails q=%d' % (j, q))
            break
    HFext[j] = F
    L.out('#   j=%d 拟合结果（i: 升幂系数）%s' % (j, {i: [str(c) for c in p] for i, p in sorted(F.items())}))
L.check('r4-high-fit-9-12', fit_ok, 'j=9..12：a_{q,j}=sum_{i<=floor(j/2)+1} pi_{j,i}(q)c(q,i)（deg pi<=5）在 q<=160 上模两素数满秩相容，有理重构后对 q<=%d 精确成立' % QM)
if fit_ok:
    L.check('r4-high-proof-9-12', symbolic_ok(HFext, 12), 'j<=12：拟合得到的公式代入递推后在 E_r(q-3) 基下残差恒为 0 且 q=1,2 初值吻合 ⇒ j<=12 均为已证明（计算机辅助）')
    # 结构子断言：a_{q,2m} 含 c(q,m+1) 系数 1；a_{q,2m+1} 含 (q-m) c(q,m+1)
    sub_ok = []
    for j in range(0, 13):
        m = j // 2
        top = HFext[j].get(m + 1, [])
        want = [Fraction(1)] if j % 2 == 0 else [Fraction(-m), Fraction(1)]
        sub_ok.append((j, tr([Fraction(c) for c in top]) == want))
    L.out('# 子断言「a_{q,2m}∋c(q,m+1)、a_{q,2m+1}∋(q-m)c(q,m+1)」逐 j 结果：%s' % sub_ok)
L.close(t0)
