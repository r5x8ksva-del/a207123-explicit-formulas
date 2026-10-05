# -*- coding: utf-8 -*-
"""check_c5a.py -- 子任务 c5a（C-5：渐近与 h_k 结构）的正式核对模块。

契约：从任意目录用 `py -3.14 <路径>` 运行；sys.path 插入 code 目录导入 core；
每条结论一行 "PASS <id> <描述>" 或 "FAIL <id> <描述>"；最后一行 "SUMMARY c5a pass=<n> fail=<n>"；
全部通过时退出码 0。
除标注 [numeric] 的条目（decimal 90 位，容差写在描述里）外，全部用精确整数 / Fraction。
所有"真值"都来自 core 的高度 DP（第 1 节原始定义的直接实现），并另用 core 的多重链 /
原题直接计数 / DFS 做锚定（c5a-anchor）。
"""
import os
import sys
import time
from fractions import Fraction
from math import factorial, comb, gcd
from decimal import Decimal, getcontext

CODE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, CODE)
from core import (U_fast_column, U_list, U_multichain, a_direct, N_from_U,  # noqa: E402
                  N_brute, allowed_rows)

getcontext().prec = 90
T0 = time.time()
RESULTS = []


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc))
    sys.stdout.flush()


def run(cid, fn):
    try:
        fn()
    except Exception as exc:  # 任何异常都记为 FAIL
        report(cid, False, 'exception: %r' % (exc,))


# ---------------------------------------------------------------------------
# 精确多项式小工具（系数全部转成 Fraction，避免 int/int 变成浮点）
# ---------------------------------------------------------------------------
def fr(p):
    return [Fraction(c) for c in p]


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(a, b):
    n = max(len(a), len(b))
    return trim([Fraction(a[i] if i < len(a) else 0) + Fraction(b[i] if i < len(b) else 0) for i in range(n)])


def pscale(a, c):
    return trim([Fraction(c) * Fraction(x) for x in a])


def psub(a, b):
    return padd(a, pscale(b, -1))


def pmul(a, b):
    if not a or not b:
        return []
    r = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += Fraction(x) * Fraction(y)
    return trim(r)


def peval(p, x):
    r = Fraction(0)
    for c in reversed(p):
        r = r * x + Fraction(c)
    return r


def pderiv(p):
    return trim([Fraction(i) * Fraction(p[i]) for i in range(1, len(p))])


def parg_shift(p, a):
    """p(k+a) 的系数。"""
    res = []
    for c in reversed(p):
        res = padd(pmul(res, [Fraction(a), Fraction(1)]), [Fraction(c)]) if res else [Fraction(c)]
    return trim(res)


def interp(xs, ys):
    n = len(xs)
    coef = [Fraction(y) for y in ys]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (xs[i] - xs[i - j])
    poly = []
    for i in range(n - 1, -1, -1):
        poly = padd(pmul(poly, [Fraction(-xs[i]), Fraction(1)]), [coef[i]]) if poly else [coef[i]]
    return trim(poly)


def ffall(n):
    """k(k-1)...(k-n+1) 作为 k 的多项式。"""
    p = [Fraction(1)]
    for i in range(n):
        p = pmul(p, [Fraction(-i), Fraction(1)])
    return p


def binom_poly(shift, r):
    """C(k+shift, r) 作为 k 的多项式。"""
    p = [Fraction(1)]
    for i in range(r):
        p = pmul(p, [Fraction(shift - i), Fraction(1)])
    return pscale(p, Fraction(1, factorial(r)))


def series_mul(a, b, n):
    r = [Fraction(0)] * n
    for i in range(min(len(a), n)):
        if a[i]:
            for j in range(min(len(b), n - i)):
                r[i + j] += Fraction(a[i]) * Fraction(b[j])
    return r


def series_inv(p, n):
    p = list(p) + [0] * max(0, n - len(p))
    r = [Fraction(0)] * n
    r[0] = Fraction(1) / Fraction(p[0])
    for k in range(1, n):
        s = Fraction(0)
        for i in range(1, k + 1):
            if p[i]:
                s += Fraction(p[i]) * r[k - i]
        r[k] = -s * r[0]
    return r


def b_poly(i):
    return trim(fr([1, -1, 0, -i]))


def P_poly(m):
    p = [Fraction(1)]
    for i in range(m + 1):
        p = pmul(p, b_poly(i))
    return p


def prim(p):
    p = trim(fr(p))
    if not p:
        return []
    den = 1
    for c in p:
        den = den * c.denominator // gcd(den, c.denominator)
    q = [int(c * den) for c in p]
    g = 0
    for c in q:
        g = gcd(g, abs(c))
    return [c // g for c in q]


def neg_rem(a, b):
    a = fr(a)
    b = fr(b)
    while len(a) >= len(b) and a:
        c = a[-1] / b[-1]
        d = len(a) - len(b)
        for i, bb in enumerate(b):
            a[i + d] -= c * bb
        a = trim(a)
    return prim([-c for c in a])


def sturm(p):
    p = prim(p)
    seq = [p, prim(pderiv(p))]
    while len(seq[-1]) > 1:
        r = neg_rem(seq[-2], seq[-1])
        if not r:
            break
        seq.append(r)
    return seq


def sign_changes(vals):
    vals = [v for v in vals if v != 0]
    return sum(1 for a, b in zip(vals, vals[1:]) if (a > 0) != (b > 0))


def sturm_count_all(seq):
    pinf = [s[-1] for s in seq]
    minf = [s[-1] * (-1) ** (len(s) - 1) for s in seq]
    return sign_changes(minf) - sign_changes(pinf)


def sturm_count_interval(seq, a, b):
    """(a, b] 内的不同实根数（a、b 不是根时）。"""
    va = sign_changes([peval(s, a) for s in seq])
    vb = sign_changes([peval(s, b) for s in seq])
    return va - vb


def sturm_count_above(seq, a):
    va = sign_changes([peval(s, a) for s in seq])
    return va - sign_changes([s[-1] for s in seq])


# ---------------------------------------------------------------------------
# 数据：全部来自 core 的高度 DP
# ---------------------------------------------------------------------------
K = 60
M = 60
COLS = {m: U_fast_column(m, K) for m in range(M + 1)}
T = [[COLS[m][k] for m in range(M + 1)] for k in range(K + 1)]
LONG = {m: U_fast_column(m, 3 * m + K + 10) for m in range(0, 21)}
NUM = {m: U_fast_column(m, 402) for m in range(0, 9)}
N = {(k, q): N_from_U(T, k, q) for k in range(0, K + 1) for q in range(0, k + 1)}


def Nv(k, q):
    if k < 0 or q < 0 or q > k:
        return 0
    return N[(k, q)]


def D(k, e):
    return Nv(k, k - e)


def gbinom(x, q):
    """C(x, q)，x 为任意整数（广义二项式），精确整数。"""
    num = 1
    for i in range(q):
        num *= (x - i)
    return num // factorial(q)


def Upoly(k, m):
    """多项式 U_k 在任意整数 m 处的值：U_k(m) = sum_q N(k,q) C(m+1,q)（k>=0）；约定 U_{-1}=1, U_{-2}=0。"""
    if k == -1:
        return 1
    if k <= -2:
        return 0
    return sum(N[(k, q)] * gbinom(m + 1, q) for q in range(0, k + 1))


def h_from_U(k):
    h = []
    for i in range(0, k + 1):
        h.append(sum((-1) ** (i - j) * comb(k + 1, i - j) * T[k][j] for j in range(0, i + 1)))
    return trim(fr(h)) or [Fraction(0)]


H = {k: h_from_U(k) for k in range(0, K + 1)}


def stir1u(nmax):
    c = [[0] * (nmax + 2) for _ in range(nmax + 2)]
    c[0][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            c[n][k] = (n - 1) * c[n - 1][k] + c[n - 1][k - 1]
    return c


C1 = stir1u(45)


# ---------------------------------------------------------------------------
# A. 固定 m、k -> oo
# ---------------------------------------------------------------------------
def chk_anchor():
    ok1 = all(U_list(m, 30) == U_fast_column(m, 30) for m in range(0, 9))
    ok2 = all(U_multichain(k, m) == T[k][m] for k in range(1, 9) for m in range(0, 6))
    ok3 = all(a_direct(n, k) == T[k][(n + 1) // 2] * T[k][n // 2] for k in range(1, 6) for n in range(0, 11))
    nb_ok = True
    for k in range(1, 8):
        br = N_brute(k)
        if [br.get(q, 0) for q in range(1, k + 1)] != [N[(k, q)] for q in range(1, k + 1)]:
            nb_ok = False
    report('c5a-anchor', ok1 and ok2 and ok3 and nb_ok,
           'fast height DP == reference U_list (m<=8,k<=30) == multichain (k<=8,m<=5); '
           'a_direct(n,k)==U_k(ceil n/2)U_k(floor n/2) (k<=5,n<=10); N incl-excl == DFS N_brute (k<=7)')


def chk_lemma1_poly():
    ok_basis = all(Upoly(k, m) == T[k][m] for k in range(0, K + 1) for m in range(0, M + 1))
    ok_rec = True
    for k in range(1, K + 1):
        for m in range(-25, M + 1):
            lhs = Upoly(k, m)
            rhs = Upoly(k, m - 1) + Upoly(k - 1, m) + m * Upoly(k - 3, m)
            if lhs != rhs:
                ok_rec = False
                break
    ok_m1 = all(Upoly(k, -1) == 0 for k in range(1, K + 1))
    # (1-x-m x^3) G_m = G_{m-1} + m x^2 for all integers m in [-20,20], coefficients k<=57
    ok_G = True
    for m in range(-20, 21):
        g = [Upoly(k, m) for k in range(0, 58)]
        gm1 = [Upoly(k, m - 1) for k in range(0, 58)]
        for k in range(0, 58):
            lhs = g[k] - (g[k - 1] if k >= 1 else 0) - m * (g[k - 3] if k >= 3 else 0)
            rhs = gm1[k] + (m if k == 2 else 0)
            if lhs != rhs:
                ok_G = False
    report('c5a-lemma1-Gm', ok_basis and ok_rec and ok_m1 and ok_G,
           'U_k(m)=sum_q N(k,q)C(m+1,q) (k,m<=60); Lemma1 holds as polynomial identity for m in [-25,60], k<=60; '
           'U_k(-1)=0; (1-x-m x^3)G_m = G_{m-1}+m x^2 for all integers m in [-20,20] (coeffs k<=57)')


def chk_WP():
    ok = True
    for m in range(0, 21):
        # W_m = 1 + x^2 sum_j j P_{j-1}
        W = [Fraction(1)]
        for j in range(1, m + 1):
            W = padd(W, pscale([Fraction(0), Fraction(0)] + P_poly(j - 1), j))
        Pm = P_poly(m)
        if m >= 1 and (len(W) - 1 != 3 * m or len(Pm) - 1 != 3 * m + 1):
            ok = False
        ser = series_mul(W, series_inv(Pm, K + 1), K + 1)
        if [int(c) for c in ser] != [LONG[m][k] for k in range(0, K + 1)] or any(c.denominator != 1 for c in ser):
            ok = False
    # P_m squarefree (m<=8): gcd(P_m, P_m') constant
    sqf = True
    for m in range(1, 9):
        a, b = P_poly(m), pderiv(P_poly(m))
        while b:
            # remainder
            a2 = list(a)
            while len(a2) >= len(b) and a2:
                c = a2[-1] / b[-1]
                d = len(a2) - len(b)
                for i, bb in enumerate(b):
                    a2[i + d] -= c * bb
                a2 = trim(a2)
            a, b = b, a2
        if len(a) != 1:
            sqf = False
    report('c5a-WP', ok and sqf,
           'G_m = W_m/P_m, W_m = 1 + x^2 sum_{j=1}^m j P_{j-1}, deg W_m = 3m < deg P_m = 3m+1 (m<=20, k<=60 vs DP); '
           'P_m squarefree (exact gcd, m<=8)')


def rho(m):
    if m == 0:
        return Decimal(1)
    y = Decimal(m) ** (Decimal(1) / Decimal(3)) + Decimal('0.5')
    for _ in range(400):
        y2 = y - (y ** 3 - y ** 2 - m) / (3 * y * y - 2 * y)
        if abs(y2 - y) < Decimal(10) ** (-86):
            return y2
        y = y2
    return y


RHO = {m: rho(m) for m in range(0, 31)}


def cm_dec(m, r=None):
    """c_m = rho (rho^{3m+1}/m! - e_{m-1}(rho^3)) / (3 rho - 2)，e_n(u)=sum_{i<=n} u^i/i!。"""
    if r is None:
        r = RHO[m]
    if m == 0:
        return Decimal(1)
    e = sum(r ** (3 * i) / factorial(i) for i in range(m))
    return r * (r ** (3 * m + 1) / factorial(m) - e) / (3 * r - 2)


CM = {m: cm_dec(m) for m in range(0, 31)}


def chk_roots():
    ok_one = True
    for j in range(1, 31):
        seq = sturm([-j, 0, -1, 1])
        if sturm_count_all(seq) != 1 or sturm_count_above(seq, Fraction(1)) != 1:
            ok_one = False
    ok_num = True
    for m in range(1, 31):
        if not (RHO[m] > RHO[m - 1] and m / RHO[m] < RHO[m - 1] ** 2 and m / RHO[m] < RHO[m] ** 2):
            ok_num = False
    report('c5a-roots', ok_one and ok_num,
           'y^3-y^2-j has exactly one real root rho_j, rho_j>1 (Sturm exact, j<=30); [numeric] rho_j increasing and '
           '|complex root|^2 = j/rho_j < rho_{j-1}^2 < rho_j^2 (j<=30); general proof in notes')


def ypow_table(j, n):
    tab = [(Fraction(1), Fraction(0), Fraction(0))]
    for _ in range(n):
        a0, a1, a2 = tab[-1]
        tab.append((j * a2, a0, a1 + a2))   # y^3 = y^2 + j
    return tab


def gt(j):
    d = {3 * j + 2: Fraction(1, factorial(j))}
    for i in range(j):
        d[3 * i] = d.get(3 * i, Fraction(0)) + Fraction(j - i, factorial(i))
    return d


def Lfun(poly, tab):
    return sum(c * tab[e][2] for e, c in poly.items())


TABS = {j: ypow_table(j, 260) for j in range(1, 21)}


def cseq(j, n):
    """c_j(n) = [x^n] 1/(1-x-j x^3)，n<0 时为 0。"""
    if n < 0:
        return 0
    a = [1, 1, 1]
    if n < 3:
        return 1
    for t in range(3, n + 1):
        a.append(a[-1] + j * a[-3])
    return a[n]


def chk_binet():
    ok = True
    for m in range(0, 21):
        for k in range(0, K + 1):
            tot = Fraction((-1) ** m, factorial(m))
            for j in range(1, m + 1):
                sh = k + 3 * (m - j)
                tot += Fraction((-1) ** (m - j), factorial(m - j)) * Lfun({e + sh: c for e, c in gt(j).items()}, TABS[j])
            if tot != LONG[m][k]:
                ok = False
    # c_j(n) form
    ok2 = True
    for m in range(0, 13):
        for k in range(0, K + 1):
            tot = Fraction(0)
            for j in range(0, m + 1):
                cj = 1 if j == 0 else cseq(j, k + 3 * m)
                tot += Fraction((-1) ** (m - j) * comb(m, j) * cj, factorial(m))
            for j in range(1, m + 1):
                for i in range(0, j):
                    tot += Fraction((-1) ** (m - j) * (j - i), factorial(m - j) * factorial(i)) * cseq(j, k + 3 * (m - j + i) - 2)
            if tot != LONG[m][k]:
                ok2 = False
    report('c5a-binet', ok and ok2,
           'exact spectral (Binet) formula U_k(m) = (-1)^m/m! + sum_{j=1}^m (-1)^{m-j}/(m-j)! * '
           'sum_{f_j(s)=0} gamma_j(s) s^{k+3(m-j)} via Lagrange functional [y^2](. mod f_j) (m<=20,k<=60); '
           'equivalent c_j(n)-form (m<=12,k<=60)')


def chk_filter():
    ok = True
    for m in range(1, 21):
        Pm1 = P_poly(m - 1)
        g = gt(m)
        for k in range(3 * m, 3 * m + K + 1):
            v = sum(Pm1[i] * LONG[m][k - i] for i in range(len(Pm1)) if k - i >= 0)
            rhs = factorial(m) * Lfun({e + k - 3 * m: c for e, c in g.items()}, TABS[m])
            if v != rhs:
                ok = False
    report('c5a-filter', ok,
           'rho_m-component: [x^k] P_{m-1}(x)G_m(x) == m! [y^2](gt_m(y) y^{k-3m} mod f_m) exactly, '
           '1<=m<=20, 3m<=k<=3m+60 (DP data)')


def reduce_mod(polyd, j):
    tab = ypow_table(j, max(polyd) + 1)
    v = [Fraction(0)] * 3
    for e, c in polyd.items():
        for t in range(3):
            v[t] += c * tab[e][t]
    return v


def chk_cm_form():
    ok = True
    for j in range(1, 21):
        lhs = reduce_mod(gt(j), j)
        rd = {3 * j + 3: Fraction(1, factorial(j))}
        for i in range(j):
            rd[3 * i + 2] = rd.get(3 * i + 2, Fraction(0)) - Fraction(1, factorial(i))
        if lhs != reduce_mod(rd, j):
            ok = False
    report('c5a-cm-form', ok,
           'algebraic identity gt_j(y) == y^2 (y^{3j+1}/j! - e_{j-1}(y^3)) mod y^3-y^2-j (j<=20), hence '
           'c_m = rho(rho^{3m+1}/m! - e_{m-1}(rho^3))/(3rho-2), gamma_j(s) same with s')


def solve3(A, b):
    A = [list(map(Fraction, row)) + [Fraction(bb)] for row, bb in zip(A, b)]
    for c in range(3):
        p = next(r for r in range(c, 3) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        for r in range(3):
            if r != c and A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [A[i][3] / A[i][i] for i in range(3)]


def cm_repr(m):
    g = reduce_mod(gt(m), m)
    cols = []
    for basis in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
        a0, a1, a2 = map(Fraction, basis)
        y1 = (m * a2, a0, a1 + a2)
        y2 = (m * y1[2], y1[0], y1[1] + y1[2])
        cols.append([3 * y2[t] - 2 * y1[t] for t in range(3)])
    A = [[cols[c][r] for c in range(3)] for r in range(3)]
    return solve3(A, g)


def fdec(x):
    return Decimal(x.numerator) / Decimal(x.denominator)


def chk_cm_repr():
    ok = True
    for m in range(1, 9):
        r = cm_repr(m)
        val = fdec(r[0]) + fdec(r[1]) * RHO[m] + fdec(r[2]) * RHO[m] ** 2
        if abs(val - CM[m]) > Decimal(10) ** (-70) * CM[m]:
            ok = False
    r1 = cm_repr(1)
    ok = ok and r1 == [Fraction(10, 31), Fraction(15, 31), Fraction(17, 31)]
    report('c5a-cm-repr', ok,
           'c_m in Q(rho_m): exact r_m(y) = gt_m(y)/f_m\'(y) mod f_m, e.g. c_1 = (10+15rho+17rho^2)/31; '
           '[numeric] r_m(rho_m) == closed form to 1e-70 (m<=8)')


def chk_c4():
    c4 = Fraction(2) * (Fraction(2 ** 13, 24) - sum(Fraction(8 ** i, factorial(i)) for i in range(4))) / (3 * 2 - 2)
    r = cm_repr(4)
    c4b = r[0] + 2 * r[1] + 4 * r[2]
    Pm = P_poly(4)
    # Q = P_4/(1-2x)：按升幂做综合除法 Q[i] = P[i] + 2 Q[i-1]，再用乘回检验整除
    Q = [Fraction(0)] * (len(Pm) - 1)
    acc = Fraction(0)
    for i in range(len(Pm) - 1):
        acc = Pm[i] + 2 * acc
        Q[i] = acc
    okdiv = trim(pmul(Q, fr([1, -2]))) == trim(Pm)
    vals = set()
    for k in range(12, 12 + K + 1):
        v = sum(Q[i] * LONG[4][k - i] for i in range(len(Q)) if k - i >= 0)
        vals.add(Fraction(v) / 2 ** k)
    W = [Fraction(1)]
    for j in range(1, 5):
        W = padd(W, pscale([Fraction(0), Fraction(0)] + P_poly(j - 1), j))
    W_half = peval(W, Fraction(1, 2))
    ok = okdiv and len(vals) == 1 and vals.pop() == W_half == Fraction(645, 512) and \
        W_half / peval(Q, Fraction(1, 2)) == c4 == c4b == Fraction(215, 2)
    report('c5a-c4', ok, 'rho_4=2, c_4 = 215/2 exactly: closed form == Q(rho) representation == DP filter '
                         '[x^k](P_4/(1-2x) * G_4)/2^k == W_4(1/2) = 645/512 for 12<=k<=72, c_4 = W_4(1/2)/Q(1/2)')


C18 = Fraction(37105325714711350249401, 6830759936000)


def chk_c18():
    c18 = Fraction(3) * (Fraction(3 ** 55, factorial(18)) - sum(Fraction(27 ** i, factorial(i)) for i in range(18))) / 7
    r = cm_repr(18)
    c18b = r[0] + 3 * r[1] + 9 * r[2]
    Pm = P_poly(18)
    Q = [Fraction(0)] * (len(Pm) - 1)
    acc = Fraction(0)
    for i in range(len(Pm) - 1):
        acc = Pm[i] + 3 * acc
        Q[i] = acc
    okdiv = trim(pmul(Q, fr([1, -3]))) == trim(Pm)
    vals = set()
    for k in range(54, 54 + K + 1):
        v = sum(Q[i] * LONG[18][k - i] for i in range(len(Q)) if k - i >= 0)
        vals.add(Fraction(v) / 3 ** k)
    W = [Fraction(1)]
    for j in range(1, 19):
        W = padd(W, pscale([Fraction(0), Fraction(0)] + P_poly(j - 1), j))
    W3 = peval(W, Fraction(1, 3))
    ok = okdiv and len(vals) == 1 and vals.pop() == W3 and W3 / peval(Q, Fraction(1, 3)) == c18 == c18b == C18
    report('c5a-c18', ok, 'rho_18=3, c_18 = 37105325714711350249401/6830759936000 (~5.4320933633e9) exactly: closed form '
                          '== Q(rho) representation == DP filter (54<=k<=114)')


def chk_asym_num():
    allok = True
    for m in range(1, 9):
        U = NUM[m]
        r, c = RHO[m], CM[m]
        theta = RHO[m - 1] / r
        kappa = CM[m - 1] * RHO[m - 1] ** 3 / c
        e = [Decimal(U[k]) / (c * r ** k) - 1 for k in range(402)]
        neg = all(x < 0 for x in e[:401])
        rate60 = e[61] / e[60]
        rate400 = e[401] / e[400]
        two60 = (Decimal(U[60]) - c * r ** 60) / (-CM[m - 1] * RHO[m - 1] ** 63)
        two400 = (Decimal(U[400]) - c * r ** 400) / (-CM[m - 1] * RHO[m - 1] ** 403)
        ok = neg and abs(rate400 - theta) < Decimal('1e-6') and abs(two400 - 1) < Decimal('1e-5') and \
            abs(rate60 - theta) < Decimal('0.006')
        allok = allok and ok
        report('c5a-asym-m%d' % m, ok,
               '[numeric, decimal 90 digits] m=%d rho=%.12f c_m=%.10f theta=rho_{m-1}/rho_m=%.9f kappa=%.6f: '
               'e_k=U_k/(c rho^k)-1 <0 for k<=400; e_20=%.3e e_40=%.3e e_60=%.3e; rate e61/e60=%.6f (tol 6e-3); '
               'rate e401/e400=%.9f (tol 1e-6); two-term ratio k=60: %.6f, k=400: %.9f (tol 1e-5)'
               % (m, r, c, theta, kappa, e[20], e[40], e[60], rate60, rate400, two60, two400))


def chk_asym_m18():
    U = U_fast_column(18, 2001)
    c18 = fdec(C18)
    theta = RHO[17] / 3
    kappa = CM[17] * RHO[17] ** 3 / c18
    e = lambda k: Decimal(U[k]) / (c18 * Decimal(3) ** k) - 1
    rate = e(2000) / e(1999)
    two = e(1999) / (-kappa * theta ** 1999)
    ok = abs(rate - theta) < Decimal('1e-8') and abs(two - 1) < Decimal('1e-8') and abs(e(1999)) < Decimal('1e-13')
    report('c5a-asym-m18', ok, '[numeric] m=18: theta=rho_17/3=%.10f, e_60=%.3e, e_500=%.3e, e_1999=%.3e, '
                               'rate=%.10f (tol 1e-8), two-term ratio=%.10f (tol 1e-8)'
           % (theta, e(60), e(500), e(1999), rate, two))


def chk_prompt_k40():
    lines = []
    ok = True
    for m in (2, 3):
        U = NUM[m]
        r = RHO[m]
        theta = RHO[m - 1] / r
        kappa = CM[m - 1] * RHO[m - 1] ** 3 / CM[m]
        ratio_err = Decimal(U[41]) / Decimal(U[40]) / r - 1
        pred = kappa * (1 - theta) * theta ** 40
        root_err = Decimal(U[40]) ** (Decimal(1) / Decimal(40)) / r - 1
        lvl_err = Decimal(U[40]) / (CM[m] * r ** 40) - 1
        ok = ok and 0 < ratio_err < Decimal('0.004') and abs(ratio_err / pred - 1) < Decimal('0.1') and root_err > Decimal('0.05')
        lines.append('m=%d: U41/U40 rel.err=%.3e (theory kappa(1-theta)theta^40=%.3e), U40^(1/40) rel.err=%.3e, '
                     'U40/(c rho^40)-1=%.3e' % (m, ratio_err, pred, root_err, lvl_err))
    report('c5a-prompt-k40', ok, '[numeric] prompt claim "<0.4% at k=40" matches the successive ratio U_{k+1}/U_k '
                                 '(within 10%% of theory), not U_k^(1/k): ' + '; '.join(lines))


# ---------------------------------------------------------------------------
# B. 固定 k、m -> oo
# ---------------------------------------------------------------------------
def chk_Ntri():
    ok = True
    for k in range(3, K + 1):
        for r in range(0, k):
            lhs = Nv(k, r + 1)
            rhs = Nv(k - 1, r) + Nv(k - 1, r + 1) + r * (Nv(k - 3, r - 1) + 2 * Nv(k - 3, r) + Nv(k - 3, r + 1))
            if lhs != rhs:
                ok = False
    report('c5a-Ntri', ok, 'N triangle recurrence (first occurrence of the maximum) vs N from DP, 3<=k<=60')


P0 = fr([2])
P1 = fr([-4, -1, 1])
P2 = [Fraction(c, 4) for c in (164, -98, 43, -10, 1)]
P3 = [Fraction(c, 24) for c in (11088, -17392, 8560, -2225, 331, -27, 1)]
PD = [P0, P1, P2, P3]


def chk_D0123():
    # symbolic step identities
    d2 = padd(parg_shift(P1, -1), pmul(fr([-3, 1]), padd(parg_shift(P1, -3), pscale(P0, 2))))
    d3 = padd(parg_shift(P2, -1), pmul(fr([-4, 1]), padd(padd(parg_shift(P2, -3), pscale(parg_shift(P1, -3), 2)), P0)))
    d1 = padd(parg_shift(P0, -1), pmul(fr([-2, 1]), parg_shift(P0, -3)))
    id1 = trim(psub(psub(P1, parg_shift(P1, -1)), d1)) == []
    id2 = trim(psub(psub(P2, parg_shift(P2, -1)), d2)) == []
    id3 = trim(psub(psub(P3, parg_shift(P3, -1)), d3)) == []
    base = peval(P1, 4) == D(4, 1) and peval(P2, 6) == D(6, 2) and peval(P3, 8) == D(8, 3)
    data = all(D(k, 0) == 2 for k in range(2, K + 1)) and \
        all(peval(PD[d], k) == D(k, d) for d in (1, 2, 3) for k in range(2 * d + 2, K + 1))
    defect = all(peval(PD[d], 2 * d + 1) - D(2 * d + 1, d) == (-1) ** d * factorial(d + 1) for d in (0, 1, 2, 3))
    report('c5a-D0123', id1 and id2 and id3 and base and data and defect,
           'N(k,k)=2 (k>=2); N(k,k-1)=k^2-k-4 (k>=4); N(k,k-2)=(k^4-10k^3+43k^2-98k+164)/4 (k>=6); '
           'N(k,k-3)=(k^6-27k^5+331k^4-2225k^3+8560k^2-17392k+11088)/24 (k>=8): symbolic step identities exact, '
           'base values, data k<=60; defect p_d(2d+1)-N(2d+1,d+1) = (-1)^d (d+1)! (d<=3)')


def chk_Dgen():
    ok = True
    info = []
    for d in range(1, 12):
        xs = list(range(2 * d + 2, 4 * d + 3))
        p = interp(xs, [D(x, d) for x in xs])
        good = all(peval(p, k) == D(k, d) for k in range(2 * d + 2, K + 1))
        lc = p[-1] == Fraction(2, 2 ** d * factorial(d)) and len(p) - 1 == 2 * d
        dfc = peval(p, 2 * d + 1) - D(2 * d + 1, d) == (-1) ** d * factorial(d + 1)
        ok = ok and good and lc and dfc
    report('c5a-Dgen', ok, 'for d<=11: N(k,k-d) equals a degree-2d polynomial with lc 2/(2^d d!) exactly for '
                           '2d+2<=k<=60, and p_d(2d+1)-N(2d+1,d+1) = (-1)^d (d+1)! (threshold 2d+2 sharp)')


# 由前向差分（与 N 无关）求 U_k(m) 关于 m 的系数
def coeffs_by_diff(k):
    vals = [T[k][m] for m in range(k + 1)]
    diffs = []
    cur = vals[:]
    for q in range(k + 1):
        diffs.append(cur[0])
        cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
    c = [Fraction(0)] * (k + 1)
    for q in range(k + 1):
        if diffs[q] == 0:
            continue
        p = ffall(q)
        for j, a in enumerate(p):
            c[j] += Fraction(diffs[q]) * a / factorial(q)
    return c


COEF = {k: coeffs_by_diff(k) for k in range(0, K + 1)}
B1 = fr([-1, -2, 1])
B2 = [Fraction(c, 12) for c in (422, -313, 162, -36, 3)]
B3 = [Fraction(c, 24) for c in (13380, -19331, 9570, -2533, 379, -30, 1)]
BD = [fr([2]), B1, B2, B3]
ET = [fr([1]), [Fraction(-3, 2), Fraction(1, 2)], pscale(pmul(fr([-2, 1]), fr([-13, 3])), Fraction(1, 24)),
      pscale(pmul(fr([-3, 1]), fr([8, -7, 1])), Fraction(1, 48))]


def esym(j, n):
    row = [1] + [0] * j
    for v in range(-1, n - 1):
        for t in range(j, 0, -1):
            row[t] += v * row[t - 1]
    return row[j]


def chk_mcoef():
    ok_top = all(COEF[k][k] == Fraction(2, factorial(k)) for k in range(2, K + 1))
    ok_e = all(esym(j, n) == peval(pmul(ffall(j), ET[j]), n) for j in range(0, 4) for n in range(0, 70))
    ok_id = True
    for d in range(1, 4):
        for k in range(d, K + 1):
            Bk = COEF[k][k - d] * factorial(k - d)
            rhs = sum((-1) ** (d - e) * D(k, e) * peval(ET[d - e], k - e) for e in range(0, d + 1))
            if Bk != rhs:
                ok_id = False
    ok_poly = all(COEF[k][k - d] * factorial(k - d) == peval(BD[d], k) for d in (1, 2, 3) for k in range(2 * d + 2, K + 1))
    ok_dfc = all(COEF[2 * d + 1][d + 1] * factorial(d + 1) - peval(BD[d], 2 * d + 1) == (-1) ** (d + 1) * factorial(d + 1)
                 for d in (1, 2, 3))
    k3 = COEF[3][2]
    report('c5a-mcoef', ok_top and ok_e and ok_id and ok_poly and ok_dfc,
           '[m^k]U_k=2/k! (k>=2); [m^{k-1}]U_k=(k^2-2k-1)/(k-1)! (k>=4; k=3 gives %s); '
           '[m^{k-2}]U_k=(3k^4-36k^3+162k^2-313k+422)/(12 (k-2)!) (k>=6); '
           '[m^{k-3}]U_k=(k^6-30k^5+379k^4-2533k^3+9570k^2-19331k+13380)/(24 (k-3)!) (k>=8); coefficients from '
           'forward differences of DP (k<=60); identity B_d(k)=sum_e (-1)^{d-e}N(k,k-e) et_{d-e}(k-e) (k<=60); '
           'defect at k=2d+1 equals (-1)^{d+1}(d+1)!' % k3)


def chk_mcoef_gen():
    ok = True
    for d in range(1, 12):
        xs = list(range(2 * d + 2, 4 * d + 3))
        Bv = {k: COEF[k][k - d] * factorial(k - d) for k in range(d, K + 1)}
        p = interp(xs, [Bv[x] for x in xs])
        good = all(peval(p, k) == Bv[k] for k in range(2 * d + 2, K + 1))
        lc = len(p) - 1 == 2 * d and p[-1] == Fraction(1, 2 ** (d - 1) * factorial(d))
        dfc = Bv[2 * d + 1] - peval(p, 2 * d + 1) == (-1) ** (d + 1) * factorial(d + 1)
        ok = ok and good and lc and dfc
    report('c5a-mcoef-gen', ok, 'for d<=11: (k-d)! [m^{k-d}]U_k(m) is a degree-2d polynomial in k with lc '
                                '1/(2^(d-1) d!) exactly for 2d+2<=k<=60, failing at k=2d+1 by (-1)^(d+1)(d+1)!')


# ---------------------------------------------------------------------------
# C. h_k(t)
# ---------------------------------------------------------------------------
def chk_h_def():
    ok_tail = all(sum((-1) ** (i - j) * comb(k + 1, i - j) * T[k][j] for j in range(0, i + 1)) == 0
                  for k in range(0, K) for i in range(k + 1, K + 1))
    ok_N = True
    for k in range(1, K + 1):
        s = []
        for q in range(1, k + 1):
            term = [Fraction(N[(k, q)])]
            term = pmul(term, [Fraction(0)] * (q - 1) + [Fraction(1)])
            for _ in range(k - q):
                term = pmul(term, fr([1, -1]))
            s = padd(s, term)
        if trim(s) != trim(H[k]):
            ok_N = False
    hh = {0: fr([1]), 1: fr([1]), 2: fr([1, 1])}
    ok_rec = H[0] == hh[0] and H[1] == hh[1] and H[2] == hh[2]
    for k in range(3, K + 1):
        nxt = padd(H[k - 1], pmul(fr([0, 1, -1]), padd(pmul(fr([1, -1]), pderiv(H[k - 3])), pscale(H[k - 3], k - 2))))
        if trim(nxt) != trim(H[k]):
            ok_rec = False
    ok_inv = all(sum(H[k][i] * gbinom(m - i + k, k) for i in range(len(H[k]))) == T[k][m]
                 for k in range(0, K + 1) for m in range(0, M + 1))
    report('c5a-h-def', ok_tail and ok_N and ok_rec and ok_inv,
           'h_k from DP: sum_m U_k(m)t^m=h_k/(1-t)^{k+1}, deg<=k (k<=60); h_k=sum_q N(k,q)t^{q-1}(1-t)^{k-q}; '
           'recurrence h_k=h_{k-1}+t(1-t)[(1-t)h\'_{k-3}+(k-2)h_{k-3}] (3<=k<=60) needs h_0=1,h_1=1,h_2=1+t; '
           'inverse U_k(m)=sum_i h_{k,i} C(m-i+k,k) (k,m<=60)')


def chk_h_01():
    ok = all(peval(H[k], 0) == 1 for k in range(0, K + 1)) and all(peval(H[k], 1) == 2 for k in range(2, K + 1))
    report('c5a-h-01', ok, 'h_k(0)=1 (k<=60), h_k(1)=N(k,k)=2 (2<=k<=60)')


def gneg_polys(jmax):
    G = {1: fr([1])}
    for j in range(1, jmax):
        G[j + 1] = padd(pmul(fr([1, -1, 0, j]), G[j]), fr([0, 0, j]))
    return G


GN = gneg_polys(22)


def chk_Gneg():
    ok = True
    for j in range(1, 22):
        g = GN[j]
        for k in range(0, K + 1):
            if Upoly(k, -j) != (g[k] if k < len(g) else 0):
                ok = False
    okb = True
    for j in range(2, 22):
        g = GN[j]
        if len(g) - 1 != 3 * j - 3:
            okb = False
        exp = {3 * j - 3: factorial(j - 1), 3 * j - 4: factorial(j - 1), 3 * j - 5: -C1[j][2],
               3 * j - 6: factorial(j - 1), 3 * j - 7: C1[j][2] + C1[j][3], 3 * j - 8: factorial(j - 1) - C1[j][2] - C1[j][3]}
        for e, v in exp.items():
            if e >= 0 and g[e] != v:
                okb = False
    report('c5a-Gneg', ok and okb,
           'G_{-j}(x):=sum_k U_k(-j)x^k is a polynomial: G_{-1}=1, G_{-j-1}=(1-x+jx^3)G_{-j}+jx^2 (j<=21,k<=60 vs DP '
           'polynomials); deg=3j-3, top coefficients (j-1)!,(j-1)!,-c(j,2),(j-1)!,c(j,2)+c(j,3),(j-1)!-c(j,2)-c(j,3) '
           '(c = unsigned Stirling 1st kind; 2<=j<=21)')


def lead_pred(k):
    a, r = divmod(k, 3)
    if r == 0:
        return (-1) ** a * factorial(a)
    if r == 2:
        return (-1) ** a * factorial(a + 1)
    return (-1) ** a * C1[a + 2][2]


def second_pred(k):
    a, r = divmod(k, 3)
    if r == 0:
        return (-1) ** (a + 1) * 2 * a * factorial(a)
    if r == 2:
        return (-1) ** a * (C1[a + 3][2] + C1[a + 3][3] - 3 * (a + 1) * factorial(a + 1))
    return (-1) ** a * (C1[a + 3][3] + C1[a + 3][2] - factorial(a + 2) - (3 * a + 2) * C1[a + 2][2])


def chk_h_deg_lead():
    ok_rec = True
    for k in range(0, K + 1):
        h = H[k]
        for j in range(1, 26):
            val = (-1) ** k * sum(h[i] * comb(i + j - 1, k) for i in range(len(h)) if i > k - j)
            if val != Upoly(k, -j):
                ok_rec = False
    ok_deg = all(len(H[k]) - 1 == (2 * k) // 3 for k in range(1, K + 1))
    ok_lead = all(H[k][-1] == lead_pred(k) for k in range(1, K + 1))
    ok_sec = all(H[k][-2] == second_pred(k) for k in range(3, K + 1))
    ok_zero = all(Upoly(k, -j) == 0 for k in range(1, K + 1) for j in range(1, (k + 2) // 3 + 1)) and \
        all(Upoly(k, -((k + 2) // 3) - 1) != 0 for k in range(1, K + 1))
    report('c5a-h-deg-lead', ok_rec and ok_deg and ok_lead and ok_sec and ok_zero,
           'reciprocity U_k(-j)=(-1)^k sum_{i>k-j} h_{k,i}C(i+j-1,k) (k<=60,j<=25); U_k(-j)=0 exactly for '
           '1<=j<=floor((k+2)/3); deg h_k=floor(2k/3); lead coeff (k=3a:(-1)^a a!, 3a+1:(-1)^a c(a+2,2), '
           '3a+2:(-1)^a (a+1)!) (1<=k<=60); second-top coeff closed form (3<=k<=60)')


def chk_mobius():
    ok = True
    vals = []
    for k in range(1, 11):
        rows = sorted(allowed_rows(k), key=sum)
        mu = {}
        zero = tuple([0] * k)
        for r in rows:
            if r == zero:
                mu[r] = 1
                continue
            mu[r] = -sum(mu[q] for q in rows if q in mu and q != r and all(a <= b for a, b in zip(q, r)))
        m01 = mu[tuple([1] * k)]
        hall = sum((-1) ** q * N[(k, q)] for q in range(0, k + 1))
        vals.append(m01)
        if not (m01 == Upoly(k, -2) == hall):
            ok = False
    ok = ok and all(v == 0 for v in vals[3:])
    report('c5a-mobius', ok, 'Moebius function of the poset of allowed rows: mu(0^,1^) == sum_q (-1)^q N(k,q) == '
                             'U_k(-2) (k<=10): values %s; = 0 for k>=4' % vals)


def chk_h_t1():
    ok1 = all(H[k][1] == T[k][1] - k - 1 for k in range(2, K + 1))
    den = pmul(pmul(fr([1, -1]), fr([1, -1])), fr([1, -1, 0, -1]))
    ser = series_mul(fr([0, 0, 1, -1, 1]), series_inv(den, K + 1), K + 1)
    ok2 = all(ser[k] == (H[k][1] if len(H[k]) > 1 else 0) for k in range(0, K + 1))
    ok3 = all(H[k][1] > 0 for k in range(2, K + 1))
    report('c5a-h-t1', ok1 and ok2 and ok3,
           '[t^1]h_k = R_k-k-1 = [x^k] x^2(1-x+x^2)/((1-x)^2(1-x-x^3)) > 0 (2<=k<=60)')


def chk_h_deriv():
    def der(p, d):
        for _ in range(d):
            p = pderiv(p)
        return peval(p, 1) if p else 0
    ok_gen = all(der(H[k], d) == factorial(d) * sum((-1) ** e * comb(k - 1 - e, d - e) * D(k, e)
                                                    for e in range(0, d + 1) if k - 1 - e >= d - e)
                 for k in range(1, K + 1) for d in range(0, 4))
    q1 = fr([2, 3, -1])
    q2 = [Fraction(c, 2) for c in (140, -102, 59, -14, 1)]
    q3 = [Fraction(c, 4) for c in (-13800, 20060, -10054, 2743, -421, 33, -1)]
    ok_poly = all(der(H[k], 1) == peval(q1, k) for k in range(4, K + 1)) and \
        all(der(H[k], 2) == peval(q2, k) for k in range(6, K + 1)) and \
        all(der(H[k], 3) == peval(q3, k) for k in range(8, K + 1))
    report('c5a-h-deriv', ok_gen and ok_poly,
           'h_k^{(d)}(1) = d! sum_{e<=d} (-1)^e C(k-1-e,d-e) N(k,k-e) (d<=3,k<=60); h\'(1)=-(k^2-3k-2) (k>=4); '
           'h\'\'(1)=(k^4-14k^3+59k^2-102k+140)/2 (k>=6); '
           'h\'\'\'(1)=(-k^6+33k^5-421k^4+2743k^3-10054k^2+20060k-13800)/4 (k>=8)')


def chk_H_pde():
    ok = True
    for k in range(0, K + 1):
        lhs = psub(H[k], H[k - 1]) if k >= 1 else list(H[0])
        if k >= 3:
            n = k - 3
            inner = padd(pmul(fr([1, -1]), pderiv(H[n])), pscale(H[n], n + 1))
            lhs = psub(lhs, pmul(fr([0, 1, -1]), inner))
        rhs = fr([1]) if k == 0 else (fr([0, 1]) if k == 2 else [])
        if trim(lhs) != trim(rhs):
            ok = False
    report('c5a-H-pde', ok, 'H(z,t)=sum_k h_k(t)z^k satisfies (1-z)H - t(1-t)z^3[(1-t)H_t + H + zH_z] = 1 + t z^2 '
                            '(coefficients z^k, k<=60); H(z,t)=(1-t)F(z(1-t),t)')


def chk_h_real():
    ok = True
    ok01 = True
    okdesc = True
    for k in range(2, K + 1):
        seq = sturm(H[k])
        d = len(H[k]) - 1
        if sturm_count_all(seq) != d or len(seq[-1]) != 1:
            ok = False
        if sturm_count_interval(seq, Fraction(-1, 10 ** 30), Fraction(1)) != 0 or peval(H[k], 0) == 0:
            ok01 = False
        npos = sturm_count_above(seq, Fraction(1))
        if sign_changes(H[k]) != npos:
            okdesc = False
    oklc = all(N[(k, q)] ** 2 >= N[(k, q - 1)] * N[(k, q + 1)] for k in range(3, K + 1) for q in range(2, k))
    okmult = True
    for k in range(1, K + 1):
        p = [Fraction(N[(k, q)]) for q in range(1, k + 1)]
        mlt = 0
        while len(p) > 1 and peval(p, -1) == 0:
            outc = []
            acc = Fraction(0)
            for c in reversed(p):
                acc = -acc + c
                outc.append(acc)
            outc.pop()
            p = list(reversed(outc))
            mlt += 1
        if mlt != -(-k // 3) - 1:
            okmult = False
    report('c5a-h-real', ok and ok01 and okdesc and oklc and okmult,
           'h_k real-rooted with simple roots (Sturm, exact, 2<=k<=60); no roots in [0,1] (also proved); '
           '#sign changes of coeffs == #roots>1 (Descartes, k<=60); N(k,.) log-concave (k<=60); '
           'z=-1 is a root of sum_q N(k,q)z^(q-1) of multiplicity exactly ceil(k/3)-1 (k<=60)')


def isolate_roots(p, width):
    """用 Sturm 序列 + 有理二分把 p 的实根隔离成宽度 < width 的区间 (a,b]（端点不是根）。"""
    seq = sturm(p)
    bound = 1 + max(abs(Fraction(c) / Fraction(p[-1])) for c in p[:-1])   # Cauchy 根界
    stack = [(-bound - 1, bound + 1)]
    out = []
    while stack:
        a, b = stack.pop()
        n = sturm_count_interval(seq, a, b)
        if n == 0:
            continue
        if n == 1 and b - a < width:
            out.append((a, b))
            continue
        mid = (a + b) / 2
        if peval(p, mid) == 0:
            mid += (b - a) / 7
        stack.append((a, mid))
        stack.append((mid, b))
    return sorted(out)


def chk_no_interlace():
    """反驳"相邻 h_k、h_{k+1} 的根交错"：隔离区间两两不交时，根的先后顺序是确定的。"""
    bad = []
    for k in range(2, 13):
        ra = isolate_roots(H[k], Fraction(1, 10 ** 9))
        rb = isolate_roots(H[k + 1], Fraction(1, 10 ** 9))
        ivs = sorted([(a, b, 0) for a, b in ra] + [(a, b, 1) for a, b in rb])
        disjoint = all(ivs[i][1] < ivs[i + 1][0] for i in range(len(ivs) - 1))
        labs = [l for _, _, l in ivs]
        alternating = all(labs[i] != labs[i + 1] for i in range(len(labs) - 1))
        if not disjoint or alternating or len(ra) != len(H[k]) - 1 or len(rb) != len(H[k + 1]) - 1:
            bad.append(k)
    report('c5a-h-nointerlace', not bad,
           'refutation: roots of h_k and h_{k+1} do NOT interlace for every 2<=k<=12 (exact Sturm isolation, '
           'pairwise-disjoint rational intervals of width <1e-9); explore script shows the same for k<=35; bad=%s' % bad)


def chk_fixed_i():
    thr = {1: 2, 2: 8, 3: 16, 4: 24, 5: 33, 6: 41, 7: 50, 8: 59}
    ok = True
    for i, t in thr.items():
        pos = all(len(H[k]) > i and H[k][i] > 0 for k in range(t, K + 1))
        before = len(H[t - 1]) <= i or H[t - 1][i] <= 0
        ok = ok and pos and before
    report('c5a-h-fixed-i', ok, '[t^i]h_k > 0 exactly from k = 2,8,16,24,33,41,50,59 (i=1..8) up to k=60 '
                                '(nonpositive at the previous k); asymptotically [t^i]h_k ~ c_i rho_i^k (proved)')


def nullspace_dim(rows, ncols):
    A = [list(map(Fraction, r)) for r in rows]
    rank = 0
    col = 0
    nr = len(A)
    for c in range(ncols):
        p = next((i for i in range(rank, nr) if A[i][c] != 0), None)
        if p is None:
            continue
        A[rank], A[p] = A[p], A[rank]
        for i in range(nr):
            if i != rank and A[i][c] != 0:
                f = A[i][c] / A[rank][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[rank])]
        rank += 1
        if rank == nr:
            break
    return ncols - rank


def chk_h_m1():
    seq = [peval(H[k], -1) for k in range(0, K + 1)]
    found = []
    for order in range(1, 16):
        rows = [[seq[k - i] for i in range(order + 1)] for k in range(2 + order, K + 1)]
        if nullspace_dim(rows, order + 1) > 0:
            found.append(('C', order))
    for order in range(1, 6):
        for deg in range(0, 7):
            ncols = (order + 1) * (deg + 1)
            rows = [[Fraction(k) ** dd * seq[k - i] for i in range(order + 1) for dd in range(deg + 1)]
                    for k in range(2 + order, K + 1)]
            if len(rows) < ncols + 5:
                continue
            if nullspace_dim(rows, ncols) > 0:
                found.append(('P', order, deg))
    report('c5a-h-m1', not found, 'search result (not a theorem): h_k(-1) (k<=60) satisfies no constant-coefficient '
                                  'recurrence of order<=15 and no polynomial-coefficient recurrence of order<=5, '
                                  'degree<=6 (with >=5 surplus equations); found=%s' % found)


CHECKS = [
    ('c5a-anchor', chk_anchor), ('c5a-lemma1-Gm', chk_lemma1_poly), ('c5a-WP', chk_WP),
    ('c5a-roots', chk_roots), ('c5a-binet', chk_binet), ('c5a-filter', chk_filter),
    ('c5a-cm-form', chk_cm_form), ('c5a-cm-repr', chk_cm_repr), ('c5a-c4', chk_c4), ('c5a-c18', chk_c18),
    ('c5a-asym', chk_asym_num), ('c5a-asym-m18', chk_asym_m18), ('c5a-prompt-k40', chk_prompt_k40),
    ('c5a-Ntri', chk_Ntri), ('c5a-D0123', chk_D0123), ('c5a-Dgen', chk_Dgen), ('c5a-mcoef', chk_mcoef),
    ('c5a-mcoef-gen', chk_mcoef_gen), ('c5a-h-def', chk_h_def), ('c5a-h-01', chk_h_01), ('c5a-Gneg', chk_Gneg),
    ('c5a-h-deg-lead', chk_h_deg_lead), ('c5a-mobius', chk_mobius), ('c5a-h-t1', chk_h_t1),
    ('c5a-h-deriv', chk_h_deriv), ('c5a-H-pde', chk_H_pde), ('c5a-h-real', chk_h_real),
    ('c5a-h-nointerlace', chk_no_interlace), ('c5a-h-fixed-i', chk_fixed_i), ('c5a-h-m1', chk_h_m1),
]

if __name__ == '__main__':
    for cid, fn in CHECKS:
        run(cid, fn)
    npass = sum(RESULTS)
    nfail = len(RESULTS) - npass
    print('SUMMARY c5a pass=%d fail=%d' % (npass, nfail))
    sys.exit(0 if nfail == 0 else 1)
