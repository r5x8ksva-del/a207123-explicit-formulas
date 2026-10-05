# -*- coding: utf-8 -*-
"""check_c3a：C-3 整张表的显式母函数（1F1 / 形式 Laplace / 指数积分 / Ncal / H）的正式核对模块。

契约：从任意目录 `py -3.14 <本文件>` 运行；sys.path 插入 code 目录导入 core / polylib；
每条结论一行 PASS/FAIL <id> <描述含范围>；最后一行 SUMMARY c3a pass=<n> fail=<n>；全部通过退出码 0。
除 [NUM] 标记的数值检查（decimal 高精度，容差写在描述里）外，全部是精确整数 / Fraction 运算。

所有「对照」的一方都是第 1 节原始定义的独立实现：
  core.U_fast_table（高度 DP）、core.U_multichain（多重链）、本文件 dp_stats（同一三元组条件的细分统计 DP）、
  brute_stats / core.N_brute（DFS 枚举），以及由定义直接推出的二项式反演 N = core.N_from_U。
"""
import os
import sys
import time
import random
from fractions import Fraction
from math import comb, factorial
from decimal import Decimal as D, getcontext

CODE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, CODE)
from core import U_fast_table, U_multichain, good, N_brute, N_from_U, PROMPT_TABLE, stirling2_table  # noqa: E402
from polylib import P_poly, series_inv  # noqa: E402

T_START = time.time()
RESULTS = []


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc))
    sys.stdout.flush()


# =============================================================================
# 0. 定义层：细分统计 DP 与 DFS
# =============================================================================
def dp_stats(m, K):
    """tot[k]=U_k(m)；notasc[k]=不以上升结尾；asc_to[k][j]=以上升结尾且末项为 j。"""
    n = m + 1
    tot, notasc, asc_to = [1], [1], [[0] * n]
    if K >= 1:
        tot.append(n); notasc.append(n); asc_to.append([0] * n)
    if K >= 2:
        cnt = [[1] * n for _ in range(n)]
        for k in range(2, K + 1):
            if k > 2:
                new = [[0] * n for _ in range(n)]
                for a in range(n):
                    for b in range(n):
                        v = cnt[a][b]
                        if v:
                            for c in range(n):
                                if good(a, b, c):
                                    new[b][c] += v
                cnt = new
            tot.append(sum(map(sum, cnt)))
            notasc.append(sum(cnt[a][b] for a in range(n) for b in range(n) if a >= b))
            asc_to.append([sum(cnt[a][j] for a in range(j)) for j in range(n)])
    return tot, notasc, asc_to


def brute_stats(m, k):
    res = [0, 0, [0] * (m + 1)]
    seq = []

    def dfs():
        if len(seq) == k:
            res[0] += 1
            if k <= 1 or seq[-2] >= seq[-1]:
                res[1] += 1
            else:
                res[2][seq[-1]] += 1
            return
        for v in range(m + 1):
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            dfs()
            seq.pop()
    dfs()
    return res[0], res[1], res[2]


def stats_tables(K, M):
    cols = [dp_stats(m, K) for m in range(M + 1)]
    TOT = [[cols[m][0][k] for m in range(M + 1)] for k in range(K + 1)]
    NA = [[cols[m][1][k] for m in range(M + 1)] for k in range(K + 1)]
    AS = [[cols[m][2][k] for m in range(M + 1)] for k in range(K + 1)]
    return TOT, NA, AS


# =============================================================================
# 1. 截断整数幂级数 + 形式 Laplace 的直接展开（EGF 记法：存 N![s^N]，L_s = EGF 系数之和）
# =============================================================================
def zero(K):
    return [0] * (K + 1)


def one(K):
    r = [0] * (K + 1); r[0] = 1
    return r


def pad(p, K):
    p = list(p)[:K + 1]
    return p + [0] * (K + 1 - len(p))


def smul(p, q, K):
    r = [0] * (K + 1)
    for i in range(K + 1):
        a = p[i]
        if a:
            for j in range(K + 1 - i):
                b = q[j]
                if b:
                    r[i + j] += a * b
    return r


def sadd(p, q):
    return [a + b for a, b in zip(p, q)]


def sinv_int(p, K):
    assert p[0] in (1, -1)
    r = [0] * (K + 1); r[0] = p[0]
    for k in range(1, K + 1):
        s = 0
        for i in range(1, k + 1):
            if i < len(p) and p[i]:
                s += p[i] * r[k - i]
        r[k] = -s * p[0]
    return r


def egf_mul(f, g, K, Nmax):
    r = {}
    for i, fi in f.items():
        for j, gj in g.items():
            N = i + j
            if N > Nmax:
                continue
            c = comb(N, i)
            prod = smul(fi, gj, K)
            if any(prod):
                if N in r:
                    r[N] = [a + c * b for a, b in zip(r[N], prod)]
                else:
                    r[N] = [c * b for b in prod]
    return r


def build_pieces(gamma_cols, A, K, M):
    """返回 (Pw, Gam, Ainv, Nmax)：Pw[n] = E^n/n!（E=(e^{vs}-1)/x^3），Gam[m] = gamma_m(x) e^{m v s}，v=x^3/A。"""
    Ainv = sinv_int(pad(A, K), K)
    Nmax = K // 3 + M + 2
    Ainv_pow = [one(K)]
    for N in range(1, Nmax + 2):
        Ainv_pow.append(smul(Ainv_pow[-1], Ainv, K))
    E = {}
    for N in range(1, Nmax + 1):
        if 3 * N - 3 <= K:
            E[N] = [0] * (3 * N - 3) + Ainv_pow[N][:K + 1 - (3 * N - 3)]
    Pw = [{0: one(K)}]
    for n in range(1, M + 1):
        prod = egf_mul(E, Pw[-1], K, Nmax)
        q = {}
        for N, p in prod.items():
            assert all(c % n == 0 for c in p)
            q[N] = [c // n for c in p]
        Pw.append(q)
    Gam = []
    for m in range(M + 1):
        gm = pad(gamma_cols[m], K) if m < len(gamma_cols) else zero(K)
        d = {}
        if any(gm):
            for N in range(0, Nmax + 1):
                if 3 * N > K or (m == 0 and N > 0):
                    break
                base = [0] * (3 * N) + Ainv_pow[N][:K + 1 - 3 * N]
                d[N] = [(m ** N) * c for c in smul(base, gm, K)]
        Gam.append(d)
    return Pw, Gam, Ainv, Nmax


def laplace_solve(gamma_cols, A, K, M):
    """Y = (1/A) L_s[ exp((t/x^3)(e^{vs}-1)) gamma(x, t e^{vs}) ]，返回 Y[k][m]。"""
    Pw, Gam, Ainv, Nmax = build_pieces(gamma_cols, A, K, M)
    cols = []
    for m in range(M + 1):
        acc = zero(K)
        for n in range(m + 1):
            for N, p in egf_mul(Pw[n], Gam[m - n], K, Nmax).items():
                acc = sadd(acc, p)
        cols.append(smul(acc, Ainv, K))
    return [[cols[m][k] for m in range(M + 1)] for k in range(K + 1)]


def gamma_F_cols(K, M):
    cols = []
    for m in range(M + 1):
        c = zero(K)
        if m == 0:
            c[0] = 1
        elif K >= 2:
            c[2] = m
        cols.append(c)
    return cols


def apply_LA(Y, A, K, M):
    out = [[0] * (M + 1) for _ in range(K + 1)]
    for k in range(K + 1):
        for m in range(M + 1):
            s = 0
            for i, a in enumerate(A):
                if a and k - i >= 0:
                    s += a * Y[k - i][m]
            if m >= 1:
                s -= Y[k][m - 1]
            if k >= 3:
                s -= m * Y[k - 3][m]
            out[k][m] = s
    return out


# =============================================================================
# 2. x 的 Laurent 级数（Fraction 系数，显式绝对精度 top）
# =============================================================================
class Lau:
    __slots__ = ('v', 'c', 'top')

    def __init__(self, v, c, top):
        n = top - v + 1
        c = [Fraction(a) for a in c[:max(n, 0)]]
        if n > len(c):
            c += [Fraction(0)] * (n - len(c))
        i = 0
        while i < len(c) and c[i] == 0:
            i += 1
        if i == len(c):
            self.v, self.c, self.top = None, [], top
        else:
            self.v, self.c, self.top = v + i, c[i:], top

    @staticmethod
    def poly(coeffs, cap, shift=0):
        return Lau(shift, list(coeffs), cap)

    def zero_(self):
        return self.v is None

    def __mul__(self, o):
        if not isinstance(o, Lau):
            return self if self.zero_() else Lau(self.v, [o * b for b in self.c], self.top)
        if self.zero_() or o.zero_():
            return Lau(0, [], min(self.top, o.top))
        v = self.v + o.v
        top = min(self.top + o.v, o.top + self.v)
        n = top - v + 1
        r = [Fraction(0)] * max(n, 0)
        for i, a in enumerate(self.c):
            if i >= n:
                break
            if a:
                for j in range(min(len(o.c), n - i)):
                    b = o.c[j]
                    if b:
                        r[i + j] += a * b
        return Lau(v, r, top)

    def inv(self):
        v = self.v
        n = self.top - v + 1
        c0 = self.c[0]
        r = [Fraction(0)] * n
        r[0] = 1 / c0
        for k in range(1, n):
            s = Fraction(0)
            for i in range(1, min(k, len(self.c) - 1) + 1):
                if self.c[i]:
                    s += self.c[i] * r[k - i]
            r[k] = -s / c0
        return Lau(-v, r, -v + n - 1)

    def __add__(self, o):
        top = min(self.top, o.top)
        if self.zero_():
            return Lau(o.v if not o.zero_() else 0, o.c, top)
        if o.zero_():
            return Lau(self.v, self.c, top)
        v = min(self.v, o.v)
        n = top - v + 1
        r = [Fraction(0)] * max(n, 0)
        for L in (self, o):
            d = L.v - v
            for i, a in enumerate(L.c):
                if d + i < n:
                    r[d + i] += a
        return Lau(v, r, top)

    def __sub__(self, o):
        return self + o * (-1)

    def coeff(self, e):
        assert e <= self.top
        if self.zero_() or e < self.v:
            return Fraction(0)
        return self.c[e - self.v]


def lau_matches(L, target, K):
    """x^e 系数：e<0 为 0（负幂全部消去），0<=e<=K 等于 target[e]。"""
    if L.top < K:
        return False
    if not L.zero_() and L.v < 0:
        return False
    return all(L.coeff(e) == target[e] for e in range(K + 1))


# =============================================================================
# 3. 数值工具（decimal）
# =============================================================================
def dec(fr):
    return D(fr.numerator) / D(fr.denominator)


def pi_dec():
    getcontext().prec += 10

    def arctan_inv(n):
        x = D(1) / n
        x2 = x * x
        s, term, k = D(0), x, 0
        eps = D(10) ** (-(getcontext().prec + 2))
        while abs(term) > eps:
            s += term / (2 * k + 1) if k % 2 == 0 else -term / (2 * k + 1)
            term *= x2
            k += 1
        return s
    p = 16 * arctan_inv(5) - 4 * arctan_inv(239)
    getcontext().prec -= 10
    return +p


def sin_dec(x, PI):
    getcontext().prec += 10
    twopi = 2 * PI
    x = x - twopi * (x / twopi).to_integral_value()
    s, term, k = D(0), x, 1
    eps = D(10) ** (-(getcontext().prec + 2))
    while abs(term) > eps:
        s += term
        term *= -x * x / ((2 * k) * (2 * k + 1))
        k += 1
    getcontext().prec -= 10
    return +s


def bernoulli_list(nmax):
    B = [Fraction(0)] * (nmax + 1)
    B[0] = Fraction(1)
    for n in range(1, nmax + 1):
        B[n] = -sum(comb(n + 1, k) * B[k] for k in range(n)) / (n + 1)
    return B


def lngamma_pos(z, PI, nb=60):
    prec = getcontext().prec
    shift_to = max(30, prec)
    getcontext().prec += 15
    B = bernoulli_list(2 * nb)
    acc = D(0)
    zz = z
    while zz < shift_to:
        acc += zz.ln()
        zz += 1
    s = (zz - D('0.5')) * zz.ln() - zz + (2 * PI).ln() / 2
    zp = zz
    z2 = zz * zz
    for k in range(1, nb + 1):
        s += dec(B[2 * k]) / (D(2 * k) * D(2 * k - 1) * zp)
        zp *= z2
    r = s - acc
    getcontext().prec -= 15
    return +r


def gamma_neg_reflect(lam, PI):
    return -PI / (sin_dec(PI * lam, PI) * lngamma_pos(1 + lam, PI).exp())


def expsinh_quad(f, tol_digits, h0=D('0.0625'), tmin=-6.5, tmax=3.5, maxlevel=8):
    PI = pi_dec()
    half_pi = PI / 2
    cache = {}

    def node(tau):
        if tau in cache:
            return cache[tau]
        et = tau.exp()
        sh = (et - 1 / et) / 2
        ch = (et + 1 / et) / 2
        s = (half_pi * sh).exp()
        w = s * half_pi * ch
        val = f(s) * w if w != 0 else D(0)
        cache[tau] = val
        return val
    h = h0
    prev = None
    est = None
    for level in range(maxlevel):
        n_lo = int((D(tmin) / h).to_integral_value())
        n_hi = int((D(tmax) / h).to_integral_value())
        tot = D(0)
        for i in range(n_lo, n_hi + 1):
            tot += node(h * i)
        est = tot * h
        if prev is not None and abs(est - prev) < D(10) ** (-tol_digits):
            return est, abs(est - prev)
        prev = est
        h = h / 2
    return est, abs(est - prev)


def I_val(x, t, with_g=True):
    """草稿的积分 I(x,t) = x^{-3} int_0^inf exp((t(e^sig-1)-(1-x)sig)/x^3) g(t e^sig) dsig，
    换元 sig = u s 后 = (1/(1-x)) int_0^inf e^{-s} exp((t/x^3)(e^{us}-1)) g(t e^{us}) ds。"""
    tol_digits = getcontext().prec - 8
    xd, td = dec(x), dec(t)
    u = xd ** 3 / (1 - xd)
    c = td / xd ** 3
    x2 = xd * xd
    big = D(10) ** 6

    def f(s):
        if s > big:
            return D(0)
        e = (u * s).exp()
        ex = -s + c * (e - 1)
        if ex < -(getcontext().prec * 3):
            return D(0)
        val = ex.exp()
        if with_g:
            w = td * e
            val *= 1 + x2 * w / ((1 - w) ** 2)
        return val
    val, err = expsinh_quad(f, tol_digits)
    return val / (1 - xd), err


def S_exact(x, t, with_g, M):
    """sum_{m<=M} t^m G_m(x)（或 1/P_m），精确 Fraction；另返回 G_M, G_{M-1} 便于尾项界。"""
    G_prev = Fraction(1)
    P = Fraction(1)
    tot = Fraction(0)
    tp = Fraction(1)
    Gs = []
    for m in range(M + 1):
        b = 1 - x - m * x ** 3
        P *= b
        G = (G_prev + m * x * x) / b if with_g else 1 / P
        Gs.append(G)
        tot += tp * G
        G_prev = G
        tp *= t
    return tot, Gs


def S_tail_bound(x, t, with_g, Gs, M):
    """严格尾项界：sum_{m>M} |t|^m |G_m(x)|（需要 M >= m0，见笔记 §5.6）。"""
    lam = (1 - x) / x ** 3
    m0 = 0
    while not (m0 > lam and x ** 3 * (m0 + 1 - lam) >= 2):
        m0 += 1
    assert M >= m0
    c1 = 1 / (x ** 3 * (m0 + 1 - lam))
    if with_g:
        c2 = (m0 + 1) / (x * (m0 + 1 - lam))
    else:
        c2 = Fraction(0)          # G_m = 1/P_m：|G_m| <= |G_{m-1}| * c1
    B = max(max(abs(g) for g in Gs[m0:M + 1]), c2 / (1 - c1))
    at = abs(t)
    return B * at ** (M + 1) / (1 - at)


def S_val(x, t, with_g=True):
    digits = getcontext().prec + 5
    lam = (1 - x) / x ** 3
    m0 = 0
    while not (m0 > lam and x ** 3 * (m0 + 1 - lam) >= 2):
        m0 += 1
    M = max(int(lam) + 20, m0 + 5)
    while True:
        tot, Gs = S_exact(x, t, with_g, M)
        tb = S_tail_bound(x, t, with_g, Gs, M)
        if tb < Fraction(1, 10 ** digits):
            return dec(tot), tot, tb
        M += 40


_FACT = [1]


def _fact(n):
    while len(_FACT) <= n:
        _FACT.append(_FACT[-1] * len(_FACT))
    return _FACT[n]


def K_val(x, with_g=True):
    """K(x) = sum_n phi_n/(n-lambda) + int_1^inf tau^{-lambda-1} phi(tau) dtau，phi = e^{-tau} g(-x^3 tau)；
    不带 g 时就是 Gamma(-lambda) 的 Prym 分解。"""
    tol_digits = getcontext().prec - 8
    lam = (1 - x) / x ** 3
    tol = Fraction(1, 10 ** (getcontext().prec + 5))
    ser = Fraction(0)
    n = 0
    small = 0
    while True:
        if with_g:
            ph = sum(Fraction((-1) ** (n - j), _fact(n - j)) * (1 if j == 0 else j * x * x * (-x ** 3) ** j)
                     for j in range(n + 1))
        else:
            ph = Fraction((-1) ** n, _fact(n))
        term = ph / (n - lam)
        ser += term
        if abs(term) < tol and n > lam + 5:
            small += 1
            if small >= 5:
                break
        else:
            small = 0
        n += 1
    xd = dec(x)
    lamd = dec(lam)
    x3 = xd ** 3
    x2 = xd * xd

    def f(w):
        tau = 1 + w
        val = (-(lamd + 1) * tau.ln() - tau)
        if val < -(getcontext().prec * 3):
            return D(0)
        val = val.exp()
        if with_g:
            z = -x3 * tau
            val *= 1 + x2 * z / ((1 - z) ** 2)
        return val
    tail, err = expsinh_quad(f, tol_digits)
    return dec(ser) + tail


def predicted_gap(x, t, Kx):
    xd, td = dec(x), dec(t)
    a = -td / xd ** 3
    lam = dec((1 - x) / x ** 3)
    return Kx / xd ** 3 * a.exp() * (lam * a.ln()).exp()


def fk_at(t0, Kmax):
    """f_k(t0) = sum_m U_k(m) t0^m（k<=Kmax）：由 PDE 的 x^k 系数 (1-t)f_k = f_{k-1} + t f'_{k-3} + gamma_k
    在 t0 处做 Taylor 递推（精确）。"""
    d = {}

    def get(k, j):
        if k < 0 or j < 0:
            return Fraction(0)
        return d[(k, j)]
    for k in range(Kmax + 1):
        Jk = (Kmax - k) // 3 + 2
        for j in range(Jk + 1):
            g = Fraction(0)
            if k == 0 and j == 0:
                g = Fraction(1)
            if k == 2:
                g = t0 * (j + 1) / (1 - t0) ** (j + 2) + (Fraction(j) / (1 - t0) ** (j + 1) if j >= 1 else 0)
            val = get(k, j - 1) + get(k - 1, j) + g
            if k >= 3:
                val += t0 * (j + 1) * get(k - 3, j + 1) + j * get(k - 3, j)
            d[(k, j)] = val / (1 - t0)
    return [d[(k, 0)] for k in range(Kmax + 1)]


# =============================================================================
# A. 锚点：本文件使用的定义层计数彼此一致
# =============================================================================
T60 = U_fast_table(60, 41)          # U_k(m), k<=60, m<=41
ok = all(T60[k][:7] == PROMPT_TABLE[k] for k in PROMPT_TABLE)
ok &= all(U_multichain(k, m) == T60[k][m] for k in range(0, 8) for m in range(0, 5))
TOT40, NA40, AS40 = stats_tables(40, 20)
ok &= all(TOT40[k][m] == T60[k][m] for k in range(41) for m in range(21))
for k in range(0, 8):
    for m in range(0, 5):
        tb, nb, ab = brute_stats(m, k)
        ok &= (tb, nb, ab) == (TOT40[k][m], NA40[k][m], AS40[k][m])
report('c3a-anchor', ok, 'height DP == prompt table (k<=10,m<=6) == multichain (k<=7,m<=4); refined DP (not-ascent / ascent-to-j) '
       'totals == height DP (k<=40,m<=20) and == DFS enumeration (k<=7,m<=4)')

# =============================================================================
# B. PDE（C5）= 引理 1 的系数形式
# =============================================================================
def pde_ok(T, K, M):
    def c(k, m):
        return T[k][m] if (k >= 0 and m >= 0) else 0
    for k in range(K + 1):
        for m in range(M + 1):
            lhs = c(k, m) - c(k - 1, m) - c(k, m - 1) - m * c(k - 3, m)
            rhs = (1 if (k == 0 and m == 0) else 0) + (m if (k == 2 and m >= 1) else 0)
            if lhs != rhs:
                return False
    return True


report('c3a-pde-F', pde_ok(T60, 60, 41), '(1-x-t)F - x^3 t F_t = 1 + x^2 t/(1-t)^2 holds coefficientwise for the DP table, k<=60, m<=41')

# =============================================================================
# C. 形式 Laplace 表示
# =============================================================================
random.seed(20261004)
okL = True
okI = True
for A in ([1, -1], [1, -1, 0, 1]):
    for trial in range(3):
        K, M = 18, 9
        gcols = [[random.randint(-3, 3) for _ in range(K + 1)] for _ in range(M + 1)]
        gcols[0][0] = random.choice([1, -1, 2])
        Y = laplace_solve(gcols, A, K, M)
        LY = apply_LA(Y, A, K, M)
        okL &= all(LY[k][m] == gcols[m][k] for k in range(K + 1) for m in range(M + 1))
report('c3a-lap-general', okL, 'general principle: Y=(1/A)L_s[exp((t/x^3)(e^{vs}-1)) gamma(x,t e^{vs})], v=x^3/A, solves (A-t)Y-x^3 t Y_t=gamma; '
       '6 random integer gamma, A in {1-x, 1-x+x^3}, k<=18, m<=9 (exact)')


def check_operator_identity(K, M):
    """F 的被积式 Psi：(1-x-t)Psi - x^3 t Psi_t == (1-x)(Psi - Psi_s)，逐 (t^m, s^N, x^k)。"""
    gcols = gamma_F_cols(K, M)
    Pw, Gam, Ainv, Nmax = build_pieces(gcols, [1, -1], K, M)
    Psi = []
    for m in range(M + 1):
        acc = {}
        for n in range(m + 1):
            for N, p in egf_mul(Pw[n], Gam[m - n], K, Nmax).items():
                acc[N] = sadd(acc[N], p) if N in acc else p
        Psi.append(acc)
    Ap = pad([1, -1], K)
    x3 = zero(K); x3[3] = 1
    for m in range(M + 1):
        for N in range(Nmax):
            P = Psi[m].get(N, zero(K))
            Pm1 = Psi[m - 1].get(N, zero(K)) if m >= 1 else zero(K)
            Pn1 = Psi[m].get(N + 1, zero(K))
            lhs = [a - b - m * c for a, b, c in zip(smul(Ap, P, K), Pm1, smul(x3, P, K))]
            rhs = smul(Ap, [a - b for a, b in zip(P, Pn1)], K)
            if lhs != rhs:
                return False
    return True


report('c3a-lap-operator', check_operator_identity(30, 16),
       'key identity (1-x-t)Psi - x^3 t dPsi/dt = (1-x)(Psi - dPsi/ds) for Psi=exp((t/x^3)(e^{us}-1))g(t e^{us}), '
       'all coefficients x^k t^m s^N with k<=30, m<=16 (exact)')

t1 = time.time()
LAP = laplace_solve(gamma_F_cols(60, 30), [1, -1], 60, 30)
okF = all(LAP[k][m] == T60[k][m] for k in range(61) for m in range(31))
report('c3a-lap-F', okF, 'F = (1/(1-x)) L_s[exp((t/x^3)(e^{us}-1))(1 + x^2 t e^{us}/(1-t e^{us})^2)], u=x^3/(1-x): '
       'direct exact expansion == DP U_k(m) for k<=60, m<=30 (%.1fs)' % (time.time() - t1))

# 朴素实现（普通 s 幂级数 + Fraction，逐项乘 N!），并核对良定义所用的赋值界：
#   [s^N t^m] Psi 的 x 赋值 >= 3N - 3m，且 [s^N] Psi 的 (x,t) 总次数 >= N
def naive_laplace(K, M, Nmax):
    def pz():
        return [Fraction(0)] * (K + 1)

    def pm(p, q):
        r = pz()
        for i, a in enumerate(p):
            if a:
                for j in range(K + 1 - i):
                    if q[j]:
                        r[i + j] += a * q[j]
        return r
    inv1mx_pow = [[Fraction(comb(N + j - 1, j)) if N > 0 else Fraction(1 if j == 0 else 0) for j in range(K + 1)]
                  for N in range(Nmax + 2)]
    # E[N] = x^{3N-3}(1-x)^{-N}/N!
    E = [pz() for _ in range(Nmax + 1)]
    for N in range(1, Nmax + 1):
        if 3 * N - 3 <= K:
            for j in range(K + 1 - (3 * N - 3)):
                E[N][3 * N - 3 + j] = inv1mx_pow[N][j] / factorial(N)
    # Phi[m][N]：t^m s^N 系数
    Phi = [[pz() for _ in range(Nmax + 1)] for _ in range(M + 1)]
    Phi[0][0][0] = Fraction(1)
    Epow = [[pz() for _ in range(Nmax + 1)]]
    Epow[0][0][0] = Fraction(1)
    for n in range(1, M + 1):
        prev = Epow[-1]
        cur = [pz() for _ in range(Nmax + 1)]
        for N1 in range(Nmax + 1):
            if not any(prev[N1]):
                continue
            for N2 in range(1, Nmax + 1 - N1):
                if any(E[N2]):
                    pr = pm(prev[N1], E[N2])
                    cur[N1 + N2] = [a + b for a, b in zip(cur[N1 + N2], pr)]
        Epow.append(cur)
        for N in range(Nmax + 1):
            Phi[n][N] = [c / factorial(n) for c in cur[N]]
    # Gam[j][N]：1 + x^2 sum_j j t^j e^{jus}，e^{jus} 的 s^N 系数 (ju)^N/N! = j^N x^{3N}(1-x)^{-N}/N!
    Gam = [[pz() for _ in range(Nmax + 1)] for _ in range(M + 1)]
    Gam[0][0][0] = Fraction(1)
    for j in range(1, M + 1):
        for N in range(Nmax + 1):
            if 3 * N + 2 <= K:
                for i in range(K + 1 - (3 * N + 2)):
                    Gam[j][N][3 * N + 2 + i] = Fraction(j ** (N + 1)) * inv1mx_pow[N][i] / factorial(N)
    Psi = [[pz() for _ in range(Nmax + 1)] for _ in range(M + 1)]
    for m in range(M + 1):
        for n in range(m + 1):
            for N1 in range(Nmax + 1):
                if not any(Phi[n][N1]):
                    continue
                for N2 in range(Nmax + 1 - N1):
                    if any(Gam[m - n][N2]):
                        pr = pm(Phi[n][N1], Gam[m - n][N2])
                        Psi[m][N1 + N2] = [a + b for a, b in zip(Psi[m][N1 + N2], pr)]
    Y = [[sum(factorial(N) * Psi[m][N][k] for N in range(Nmax + 1)) for m in range(M + 1)] for k in range(K + 1)]
    Y = [[sum(Y[i][m] for i in range(k + 1)) for m in range(M + 1)] for k in range(K + 1)]   # 乘 1/(1-x)
    val_ok = all(Psi[m][N][k] == 0 for m in range(M + 1) for N in range(Nmax + 1) for k in range(K + 1)
                 if k < 3 * N - 3 * m or k + m < N)
    return Y, val_ok


Yn, val_ok = naive_laplace(15, 6, 15 // 3 + 6 + 4)
ok = all(Yn[k][m] == T60[k][m] for k in range(16) for m in range(7))
report('c3a-lap-naive', ok and val_ok, 'naive implementation (ordinary s-series, Fraction, multiply [s^N] by N!) == DP for k<=15, m<=6; '
       'valuation bounds ord_x [s^N t^m]Psi >= 3N-3m and ord_(x,t) [s^N]Psi >= N hold in that range (well-definedness)')

# 系数推论：[t^m]F = 1/P_m + x^2 sum_{j=1}^m j/prod_{i=j}^m b_i（= W_m/P_m）
K, M = 60, 30
ok = True
for m in range(M + 1):
    ser = series_inv(P_poly(m), K + 1)
    for j in range(1, m + 1):
        den = [1]
        for i in range(j, m + 1):
            # multiply by b_i
            b = [1, -1, 0, -i]
            den = [sum(den[a] * b[c - a] for a in range(len(den)) if 0 <= c - a < 4) for c in range(len(den) + 3)]
        inv = series_inv(den, K + 1)
        for k in range(2, K + 1):
            ser[k] += j * inv[k - 2]
    if [int(c) for c in ser] != [T60[k][m] for k in range(K + 1)] or any(c.denominator != 1 for c in ser):
        ok = False
report('c3a-lap-coeff', ok, 'coefficient corollary [t^m]F = 1/P_m + x^2 sum_{j=1}^m j/prod_{i=j}^m b_i == DP, k<=60, m<=30')

# =============================================================================
# D. 1F1 / Kummer / 下不完全 Gamma（Laurent 级数直接按定义展开）
# =============================================================================
K, M = 40, 20
CAP = K + 3 * M + 10
lam_L = Lau.poly([1, -1], CAP, shift=-3)                 # lambda = (1-x)/x^3
inv_1mx = Lau.poly([1, -1], CAP).inv()
ilm = [Lau.poly([i], CAP) - lam_L for i in range(M + 2)]   # i - lambda
inv_lmn = [(lam_L - Lau.poly([n], CAP)).inv() for n in range(M + 1)]   # 1/(lambda-n)


def xpow(e, c=1):
    return Lau.poly([c], CAP, shift=e)


# D1: 1F1(1;1-lambda;-t/x^3)/(1-x) 的 t^n 系数 = (-1)^n x^{-3n}/((1-lambda)_n (1-x)) == 不以上升结尾的计数
ok = True
for n in range(M + 1):
    poch = Lau.poly([1], CAP)
    for i in range(1, n + 1):
        poch = poch * ilm[i]
    term = xpow(-3 * n, (-1) ** n) * poch.inv() * inv_1mx
    ok &= lau_matches(term, [NA40[k][n] for k in range(K + 1)], K)
report('c3a-1f1-const', ok, 'sum_m t^m/P_m = 1F1(1;1-lambda;-t/x^3)/(1-x): Pochhammer expansion in Q(x) (as Laurent series) '
       'has no negative powers and equals #legal sequences not ending in an ascent, k<=40, m<=20')

# D1b: 1/P_m 作为有理函数精确等于 1F1 的系数：(-1)^n x^{-3n}/((1-x)(1-lambda)_n)，交叉相乘多项式恒等
ok = True
for n in range(0, 26):
    # (1-lambda)_n = prod_{i=1}^n (i x^3 - 1 + x)/x^3  =>  系数 = (-1)^n / ((1-x) prod (i x^3 - 1 + x))
    den = [1, -1]
    for i in range(1, n + 1):
        f = [-1, 1, 0, i]
        den = [sum(den[a] * f[c - a] for a in range(len(den)) if 0 <= c - a < 4) for c in range(len(den) + 3)]
    lhs = [(-1) ** n * c for c in den]      # 1F1 系数的分母（分子为 1）
    ok &= lhs == [int(c) for c in P_poly(n)] + [0] * (len(lhs) - len(P_poly(n)))
report('c3a-1f1-exact', ok, 'exact rational identity (-1)^n x^{-3n}/((1-x)(1-lambda)_n) = 1/P_n (polynomial cross-check), n<=25; '
       'hence each t^n coefficient lies in Q(x) and in Z[[x]]')

# D1c: Stirling 展开 [x^k] 1/P_m = sum_s S(m+s,m) C(k+m-2s, k-3s)（由 L_s[(e^{us}-1)^m/m!] = sum_N S(N,m) u^N）
S2 = stirling2_table(120)
ok = all(sum(S2[m + s][m] * comb(k + m - 2 * s, k - 3 * s) for s in range(0, k // 3 + 1)) == NA40[k][m]
         for k in range(K + 1) for m in range(M + 1))
report('c3a-1f1-stirling', ok, 'Stirling expansion of the 1F1 part: [x^k t^m] = sum_s S(m+s,m) C(k+m-2s,k-3s) == not-ascent counts, k<=40, m<=20')

# D2: Kummer 恒等式在 Q(lambda) 中（n+2 个点 + 次数论证 => 恒等）
random.seed(7)
ok = True
for n in range(0, 31):
    pts = set()
    while len(pts) < n + 2:
        p = Fraction(random.randint(-10 ** 6, 10 ** 6), random.randint(1, 10 ** 4))
        if p.denominator == 1 and 0 <= p <= n:
            continue
        pts.add(p)
    for L in pts:
        lhs = sum(Fraction((-1) ** j, factorial(n - j) * factorial(j)) * L / (L - j) for j in range(n + 1))
        poch = Fraction(1)
        for i in range(1, n + 1):
            poch *= (i - L)
        ok &= (lhs == 1 / poch)
# 以及 e^a 1F1(-lambda;1-lambda;-a)/(1-x) 的 Laurent 展开 == 不以上升结尾的计数
for m in range(M + 1):
    acc = Lau(0, [], CAP)
    for j in range(m + 1):
        i = m - j
        # a^i/i! * [(-lambda)_j/(1-lambda)_j] (-a)^j/j!，a = -t/x^3：a^i -> (-1)^i x^{-3i}，(-a)^j -> x^{-3j}
        ratio = (Lau.poly([0], CAP) - lam_L) * ilm[j].inv() if j >= 1 else Lau.poly([1], CAP)   # (-lambda)/(j-lambda)
        acc = acc + xpow(-3 * m, Fraction((-1) ** i, factorial(i) * factorial(j))) * ratio
    ok &= lau_matches(acc * inv_1mx, [NA40[k][m] for k in range(K + 1)], K)
report('c3a-kummer', ok, 'Kummer: 1F1(1;1-lambda;a) = e^a 1F1(-lambda;1-lambda;-a): identity in Q(lambda)[[a]] (n<=30, exact via degree argument) '
       'and the Kummer form expanded in Q(x)[[t]] == not-ascent counts, k<=40, m<=20')

# D3: 下不完全 Gamma（级数）形式：sum_m t^m/P_m = x^{-3} e^a sum_n (-a)^n/(n!(lambda-n))  [= -x^{-3} e^a a^lambda gamma(-lambda,a)]
ok = True
for m in range(M + 1):
    acc = Lau(0, [], CAP)
    for n in range(m + 1):
        i = m - n
        acc = acc + xpow(-3 - 3 * m, Fraction((-1) ** i, factorial(i) * factorial(n))) * inv_lmn[n]
    ok &= lau_matches(acc, [NA40[k][m] for k in range(K + 1)], K)
report('c3a-gamma', ok, 'lower-incomplete-gamma form sum_m t^m/P_m = x^{-3} e^a sum_n (-a)^n/(n!(lambda-n)), a=-t/x^3, '
       'expanded in Q(x)[[t]] == not-ascent counts, k<=40, m<=20')

# D4: F = sum_{j>=0} c_j t^j/b_j 1F1(1; j+1-lambda; -t/x^3)，c_0=1, c_j=j x^2；逐 j 对照「以上升到 j 结尾」
ok = True
inv_b = [Lau.poly([1, -1, 0, -j], CAP).inv() for j in range(M + 1)]
for m in range(M + 1):
    total = Lau(0, [], CAP)
    for j in range(m + 1):
        n = m - j
        poch = Lau.poly([1], CAP)
        for i in range(j + 1, j + n + 1):
            poch = poch * ilm[i]
        cj = Lau.poly([1], CAP) if j == 0 else Lau.poly([j], CAP, shift=2)
        term = cj * inv_b[j] * xpow(-3 * n, (-1) ** n) * poch.inv()
        target = [NA40[k][m] for k in range(K + 1)] if j == 0 else [AS40[k][m][j] for k in range(K + 1)]
        ok &= lau_matches(term, target, K)
        total = total + term
    ok &= lau_matches(total, [T60[k][m] for k in range(K + 1)], K)
report('c3a-1f1-sum', ok, 'F = sum_j c_j t^j/b_j 1F1(1;j+1-lambda;-t/x^3): term j=0 == not-ascent counts, term j>=1 == '
       '#sequences ending with an ascent to value j, total == U_k(m); k<=40, m<=20')

# D5: Kummer 形式 F = x^{-3} e^a sum_n phi_n a^n/(lambda-n)，phi(tau) = e^{-tau} g(-x^3 tau)
def phi_L(n):
    acc = Lau(0, [], CAP)
    for j in range(n + 1):
        c = Fraction((-1) ** (n - j), factorial(n - j))
        acc = acc + (Lau.poly([c], CAP) if j == 0 else Lau.poly([c * j * (-1) ** j], CAP, shift=2 + 3 * j))
    return acc


phis = [phi_L(n) for n in range(M + 1)]
ok = True
for m in range(M + 1):
    acc = Lau(0, [], CAP)
    for n in range(m + 1):
        i = m - n
        acc = acc + xpow(-3 - 3 * m, Fraction((-1) ** m, factorial(i))) * phis[n] * inv_lmn[n]
    ok &= lau_matches(acc, [T60[k][m] for k in range(K + 1)], K)
report('c3a-kummer-F', ok, 'Kummer form of the whole table F = x^{-3} e^a sum_n phi_n a^n/(lambda-n), phi(tau)=e^{-tau}(1 - x^5 tau/(1+x^3 tau)^2), '
       'expanded in Q(x)[[t]] == U_k(m), k<=40, m<=20')

# D6: 1F1(1;-lambda;a) = 1 + t sum_m t^m/P_m
ok = True
for n in range(0, M + 1):
    poch = Lau.poly([1], CAP)
    for i in range(0, n):
        poch = poch * ilm[i]
    term = xpow(-3 * n, (-1) ** n) * poch.inv()
    target = [1 if k == 0 else 0 for k in range(K + 1)] if n == 0 else [NA40[k][n - 1] for k in range(K + 1)]
    ok &= lau_matches(term, target, K)
report('c3a-1f1-shift', ok, '1F1(1;-lambda;-t/x^3) = 1 + t sum_m t^m/P_m (constant part of Ntilde = 1 + tF), k<=40, n<=20')

# D7: Humbert（合流 Appell）Phi_1(al,be;ga;X,Y) = sum_{m,n} (al)_{m+n}(be)_m/((ga)_{m+n} m! n!) X^m Y^n
def gpoch(b, n):
    r = Fraction(1)
    for i in range(n):
        r *= b + i
    return r


def humbert_Y(A, be, KK, MM, cap):
    """Y_beta = (1/A)(1-t)^{-beta} Phi_1(1,beta;1-lam_A;-t/(1-t),a)，lam_A = A/x^3，a=-t/x^3：返回 t^N 系数（Lau）列表。"""
    ONE_ = Lau.poly([1], cap)
    ZERO_ = Lau(0, [], cap)
    Ap = Lau.poly(A, cap)
    lamA = Ap * Lau.poly([1], cap, shift=-3)
    inv_poch = []
    pp = ONE_
    for N in range(MM + 1):
        inv_poch.append(pp.inv())
        pp = pp * (Lau.poly([1 + N], cap) - lamA)
    out = [ZERO_] * (MM + 1)
    for m in range(MM + 1):
        Xm = [Fraction(0)] * (MM + 1)
        if m == 0:
            Xm[0] = Fraction(1)
        else:
            for r in range(MM + 1 - m):
                Xm[m + r] = Fraction((-1) ** m * comb(m + r - 1, r))
        for n in range(MM + 1 - m):
            N = m + n
            coef = Fraction(factorial(N)) * gpoch(be, m) / (factorial(m) * factorial(n)) * (-1) ** n
            base = inv_poch[N] * Lau.poly([coef], cap, shift=-3 * n)
            for d in range(MM + 1 - n):
                if Xm[d]:
                    out[d + n] = out[d + n] + base * Xm[d]
    pre = [gpoch(be, q) / factorial(q) for q in range(MM + 1)]
    res = [ZERO_] * (MM + 1)
    for i in range(MM + 1):
        for j in range(MM + 1 - i):
            if pre[j]:
                res[i + j] = res[i + j] + out[i] * pre[j]
    Ainv = Ap.inv()
    return [r * Ainv for r in res]


# D7a 一般 beta：L_A[Y_beta] = (1-t)^{-beta}
KK, MM = 24, 10
cap = KK + 3 * MM + 12
ok = True
for A in ([1, -1], [1, -1, 0, 1]):
    for be in (Fraction(0), Fraction(1), Fraction(2), Fraction(1, 2), Fraction(-3)):
        Y = humbert_Y(A, be, KK, MM, cap)
        Ap = Lau.poly(A, cap)
        for N in range(MM + 1):
            Lv = Ap * Y[N] - Lau.poly([N], cap, shift=3) * Y[N]
            if N >= 1:
                Lv = Lv - Y[N - 1]
            target = [gpoch(be, N) / factorial(N) if k == 0 else 0 for k in range(KK + 1)]
            ok &= lau_matches(Lv, target, KK)
report('c3a-humbert-general', ok, 'Humbert solution: Y_beta=(1/A)(1-t)^{-beta} Phi_1(1,beta;1-A/x^3;-t/(1-t),-t/x^3) solves (A-t)Y-x^3 t Y_t=(1-t)^{-beta}; '
       'A in {1-x,1-x+x^3}, beta in {0,1,2,1/2,-3}, k<=24, t^N N<=10 (Phi_1 and Pochhammers expanded from the definitions)')

# D7b F = Y_0 + x^2 (Y_2 - Y_1)（A = 1-x），以及未变换形式 e^a/(1-x)[1F1(-lam;1-lam;-a) + x^2(Phi_1(-lam,2;..;t,-a) - Phi_1(-lam,1;..;t,-a))]
KK, MM = 40, 16
cap = KK + 3 * MM + 12
Ys = [humbert_Y([1, -1], Fraction(b), KK, MM, cap) for b in (0, 1, 2)]
x2L = Lau.poly([1], cap, shift=2)
ok = all(lau_matches(Ys[0][N] + x2L * (Ys[2][N] - Ys[1][N]), [T60[k][N] for k in range(KK + 1)], KK) for N in range(MM + 1))
KK2, MM2 = 30, 12
cap2 = KK2 + 3 * MM2 + 12
lam2 = Lau.poly([1, -1], cap2, shift=-3)
ONE2 = Lau.poly([1], cap2)
ZERO2 = Lau(0, [], cap2)
pochm2, ipoch2 = [], []
pa, pb = ONE2, ONE2
for N in range(MM2 + 1):
    pochm2.append(pa)
    ipoch2.append(pb.inv())
    pa = pa * (Lau.poly([N], cap2) - lam2)          # (-lam)_{N+1}
    pb = pb * (Lau.poly([N + 1], cap2) - lam2)      # (1-lam)_{N+1}


def phi1_I(be):
    out = [ZERO2] * (MM2 + 1)
    for m in range(MM2 + 1):
        for n in range(MM2 + 1 - m):
            N = m + n
            out[N] = out[N] + pochm2[N] * ipoch2[N] * Lau.poly([gpoch(be, m) / (factorial(m) * factorial(n))], cap2, shift=-3 * n)
    return out


P0_, P1_, P2_ = phi1_I(0), phi1_I(1), phi1_I(2)
x2L2 = Lau.poly([1], cap2, shift=2)
inner = [P0_[N] + x2L2 * (P2_[N] - P1_[N]) for N in range(MM2 + 1)]
ea = [Lau.poly([Fraction((-1) ** n, factorial(n))], cap2, shift=-3 * n) for n in range(MM2 + 1)]
inv1mx2 = Lau.poly([1, -1], cap2).inv()
for N in range(MM2 + 1):
    acc = ZERO2
    for i in range(N + 1):
        acc = acc + ea[i] * inner[N - i]
    ok &= lau_matches(acc * inv1mx2, [T60[k][N] for k in range(KK2 + 1)], KK2)
report('c3a-humbert-F', ok, 'closed form F = (1/(1-x))[1F1(1;1-lam;a) + x^2((1-t)^{-2}Phi_1(1,2;1-lam;-t/(1-t),a) - (1-t)^{-1}Phi_1(1,1;1-lam;-t/(1-t),a))] '
       '== DP (k<=40, m<=16); untransformed form e^a/(1-x)[1F1(-lam;1-lam;-a)+x^2(Phi_1(-lam,2;1-lam;t,-a)-Phi_1(-lam,1;1-lam;t,-a))] == DP (k<=30, m<=12)')

# D7c 系数形式：Y_beta = (1-t)^{-beta} sum_N (t^N/P_N) sum_{m<=N} C(N,m)(beta)_m (x^3/(1-t))^m，
#     故 G_M = 1/P_M + x^2 sum_{N<=M} (1/P_N) sum_{m<=N} C(N,m) x^{3m} [ (m+1)! C(M-N+m+1, M-N) - m! C(M-N+m, M-N) ]
KK, MM = 60, 30
invP = [series_inv(P_poly(N), KK + 1) for N in range(MM + 1)]
ok = True
for Mm in range(MM + 1):
    ser = list(invP[Mm])
    for N in range(Mm + 1):
        for m in range(N + 1):
            c = comb(N, m) * (factorial(m + 1) * comb(Mm - N + m + 1, Mm - N) - factorial(m) * comb(Mm - N + m, Mm - N))
            if c == 0:
                continue
            sh = 2 + 3 * m
            for k in range(sh, KK + 1):
                ser[k] += c * invP[N][k - sh]
    ok &= all(ser[k] == T60[k][Mm] for k in range(KK + 1))
report('c3a-humbert-coeff', ok, 'coefficient form of the Humbert closed form: G_M = 1/P_M + x^2 sum_{N<=M} P_N^{-1} sum_{m<=N} C(N,m) x^{3m} '
       '[(m+1)! C(M-N+m+1,M-N) - m! C(M-N+m,M-N)] == DP, k<=60, M<=30')

# =============================================================================
# E. Ncal(x,y) = sum N(k,q) x^k y^q
# =============================================================================
KN = 30
Ntab = [[N_from_U(T60, k, q) for q in range(KN + 1)] for k in range(KN + 1)]
ok = True
NB = {}
for k in range(0, 10):
    br = N_brute(k)
    NB[k] = [br.get(q, 0) for q in range(KN + 1)]
    ok &= NB[k] == Ntab[k]
ok &= all(Ntab[k][q] == 0 for k in range(KN + 1) for q in range(k + 1, KN + 1))
report('c3a-N-def', ok, 'N(k,q) by DFS over surjective legal words (k<=9) == binomial inversion of the DP table; N(k,q)=0 for q>k (k<=30)')

# E1 代换：1 + tF(x,t) = Ncal(x,t/(1-t))/(1-t)  <=>  [k=n=0] + U_k(n-1) = sum_q N(k,q) C(n,q)
ok = all(((1 if (k == 0 and n == 0) else 0) + (T60[k][n - 1] if n >= 1 else 0)) ==
         sum(NB[k][q] * comb(n, q) for q in range(KN + 1)) for k in range(10) for n in range(0, 42))
report('c3a-N-subst', ok, 'substitution 1 + t F(x,t) = Ncal(x, t/(1-t))/(1-t) with N from DFS (k<=9) and U from DP, n<=41')


def Nc(k, q):
    if k < 0 or q < 0 or k > KN or q > KN:
        return 0
    return Ntab[k][q]


# E2 PDE：(1 - x(1+y) + x^3(1-y^2)) Ncal - x^3 y (1+y)^2 Ncal_y = 1 - x + x^3 + x^2 y^2
def pde_N(k, q):
    s = Nc(k, q) - Nc(k - 1, q) - Nc(k - 1, q - 1) + Nc(k - 3, q) - Nc(k - 3, q - 2)
    s -= q * Nc(k - 3, q) + 2 * (q - 1) * Nc(k - 3, q - 1) + (q - 2) * Nc(k - 3, q - 2)
    return s


ok = all(pde_N(k, q) == {(0, 0): 1, (1, 0): -1, (3, 0): 1, (2, 2): 1}.get((k, q), 0)
         for k in range(KN + 1) for q in range(KN + 1))
report('c3a-N-pde', ok, 'Ncal PDE (1 - x(1+y) + x^3(1-y^2))N - x^3 y(1+y)^2 N_y = 1 - x + x^3 + x^2 y^2, coefficientwise k,q<=30')

# E3 三角递推（k>=3, q>=1）
ok = all(Nc(k, q) == Nc(k - 1, q - 1) + Nc(k - 1, q) + (q - 1) * (Nc(k - 3, q - 2) + 2 * Nc(k - 3, q - 1) + Nc(k - 3, q))
         for k in range(3, KN + 1) for q in range(1, KN + 1))
report('c3a-N-rec', ok, 'triangle recurrence N(k,q)=N(k-1,q-1)+N(k-1,q)+(q-1)[N(k-3,q-2)+2N(k-3,q-1)+N(k-3,q)] (k>=3,q>=1), k<=30')

# E4 原生 Laplace：Ntilde = 1+tF = (1/A) L_s[exp((t/x^3)(e^{vs}-1)) (A + x^2 t^2 e^{2vs}/(1-t e^{vs})^2)]，A=1-x+x^3，v=x^3/A；
#    Ncal(x,y) = Ntilde(x, y/(1+y))/(1+y)，即 [y^q] = sum_n Ntilde_n (-1)^{q-n} C(q,n)
t1 = time.time()
A = [1, -1, 0, 1]
gcols = []
for n in range(KN + 1):
    c = zero(KN)
    if n == 0:
        c[0], c[1], c[3] = 1, -1, 1
    elif n >= 2:
        c[2] = n - 1
    gcols.append(c)
Nt = laplace_solve(gcols, A, KN, KN)
ok = all(Nt[k][n] == ((1 if (k == 0 and n == 0) else 0) + (T60[k][n - 1] if n >= 1 else 0))
         for k in range(KN + 1) for n in range(KN + 1))
Nrep = [[sum(Nt[k][n] * (-1) ** (q - n) * comb(q, n) for n in range(q + 1)) for q in range(KN + 1)] for k in range(KN + 1)]
ok &= Nrep == Ntab
ok &= all(Nrep[k] == NB[k] for k in range(10))
report('c3a-N-lap', ok, 'native Laplace representation of Ntilde=1+tF (A=1-x+x^3) expanded exactly == 1+tF(DP), and '
       'Ncal(x,y)=Ntilde(x,y/(1+y))/(1+y) == N(k,q) (DP inversion k,q<=30; DFS k<=9) (%.1fs)' % (time.time() - t1))

# E5 Ncal 的 Humbert 形式：yh = -y/((1+y)x^3)，A = 1-x+x^3
#   Ncal = (1/(A(1+y))) [ (A+x^2) 1F1(1;-lam;yh) - 2x^2(1+y) Phi_1(1,1;-lam;-y,yh) + x^2(1+y)^2 Phi_1(1,2;-lam;-y,yh) ]
KQ, QQ = 40, 14
capN = KQ + 3 * QQ + 12
lamN = Lau.poly([1, -1], capN, shift=-3)
ONEN = Lau.poly([1], capN)
ZERON = Lau(0, [], capN)
ipN = []
pp = ONEN
for N in range(QQ + 1):
    ipN.append(pp.inv())
    pp = pp * (Lau.poly([N], capN) - lamN)        # (-lam)_{N+1}


def phi1_Ncal(be):
    out = [ZERON] * (QQ + 1)
    for m in range(QQ + 1):
        for n in range(QQ + 1 - m):
            N = m + n
            coef = Fraction(factorial(N)) * gpoch(be, m) / (factorial(m) * factorial(n)) * (-1) ** m * (-1) ** n
            base = ipN[N] * Lau.poly([coef], capN, shift=-3 * n)
            for r in range(QQ + 1 - N):
                c = (comb(n + r - 1, r) * (-1) ** r) if n > 0 else (1 if r == 0 else 0)
                if c:
                    out[N + r] = out[N + r] + base * Fraction(c)
    return out


def sermul_scalar(Aser, sc):
    out = [ZERON] * (QQ + 1)
    for i in range(QQ + 1):
        for j in range(QQ + 1 - i):
            if sc[j]:
                out[i + j] = out[i + j] + Aser[i] * sc[j]
    return out


AN = Lau.poly([1, -1, 0, 1], capN)
x2N = Lau.poly([1], capN, shift=2)
H0, H1, H2 = phi1_Ncal(0), phi1_Ncal(1), phi1_Ncal(2)
term0 = [(AN + x2N) * c for c in H0]
term1 = sermul_scalar([x2N * c * (-2) for c in H1], [Fraction(comb(1, r)) for r in range(QQ + 1)])
term2 = sermul_scalar([x2N * c for c in H2], [Fraction(comb(2, r)) for r in range(QQ + 1)])
innerN = [term0[q] + term1[q] + term2[q] for q in range(QQ + 1)]
NcalH = sermul_scalar(innerN, [Fraction((-1) ** r) for r in range(QQ + 1)])
ANinv = AN.inv()
TNH = U_fast_table(KQ, QQ + 1)
ok = True
for q in range(QQ + 1):
    ok &= lau_matches(NcalH[q] * ANinv, [N_from_U(TNH, k, q) for k in range(KQ + 1)], KQ)
report('c3a-N-humbert', ok, 'Humbert form Ncal(x,y) = [(A+x^2) 1F1(1;-lam;yh) - 2x^2(1+y)Phi_1(1,1;-lam;-y,yh) + x^2(1+y)^2 Phi_1(1,2;-lam;-y,yh)]/(A(1+y)), '
       'yh=-y/((1+y)x^3), A=1-x+x^3: expanded from the definitions == N(k,q) (DP inversion), k<=40, q<=14')

# =============================================================================
# F. H(z,t) = sum_k h_k(t) z^k
# =============================================================================
KH = 30


def h_from_U(k, deg=40):
    return [sum((-1) ** j * comb(k + 1, j) * T60[k][i - j] for j in range(0, min(i, k + 1) + 1)) for i in range(deg + 1)]


H = [h_from_U(k) for k in range(KH + 1)]


def trim_(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


okpoly = all(all(c == 0 for c in H[k][max(k, 1):]) for k in range(KH + 1))


def h_via_N(k, Nrow):
    r = [0] * 41
    for q in range(1, k + 1):
        for i in range(k - q + 1):
            r[q - 1 + i] += Nrow[q] * comb(k - q, i) * (-1) ** i
    return r


okN = all(h_via_N(k, Ntab[k]) == H[k] for k in range(1, KH + 1)) and all(h_via_N(k, NB[k]) == H[k] for k in range(1, 10))
report('c3a-H-poly', okpoly and okN, 'h_k(t) := (1-t)^{k+1} sum_m U_k(m) t^m is a polynomial of degree <= k-1 (coefficients t^k..t^40 vanish, k<=30) '
       'and h_k = sum_q N(k,q) t^{q-1}(1-t)^{k-q}, i.e. H(z,t) = 1 + (Ncal(z(1-t), t/(1-t)) - 1)/t (k<=30; DFS-N k<=9)')


def padd_(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pmul_(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def pder(p):
    return [i * p[i] for i in range(1, len(p))]


hp = [trim_(H[k]) for k in range(KH + 1)]
ok = True
for k in range(KH + 1):
    s = list(hp[k])
    if k >= 1:
        s = padd_(s, [-c for c in hp[k - 1]])
    if k >= 3:
        s = padd_(s, [-c for c in pmul_([0, 1, -1], hp[k - 3])])
        s = padd_(s, [-(k - 3) * c for c in pmul_([0, 1, -1], hp[k - 3])])
        s = padd_(s, [-c for c in pmul_([0, 1, -2, 1], pder(hp[k - 3]))])
    rhs = [1] if k == 0 else ([0, 1] if k == 2 else [])
    ok &= trim_(s) == rhs
report('c3a-H-pde', ok, 'H PDE (1 - z - z^3 t(1-t))H - z^4 t(1-t) H_z - z^3 t(1-t)^2 H_t = 1 + z^2 t, coefficient of z^k exact in t, k<=30')

# (C6) 递推从 h_0=1 出发生成，再对照 DP（H = (1-t)F(z(1-t),t) 的非平凡核对）
hr = [[1], [1], [1, 1]]
for k in range(3, KH + 1):
    a = hr[k - 3]
    term = padd_(pmul_([1, -1], pder(a)), [(k - 2) * c for c in a])
    hr.append(trim_(padd_(hr[k - 1], pmul_([0, 1, -1], term))))
ok = all(hr[k] == hp[k] for k in range(KH + 1))
report('c3a-H-rec', ok, '(C6) recurrence h_k = h_{k-1} + t(1-t)[(1-t)h\'_{k-3} + (k-2)h_{k-3}] from h_0=h_1=1, h_2=1+t '
       'reproduces (1-t)^{k+1} sum_m U_k(m) t^m from the DP, k<=30')

# =============================================================================
# G. 解析版本：严格的符号反例 + [NUM] 高精度数值证据
# =============================================================================
# G1（严格）：x=3/5, t=-1/2：I(x,t) > 0（被积函数为正，见笔记），而 S = sum_m t^m G_m(x) < 0（精确部分和 + 严格尾项界）
x, t = Fraction(3, 5), Fraction(-1, 2)
tot, Gs = S_exact(x, t, True, 400)
tb = S_tail_bound(x, t, True, Gs, 400)
ok = (tot + tb < 0)
report('c3a-analytic-counterex', ok, 'draft analytic claim F = x^{-3} int_0^inf ... refuted at (x,t)=(3/5,-1/2): '
       'S = sum_m t^m G_m(x) = (exact partial sum m<=400, approx %.10f) + tail, |tail| <= %.1e (rigorous bound), '
       'so S <= partial + bound < 0 while the integral is > 0' % (float(tot), float(tb)))
       # 2026-10-04 审计后改写说明文字：原来写成「<= -1057.810873 + 3.5e-118」，舍入方向反了（部分和是 -1057.81087256…）；判定逻辑 tot+tb<0 不变

# G2 [NUM]：I - S = x^{-3} K(x) e^a a^lambda 与 I0 - S0 = x^{-3} Gamma(-lambda) e^a a^lambda
getcontext().prec = 60
PI = pi_dec()
ok_c, ok_f, ok_g = True, True, True
worst_c, worst_f = D(0), D(0)
for (x, t) in [(Fraction(3, 5), Fraction(-1, 2)), (Fraction(2, 5), Fraction(-3, 10)), (Fraction(3, 10), Fraction(-1, 10))]:
    lam = (1 - x) / x ** 3
    I0, e0 = I_val(x, t, with_g=False)
    S0, _, _ = S_val(x, t, with_g=False)
    G1 = gamma_neg_reflect(dec(lam), PI)
    G2 = K_val(x, with_g=False)
    ok_g &= abs(G1 - G2) <= D(10) ** -45 * max(D(1), abs(G1))
    gap0 = predicted_gap(x, t, G1)
    r0 = abs(I0 - S0 - gap0) / max(D(1), abs(gap0))
    worst_c = max(worst_c, r0)
    ok_c &= r0 < D(10) ** -45
    I1, e1 = I_val(x, t, with_g=True)
    S1, _, _ = S_val(x, t, with_g=True)
    Kx = K_val(x, with_g=True)
    gap1 = predicted_gap(x, t, Kx)
    r1 = abs(I1 - S1 - gap1) / max(D(1), abs(gap1))
    worst_f = max(worst_f, r1)
    ok_f &= r1 < D(10) ** -40
report('c3a-num-gamma', ok_g, '[NUM] Gamma(-lambda) via reflection+Stirling == Prym decomposition sum_n (-1)^n/(n!(n-lambda)) + E_{lambda+1}(1) '
       'at lambda = 50/27, 75/8, 700/27 (60 digits, tol 1e-45 relative)')
report('c3a-num-gap-const', ok_c, '[NUM] I0 - sum_m t^m/P_m = x^{-3} Gamma(-lambda) e^a a^lambda at (x,t)=(3/5,-1/2),(2/5,-3/10),(3/10,-1/10); '
       'worst residual %.1E (tol 1e-45, relative to max(1,|gap|); 60-digit decimal quadrature)' % worst_c)
report('c3a-num-gap-full', ok_f, '[NUM] I - sum_m t^m G_m(x) = x^{-3} K(x) e^a a^lambda at the same 3 points; worst residual %.1E (tol 1e-40)' % worst_f)

# G3 [NUM]：x->0+ 渐近：I(21/100,-1/2) 与 sum_{k<150} f_k(t) x^k 相差 < 1e-50，而 |sum_m t^m G_m(x)| > 1e44
x, t = Fraction(21, 100), Fraction(-1, 2)
I1, e1 = I_val(x, t, with_g=True)
fk = fk_at(t, 150)
# 自检：Taylor 递推给出的 f_k(t) 与 DP 的 h_k(t)/(1-t)^{k+1} 一致（k<=30）
fk_ok = True
for k in range(31):
    hk = [sum((-1) ** j * comb(k + 1, j) * T60[k][i - j] for j in range(0, min(i, k + 1) + 1)) for i in range(max(k, 1))]
    fk_ok &= sum(Fraction(c) * t ** i for i, c in enumerate(hk)) / (1 - t) ** (k + 1) == fk[k]
part = sum(dec(fk[k]) * dec(x) ** k for k in range(150))
totS, GsS = S_exact(x, t, True, 500)
tbS = S_tail_bound(x, t, True, GsS, 500)
ok = fk_ok and abs(I1 - part) < D(10) ** -50 and abs(totS) - tbS > Fraction(10) ** 44
report('c3a-num-asym', ok, '[NUM] x->0+ asymptotics at (x,t)=(21/100,-1/2): |I - sum_{k<150} f_k(t) x^k| = %.1E < 1e-50 (f_k exact from the PDE, == DP h_k/(1-t)^{k+1} for k<=30), '
       'while |sum_m t^m G_m(x)| > 1e44 rigorously (it is %.3E)' % (abs(I1 - part), float(totS)))

# G4 [NUM]：小 |t| 时两者只差超越所有阶的项：(21/100,-1/20)，100 位精度，I - S 与预测 ~3.8e-62 相对误差 < 1e-25
getcontext().prec = 100
x, t = Fraction(21, 100), Fraction(-1, 20)
I1, e1 = I_val(x, t, with_g=True)
S1, _, _ = S_val(x, t, with_g=True)
getcontext().prec = 170          # K(x) ~ 5e-129 comes from cancellation of O(1) terms: needs ~170 digits
Kx = K_val(x, with_g=True)
getcontext().prec = 100
gap = predicted_gap(x, t, Kx)
rel = abs((I1 - S1 - gap) / gap)
report('c3a-num-small-t', rel < D(10) ** -25, '[NUM] at (x,t)=(21/100,-1/20): I - sum_m t^m G_m(x) = %.4E matches x^{-3}K e^a a^lambda with relative error %.1E '
       '(tol 1e-25; I,S with 100 digits, K with 170 digits)' % (I1 - S1, rel))

# G5 [NUM]：S(x,t) = sum_m t^m G_m(x) 在 x_i（1-x-i x^3 的正根）处的留数律
#   Res_{x_i} G_m = Res_{x_i} G_i * (-x_i^{-3})^{m-i}/(m-i)!（m>=i），故 Res_{x_i} S = Res_{x_i} G_i * t^i e^{-t/x_i^3}；且 Res_{x_i} G_i < 0
getcontext().prec = 60
ok = True
worst = D(0)
for i in (1, 2, 3, 4, 5):
    xi = D('0.5')
    for _ in range(100):
        xi = xi - (1 - xi - i * xi ** 3) / (-1 - 3 * i * xi ** 2)
    d = D(10) ** -25
    def Gl(xv, M):
        G = D(1); out = []
        for m in range(M + 1):
            G = (G + m * xv * xv) / (1 - xv - m * xv ** 3)
            out.append(G)
        return out
    Gp, Gm_ = Gl(xi + d, i + 8), Gl(xi - d, i + 8)
    res = [(Gp[m] - Gm_[m]) * d / 2 for m in range(i + 9)]
    ok &= res[i] < 0
    for m in range(i, i + 9):
        pred = res[i] * (-1 / xi ** 3) ** (m - i) / factorial(m - i)
        r = abs(res[m] - pred) / abs(pred)
        worst = max(worst, r)
        ok &= r < D(10) ** -40
report('c3a-num-residue', ok, '[NUM] residue law Res_{x_i}G_m = Res_{x_i}G_i (-x_i^{-3})^{m-i}/(m-i)! for i<=5, m<=i+8 '
       '(so Res_{x_i} sum_m t^m G_m = Res_{x_i}G_i t^i e^{-t/x_i^3}), Res_{x_i}G_i<0; worst rel dev %.1E (tol 1e-40, 60 digits)' % worst)

npass = sum(RESULTS)
nfail = len(RESULTS) - npass
print('# elapsed %.1fs' % (time.time() - T_START))
print('SUMMARY c3a pass=%d fail=%d' % (npass, nfail))
sys.exit(0 if nfail == 0 else 1)
