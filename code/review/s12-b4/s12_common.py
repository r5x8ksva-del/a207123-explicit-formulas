# -*- coding: utf-8 -*-
"""复核者 s12-b4 的公用工具（独立实现）。

只从 code/core.py 取 U_k(m) 的真值（U_fast_table）；其余（E、U^c 的计数、多项式、
Q[x]/(b_i) 中的约化、c_i 的双向延拓、线性方程组、p 进赋值）都是本文件自己写的，
不导入 code/tableB/ 下的任何脚本。
"""
import os
import sys
from fractions import Fraction as Fr
from math import comb, factorial

try:
    sys.stdout.reconfigure(encoding='utf-8')
    sys.stderr.reconfigure(encoding='utf-8')
except Exception:
    pass

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))
import core  # noqa: E402  （只用 U_fast_table 当真值）


# ---------------------------------------------------------------- 记账
class Checker:
    def __init__(self, name):
        self.name = name
        self.n_pass = 0
        self.n_fail = 0
        self.fails = []

    def check(self, label, ok, detail=''):
        tag = 'PASS' if ok else 'FAIL'
        if ok:
            self.n_pass += 1
        else:
            self.n_fail += 1
            self.fails.append(label)
        print(f'{tag} {label} {detail}'.rstrip())
        sys.stdout.flush()
        return ok

    def info(self, msg):
        print(f'     {msg}')
        sys.stdout.flush()

    def summary(self):
        print(f'== {self.name}: PASS {self.n_pass}, FAIL {self.n_fail}')
        if self.fails:
            print('   FAILED: ' + ', '.join(self.fails))
        sys.stdout.flush()
        return self.n_fail == 0


# ---------------------------------------------------------------- 组合
def C(a, b):
    """报告的二项式约定：除非 0<=b<=a，否则为 0。"""
    if b < 0 or a < 0 or b > a:
        return 0
    return comb(a, b)


def ff(i, j):
    """下降阶乘 i(i-1)...(i-j+1)。"""
    r = 1
    for t in range(j):
        r *= (i - t)
    return r


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b'\x00\x00'
    for q in range(2, int(n ** 0.5) + 1):
        if s[q]:
            s[q * q::q] = bytearray(len(s[q * q::q]))
    return [q for q in range(n + 1) if s[q]]


def vp(x, p):
    """有理数的 p 进赋值；0 返回 None（+inf）。"""
    x = Fr(x)
    if x == 0:
        return None
    n, d = abs(x.numerator), x.denominator
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    while d % p == 0:
        d //= p
        v -= 1
    return v


# ---------------------------------------------------------------- 多项式（系数表，下标=次数）
def ptrim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pscale(a, c):
    return [c * x for x in a]


def pmul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if y:
                r[i + j] += x * y
    return r


def pshift(a, s):
    return [0] * s + list(a)


def pderiv(a):
    return [i * a[i] for i in range(1, len(a))]


def peval(a, x):
    r = 0
    for c in reversed(a):
        r = r * x + c
    return r


def pdivmod(a, b):
    """Q 上的多项式带余除法。"""
    a = [Fr(x) for x in ptrim(a)]
    b = [Fr(x) for x in ptrim(b)]
    if not b:
        raise ZeroDivisionError
    q = [Fr(0)] * max(len(a) - len(b) + 1, 1)
    while len(a) >= len(b) and a:
        c = a[-1] / b[-1]
        k = len(a) - len(b)
        q[k] = c
        for i, y in enumerate(b):
            a[i + k] -= c * y
        a = ptrim(a)
    return ptrim(q), a


def pgcd(a, b):
    a, b = ptrim(a), ptrim(b)
    while b:
        _, r = pdivmod(a, b)
        a, b = b, r
    if not a:
        return a
    lc = Fr(a[-1])
    return [Fr(x) / lc for x in a]


def series_div(num, den, N):
    """num/den 的幂级数系数 [x^0..x^N]（den[0] != 0）。"""
    num = list(num) + [0] * (N + 1)
    d0 = Fr(den[0])
    out = []
    for n in range(N + 1):
        s = Fr(num[n])
        for j in range(1, min(n, len(den) - 1) + 1):
            if den[j]:
                s -= den[j] * out[n - j]
        out.append(s / d0)
    return out


# ---------------------------------------------------------------- 本项目的对象
def b_poly(v):
    return [1, -1, 0, -v]


def P_poly(m):
    r = [1]
    for v in range(m + 1):
        r = pmul(r, b_poly(v))
    return r


def W_poly(m):
    """W_m = 1 + x^2 Σ_{j=1}^m j P_{j-1}。"""
    r = [1]
    for j in range(1, m + 1):
        r = padd(r, pshift(pscale(P_poly(j - 1), j), 2))
    return ptrim(r)


def Wt_poly(i):
    """W̃_i = 1 + Σ_{j=1}^i j i^{(j)} x^{3j+2}。"""
    r = [0] * (3 * i + 3)
    r[0] = 1
    for j in range(1, i + 1):
        r[3 * j + 2] += j * ff(i, j)
    return ptrim(r)


def reduce_bi(poly, i):
    """在 K_i=Q[x]/(b_i)（i>=1）中把多项式约化成 (a0,a1,a2)，用 x^3=(1-x)/i 从高次往低次消。"""
    a = [Fr(c) for c in poly] + [Fr(0)] * 3
    for n in range(len(a) - 1, 2, -1):
        c = a[n]
        if c == 0:
            continue
        a[n] = Fr(0)
        a[n - 3] += c / i
        a[n - 2] -= c / i
    return (a[0], a[1], a[2])


def mul_x(vec, i):
    a0, a1, a2 = vec
    return (a2 / i, a0 - a2 / i, a1)


def mul_xinv(vec, i):
    # x^{-1} = 1 + i x^2
    a0, a1, a2 = vec
    return (a0 + a1, a2, i * a0)


def mul_xpow(vec, i, s):
    v = tuple(Fr(t) for t in vec)
    if s >= 0:
        for _ in range(s):
            v = mul_x(v, i)
    else:
        for _ in range(-s):
            v = mul_xinv(v, i)
    return v


def mulmat_K(vec, f):
    """首一化前的三次多项式 f（f[3]!=0）给出的 Q[x]/(f) 中「乘以 vec」的矩阵（列 = vec*x^j 的坐标）。"""
    f = [Fr(t) for t in f]
    lc = f[3]

    def red(poly):
        a = [Fr(c) for c in poly] + [Fr(0)] * 3
        for n in range(len(a) - 1, 2, -1):
            c = a[n]
            if c == 0:
                continue
            a[n] = Fr(0)
            for t in range(3):
                a[n - 3 + t] -= c * f[t] / lc
        return a[:3]
    cols = []
    for j in range(3):
        cols.append(red(pshift(list(vec), j)))
    return [[cols[j][r] for j in range(3)] for r in range(3)]


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def norm_K(poly, f):
    """Q[x]/(f) 中 poly 的范数（乘法矩阵的行列式）。"""
    return det3(mulmat_K(poly, f))


# ---------------------------------------------------------------- c_i 与双向延拓
def c_seq(i, N):
    """c_i(0..N)，c_i(n)=[x^n]1/(1-x-i x^3)。"""
    c = []
    for n in range(N + 1):
        if n == 0:
            c.append(1)
        else:
            c.append(c[n - 1] + (i * c[n - 3] if n >= 3 else 0))
    return c


def c_at(cs, n):
    return cs[n] if n >= 0 else 0


def cbar_neg(i, nmax):
    """d[n] = c̄_i(-n)，0<=n<=nmax，由递推向负方向解：c̄(n-3)=(c̄(n)-c̄(n-1))/i。"""
    vals = {0: Fr(1), 1: Fr(1), 2: Fr(1)}   # c̄(0),c̄(1),c̄(2)
    for n in range(2, -nmax - 1, -1):        # 求 c̄(n-3)
        vals[n - 3] = (vals[n] - vals[n - 1]) / i
    return [vals[-n] for n in range(nmax + 1)]


# ---------------------------------------------------------------- 真值表
def good(a, b, c):
    return b == c or (a >= b and a >= c)


def tables_UEc(K, M):
    """自写的「最后两项」DP：返回 U[k][m]、E[k][m]（以上升 a_{k-1}<a_k 结尾）、Uc[k][m]。"""
    U = [[0] * (M + 1) for _ in range(K + 1)]
    E = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        n = m + 1
        U[0][m] = 1
        if K >= 1:
            U[1][m] = n
        if K < 2:
            continue
        cnt = {(a, b): 1 for a in range(n) for b in range(n)}
        U[2][m] = n * n
        E[2][m] = sum(1 for (a, b) in cnt if a < b)
        for k in range(3, K + 1):
            new = {}
            for (a, b), val in cnt.items():
                for c in range(n):
                    if good(a, b, c):
                        new[(b, c)] = new.get((b, c), 0) + val
            cnt = new
            U[k][m] = sum(cnt.values())
            E[k][m] = sum(val for (a, b), val in cnt.items() if a < b)
    Uc = [[U[k][m] - E[k][m] for m in range(M + 1)] for k in range(K + 1)]
    return U, E, Uc


def U_core(K, M):
    return core.U_fast_table(K, M)


# ---------------------------------------------------------------- 线性方程组
MODP = (1 << 61) - 1


def _rank_mod(rows, ncols, p=MODP):
    rows = [[x % p for x in r] for r in rows]
    rank = 0
    col = 0
    nrows = len(rows)
    while rank < nrows and col < ncols:
        piv = None
        for r in range(rank, nrows):
            if rows[r][col]:
                piv = r
                break
        if piv is None:
            col += 1
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], p - 2, p)
        pr = rows[rank]
        for r in range(nrows):
            if r != rank and rows[r][col]:
                f = rows[r][col] * inv % p
                rr = rows[r]
                for c in range(col, len(rr)):
                    rr[c] = (rr[c] - f * pr[c]) % p
        rank += 1
        col += 1
    return rank


def exact_solve(A, b):
    """Q 上精确消元。返回 (consistent, rank, solution 或 None)。"""
    nr = len(A)
    nc = len(A[0]) if nr else 0
    M = [[Fr(x) for x in A[r]] + [Fr(b[r])] for r in range(nr)]
    piv_cols = []
    rank = 0
    for col in range(nc):
        piv = None
        for r in range(rank, nr):
            if M[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        pv = M[rank][col]
        M[rank] = [x / pv for x in M[rank]]
        for r in range(nr):
            if r != rank and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[rank])]
        piv_cols.append(col)
        rank += 1
        if rank == nr:
            break
    for r in range(rank, nr):
        if M[r][nc] != 0:
            return False, rank, None
    sol = [Fr(0)] * nc
    for r, col in enumerate(piv_cols):
        sol[col] = M[r][nc]
    return True, rank, sol


def system_status(A, b):
    """整数方程组 A s = b 是否在 Q 上相容。
    'inconsistent-cert'：模 2^61-1 满列秩且增广秩更大（⇒ Q 上不相容，见复核报告的论证）；
    否则退回精确消元，返回 'consistent' 或 'inconsistent-exact'。"""
    nc = len(A[0]) if A else 0
    if nc == 0:
        return 'consistent' if all(x == 0 for x in b) else 'inconsistent-exact'
    rA = _rank_mod(A, nc)
    rAb = _rank_mod([list(r) + [x] for r, x in zip(A, b)], nc + 1)
    if rA == nc and rAb > rA:
        return 'inconsistent-cert'
    ok, _, _ = exact_solve(A, b)
    return 'consistent' if ok else 'inconsistent-exact'


# ---------------------------------------------------------------- ξ
def xi_float():
    x = 0.68
    for _ in range(60):
        x -= (x ** 3 + x - 1) / (3 * x * x + 1)
    return x
