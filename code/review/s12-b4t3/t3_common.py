# -*- coding: utf-8 -*-
"""复核者 s12-b4t3 的公用工具（全部自写，不导入项目里的任何模块）。

约定（与 notes/12 相同）：
  b_v = 1 - x - v x^3，P_m = b_0 ... b_m，W_m = 1 + x^2 * sum_{j=1}^m j P_{j-1}；
  W~_i = 1 + sum_{j=1}^i j * i(i-1)...(i-j+1) * x^{3j+2}；
  K_i = Q[x]/(b_i)，元素用基 (1, x, x^2) 下的坐标 [a0, a1, a2] 表示，x^3 = (1 - x)/i，x^{-1} = 1 + i x^2。
真值 U_k(m)、N(k,q) 一律按定义计数（相邻三元组 (a,b,c) 合法 <=> b==c 或 a>=max(b,c)）。
"""
import sys
from fractions import Fraction as Fr
from itertools import product
from math import comb, factorial


def setup_utf8():
    try:
        sys.stdout.reconfigure(encoding='utf-8')
    except Exception:
        pass


class Reporter:
    def __init__(self, tag):
        self.tag = tag
        self.npass = 0
        self.nfail = 0

    def check(self, cid, ok, desc=''):
        print(('PASS ' if ok else 'FAIL ') + cid + ' ' + desc, flush=True)
        if ok:
            self.npass += 1
        else:
            self.nfail += 1
        return ok

    def finish(self):
        print('SUMMARY %s pass=%d fail=%d' % (self.tag, self.npass, self.nfail), flush=True)
        sys.exit(1 if self.nfail else 0)


# ---------------------------------------------------------------- 按定义计数
def legal(a, b, c):
    return b == c or a >= max(b, c)


def U_dp(m, K):
    """U_k(m)，k=0..K：长 k、取值 {0..m}、每个相邻三元组合法的序列数（按定义的 DP，状态是最后两项）。"""
    out = [1]
    if K >= 1:
        out.append(m + 1)
    if K >= 2:
        out.append((m + 1) ** 2)
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    for _k in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if legal(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
        cnt = new
        out.append(sum(cnt.values()))
    return out[:K + 1]


def U_brute(m, k):
    """直接枚举全部 (m+1)^k 个序列（只用于小参数，核对 DP）。"""
    tot = 0
    for s in product(range(m + 1), repeat=k):
        if all(legal(s[t], s[t + 1], s[t + 2]) for t in range(k - 2)):
            tot += 1
    return tot


def N_dp(q, K):
    """N(k,q)，k=0..K：长 k、值域恰为 {1..q} 的合法词数（按定义的 DP，状态是（最后两项, 已用值的集合））。"""
    full = (1 << q) - 1
    out = [1 if q == 0 else 0]
    if K == 0:
        return out
    out.append(1 if q == 1 else 0)          # k=1：只有 q=1 时有一个词
    if K == 1:
        return out
    cnt = {}
    for a in range(1, q + 1):
        for b in range(1, q + 1):
            key = (a, b, (1 << (a - 1)) | (1 << (b - 1)))
            cnt[key] = cnt.get(key, 0) + 1
    out.append(sum(v for (a, b, S), v in cnt.items() if S == full))
    for _k in range(3, K + 1):
        new = {}
        for (a, b, S), v in cnt.items():
            for c in range(1, q + 1):
                if legal(a, b, c):
                    key = (b, c, S | (1 << (c - 1)))
                    new[key] = new.get(key, 0) + v
        cnt = new
        out.append(sum(v for (a, b, S), v in cnt.items() if S == full))
    return out[:K + 1]


def N_brute(q, k):
    tot = 0
    for s in product(range(1, q + 1), repeat=k):
        if set(s) == set(range(1, q + 1)) and all(legal(s[t], s[t + 1], s[t + 2]) for t in range(k - 2)):
            tot += 1
    return tot


# ---------------------------------------------------------------- 多项式（系数列表，低次在前）
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pscale(a, c):
    return [c * x for x in a]


def b_poly(v):
    return [1, -1, 0, -v]


def P_poly(m):
    p = [1]
    for v in range(m + 1):
        p = pmul(p, b_poly(v))
    return p


def W_poly(m):
    acc = [1]
    for j in range(1, m + 1):
        acc = padd(acc, pscale([0, 0] + P_poly(j - 1), j))
    return acc


def falling(i, j):
    r = 1
    for t in range(j):
        r *= (i - t)
    return r


def Wt_dict(i):
    """W~_i 作为 {指数: 系数}。"""
    d = {0: 1}
    for j in range(1, i + 1):
        d[3 * j + 2] = d.get(3 * j + 2, 0) + j * falling(i, j)
    return d


def series_div(num, den, K):
    """num/den 的幂级数系数（den[0] = ±1 或非零），到 x^K，Fraction。"""
    out = []
    d0 = Fr(den[0])
    for k in range(K + 1):
        s = Fr(num[k]) if k < len(num) else Fr(0)
        for j in range(1, min(k, len(den) - 1) + 1):
            s -= den[j] * out[k - j]
        out.append(s / d0)
    return out


# ---------------------------------------------------------------- c_i 与双向延拓
def c_seq(i, N):
    """c_i(n)=[x^n]1/b_i，n=0..N（i>=0；i=0 时恒为 1）。"""
    c = []
    for n in range(N + 1):
        if n == 0:
            c.append(1)
        else:
            v = c[n - 1]
            if n >= 3:
                v += i * c[n - 3]
            c.append(v)
    return c


class CBar:
    """c~_i: Z -> Q，满足 c(n)=c(n-1)+i c(n-3)，n>=0 时等于 c_i(n)。负方向：c(n-3)=(c(n)-c(n-1))/i。"""
    def __init__(self, i, npos=400, nneg=60):
        assert i >= 1
        self.i = i
        self.pos = [Fr(v) for v in c_seq(i, npos)]
        # c_i(0)=c_i(1)=c_i(2)=1；向负方向解递推：c(n-3) = (c(n) - c(n-1))/i，n = 2,1,0,-1,...
        vals = {0: Fr(1), 1: Fr(1), 2: Fr(1)}
        for n in range(2, -nneg + 2, -1):
            vals[n - 3] = (vals[n] - vals[n - 1]) / i
        self.vals = vals

    def __call__(self, n):
        if n >= 0:
            return self.pos[n]
        return self.vals[n]


# ---------------------------------------------------------------- K_i = Q[x]/(b_i) 精确运算
class KField:
    """K_i 中的精确运算（Fraction 坐标）。x 的幂用线性递推求坐标：
       x^{e+3} = (x^e - x^{e+1})/i（e>=0 方向），x^e = i x^{e+3} + x^{e+1}（负方向）。"""
    def __init__(self, i):
        self.i = i
        self.pw = {0: (Fr(1), Fr(0), Fr(0)), 1: (Fr(0), Fr(1), Fr(0)), 2: (Fr(0), Fr(0), Fr(1))}
        self.hi = 2
        self.lo = 0

    def xpow(self, e):
        while e > self.hi:
            n = self.hi + 1          # x^n = (x^{n-3} - x^{n-2})/i
            a, b = self.pw[n - 3], self.pw[n - 2]
            self.pw[n] = tuple((a[t] - b[t]) / self.i for t in range(3))
            self.hi = n
        while e < self.lo:
            n = self.lo - 1          # x^n = i x^{n+3} + x^{n+1}
            a, b = self.pw[n + 3], self.pw[n + 1]
            self.pw[n] = tuple(self.i * a[t] + b[t] for t in range(3))
            self.lo = n
        return self.pw[e]

    def from_dict(self, d):
        acc = [Fr(0)] * 3
        for e, c in d.items():
            v = self.xpow(e)
            for t in range(3):
                acc[t] += c * v[t]
        return tuple(acc)

    def mul(self, a, b):
        r = [Fr(0)] * 5
        for p in range(3):
            if a[p]:
                for q in range(3):
                    r[p + q] += a[p] * b[q]
        acc = [r[0], r[1], r[2]]
        for e in (3, 4):
            if r[e]:
                v = self.xpow(e)
                for t in range(3):
                    acc[t] += r[e] * v[t]
        return tuple(acc)

    def mulmat(self, a):
        """乘以 a 的矩阵（列 = a*1, a*x, a*x^2 的坐标）。"""
        cols = [self.mul(a, self.xpow(e)) for e in range(3)]
        return [[cols[c][r] for c in range(3)] for r in range(3)]

    def norm(self, a):
        return det3(self.mulmat(a))

    def inv(self, a):
        M = self.mulmat(a)
        return tuple(solve3(M, [Fr(1), Fr(0), Fr(0)]))

    def reduce_poly(self, coeffs, shift=0):
        """系数列表（低次在前，可整体乘 x^shift）约化到 K_i。"""
        return self.from_dict({e + shift: c for e, c in enumerate(coeffs) if c})


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def det3cols(u, v, w):
    """以 u, v, w 为列（或行，行列式相同）的 3x3 行列式。"""
    return det3([[u[0], v[0], w[0]], [u[1], v[1], w[1]], [u[2], v[2], w[2]]])


def solve3(M, rhs):
    """Fraction 高斯消元解 3x3 方程组。"""
    A = [[Fr(M[r][c]) for c in range(3)] + [Fr(rhs[r])] for r in range(3)]
    for c in range(3):
        piv = next(r for r in range(c, 3) if A[r][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        for r in range(3):
            if r != c and A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [A[r][t] - f * A[c][t] for t in range(4)]
    return [A[r][3] / A[r][r] for r in range(3)]


def in_span2(K, w, e1, e2):
    """w 是否属于 span_Q(x^e1, x^e2)（K 中）；返回 (bool, (lam, mu))。"""
    u, v = K.xpow(e1), K.xpow(e2)
    if det3cols(w, u, v) != 0:
        return False, None
    # 解 lam*u + mu*v = w（两列线性无关时唯一）
    for (r1, r2) in ((0, 1), (0, 2), (1, 2)):
        dd = u[r1] * v[r2] - u[r2] * v[r1]
        if dd != 0:
            lam = (w[r1] * v[r2] - w[r2] * v[r1]) / dd
            mu = (u[r1] * w[r2] - u[r2] * w[r1]) / dd
            ok = all(lam * u[t] + mu * v[t] == w[t] for t in range(3))
            return ok, (lam, mu)
    return False, None


# ---------------------------------------------------------------- 素数与赋值
def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def factorize(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def vp_int(n, p):
    if n == 0:
        return 10 ** 9
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def vp_frac(x, p):
    x = Fr(x)
    if x == 0:
        return 10 ** 9
    return vp_int(x.numerator, p) - vp_int(x.denominator, p)


def frac_mod(x, mod):
    """有理数 x（分母与 mod 互素）模 mod 的值。"""
    x = Fr(x)
    return x.numerator * pow(x.denominator, -1, mod) % mod
