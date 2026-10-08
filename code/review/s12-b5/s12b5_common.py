# -*- coding: utf-8 -*-
"""s12-b5 复核者的公共工具（2026-10-08）。不导入作者的 code/tableB/*（check_b4、check_b5 等）。

真值：
  direct_counts(K, Q)   —— 自写 DP，按定义数「长 k、值集恰为 {0..q-1}、每个相邻三元组 (a,b,c) 满足 b==c 或 a>=max(b,c)」
                           的词，并按「是否以上升结尾（k>=2 且 w[k-2]<w[k-1]）」分类；状态 = (倒数第二个值, 最后一个值, 已用值集合)。
  classified_U(K, M)    —— 自写 DP，数值域含于 {0..m} 的合法词 U_k(m)，以及其中以上升结尾的 E_k(m)。
  ie_tables(...)        —— 由 classified_U 经容斥得到 N、N^c、N^E（只作为扩大范围的手段；在 k<=30 上与 direct_counts 逐项对照）。
其余：多项式（低次在前）、Q[x]/(f) 中的运算与范数（乘法矩阵行列式，Fraction 精确）、Z[x]/(x^3+x-1) 的整数运算、
数值求根与围道积分。只用标准库与 numpy（numpy 只用于求根初值）。
"""
import sys
from fractions import Fraction as Fr
from math import comb, factorial

if not sys.stdout.isatty():
    try:
        sys.stdout.reconfigure(encoding='utf-8')
    except Exception:
        pass

RESULTS = []


def report(ok, tag, msg):
    RESULTS.append((bool(ok), tag))
    print(('PASS ' if ok else 'FAIL ') + tag + ' ' + msg, flush=True)


def summary(name):
    p = sum(1 for ok, _ in RESULTS if ok)
    f = sum(1 for ok, _ in RESULTS if not ok)
    print('SUMMARY %s pass=%d fail=%d' % (name, p, f), flush=True)
    return f


# ---------------------------------------------------------------- 组合
def C(n, k):
    """组合约定：除非 0<=k<=n，否则为 0。"""
    if k < 0 or n < 0 or k > n:
        return 0
    return comb(n, k)


def ffall(n, j):
    r = 1
    for t in range(j):
        r *= (n - t)
    return r


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def direct_counts(K, Q):
    """返回 (N, NE)，N[k][q]、NE[k][q]（0<=k<=K，0<=q<=Q）。NE：以上升结尾。"""
    N = [[0] * (Q + 1) for _ in range(K + 1)]
    NE = [[0] * (Q + 1) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1          # 只有词 (0)
    if K < 2:
        return N, NE
    allowed = [[[c for c in range(Q) if good(a, b, c)] for b in range(Q)] for a in range(Q)]
    cur = {}
    for a in range(Q):
        for b in range(Q):
            key = (a, b, (1 << a) | (1 << b))
            cur[key] = cur.get(key, 0) + 1

    def tally(k, st):
        for (a, b, m), v in st.items():
            if m & (m + 1) == 0:             # m = 2^q - 1，值集恰为 {0..q-1}
                q = m.bit_length()
                N[k][q] += v
                if a < b:
                    NE[k][q] += v
    tally(2, cur)
    for k in range(3, K + 1):
        new = {}
        for (a, b, m), v in cur.items():
            for c in allowed[a][b]:
                key = (b, c, m | (1 << c))
                new[key] = new.get(key, 0) + v
        cur = new
        tally(k, cur)
    return N, NE


def classified_U(K, M):
    """U[k][m]：值域含于 {0..m} 的合法词数；UE[k][m]：其中以上升结尾的。0<=k<=K，0<=m<=M。"""
    U = [[0] * (M + 1) for _ in range(K + 1)]
    UE = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        n = m + 1
        U[0][m] = 1
        if K >= 1:
            U[1][m] = n
        if K >= 2:
            cnt = [[1] * n for _ in range(n)]
            U[2][m] = n * n
            UE[2][m] = n * (n - 1) // 2
            for k in range(3, K + 1):
                new = [[0] * n for _ in range(n)]
                for a in range(n):
                    for b in range(n):
                        v = cnt[a][b]
                        if v:
                            for c in range(n):
                                if good(a, b, c):
                                    new[b][c] += v
                cnt = new
                U[k][m] = sum(map(sum, cnt))
                UE[k][m] = sum(cnt[a][b] for a in range(n) for b in range(a + 1, n))
    return U, UE


def ie_tables(K, Q):
    """由 classified_U 经容斥 N(k,q)=sum_{i=0}^q (-1)^{q-i} C(q,i) X_k(i-1) 得到 N、Nc、NE（0<=k<=K，0<=q<=Q）。
    X_k(-1)：U 与 U^c 取 [k==0]，E 取 0。"""
    U, UE = classified_U(K, max(Q - 1, 0))

    def X(tab, k, m, km1):
        if m < 0:
            return km1
        return tab[k][m]
    N = [[0] * (Q + 1) for _ in range(K + 1)]
    Nc = [[0] * (Q + 1) for _ in range(K + 1)]
    NE = [[0] * (Q + 1) for _ in range(K + 1)]
    for k in range(K + 1):
        for q in range(Q + 1):
            s = sc = se = 0
            for i in range(q + 1):
                sg = (-1) ** (q - i) * comb(q, i)
                u = X(U, k, i - 1, 1 if k == 0 else 0)
                e = X(UE, k, i - 1, 0)
                s += sg * u
                se += sg * e
                sc += sg * (u - e)
            N[k][q], Nc[k][q], NE[k][q] = s, sc, se
    return N, Nc, NE


# ---------------------------------------------------------------- c_i、w_i
def c_seq(i, nmax):
    """c_i(n)=[x^n]1/(1-x-i x^3)，0<=n<=nmax（i>=0）。"""
    c = [0] * (nmax + 1)
    for n in range(nmax + 1):
        if n == 0:
            c[n] = 1
        else:
            c[n] = c[n - 1] + (i * c[n - 3] if n >= 3 else 0)
    return c


class CI:
    """c_i(n)，n<0 时为 0。"""
    def __init__(self, nmax):
        self.nmax = nmax
        self.cache = {}

    def __call__(self, i, n):
        if n < 0:
            return 0
        if i not in self.cache:
            self.cache[i] = c_seq(i, self.nmax)
        return self.cache[i][n]


def w_atom(ci, i, n, drop_top=False):
    """w_i(n)=c_i(n)+sum_{j=1}^{i} j i^(j falling) c_i(n-3j-2)。drop_top：去掉 j=i 项（反向检查用）。"""
    s = ci(i, n)
    for j in range(1, i + 1):
        if drop_top and j == i:
            continue
        s += j * ffall(i, j) * ci(i, n - 3 * j - 2)
    return s


# ---------------------------------------------------------------- 多项式（低次在前）
def ptrim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return ptrim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def pscale(p, a):
    return ptrim([a * c for c in p])


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    r[i + j] += a * b
    return ptrim(r)


def pderiv(p):
    return ptrim([i * p[i] for i in range(1, len(p))] or [0])


def b_poly(v):
    return [1, -1, 0, -v]


def P_poly(m):
    p = [1]
    for v in range(m + 1):
        p = pmul(p, b_poly(v))
    return p


def Wtil_poly(i):
    """W~_i(x)=1+sum_{j=1}^i j i^(j falling) x^(3j+2)。"""
    p = [0] * (3 * i + 3)
    p[0] = 1
    for j in range(1, i + 1):
        p[3 * j + 2] = j * ffall(i, j)
    return ptrim(p)


def peval(p, x):
    r = 0
    for c in reversed(p):
        r = r * x + c
    return r


# ---------------------------------------------------------------- Q[x]/(f)，f 三次（首项可不为 1）
class Cubic:
    """K=Q[x]/(f)，f=f0+f1 x+f2 x^2+f3 x^3（f3!=0）。元素：长度 3 的 Fraction 列表。"""

    def __init__(self, f):
        self.f = [Fr(c) for c in f]
        assert len(self.f) == 4 and self.f[3] != 0
        f0, f1, f2, f3 = self.f
        # x^3 = -(f0+f1 x+f2 x^2)/f3
        self.x3 = [-f0 / f3, -f1 / f3, -f2 / f3]

    def red(self, p):
        p = [Fr(c) for c in p]
        while len(p) > 3:
            top = p.pop()
            d = len(p) - 3           # top * x^(d+3) = top * x^d * x^3
            for t in range(3):
                p[d + t] += top * self.x3[t]
        while len(p) < 3:
            p.append(Fr(0))
        return p

    def mul(self, a, b):
        r = [Fr(0)] * 5
        for i in range(3):
            if a[i]:
                for j in range(3):
                    if b[j]:
                        r[i + j] += a[i] * b[j]
        return self.red(r)

    def mat(self, a):
        """乘以 a 的矩阵（列 = a*1, a*x, a*x^2 的坐标）。"""
        cols = [self.red([0] * j + list(a)) for j in range(3)]
        return [[cols[j][i] for j in range(3)] for i in range(3)]

    def norm(self, a):
        return det3(self.mat(a))

    def inv(self, a):
        M = self.mat(a)
        sol = solve3(M, [Fr(1), Fr(0), Fr(0)])
        return sol

    def poly(self, p):
        return self.red(p)

    def xpow(self, n):
        """x^n（n 可为负；要求 x 可逆，即 f0!=0）。"""
        if n >= 0:
            r = [Fr(1), Fr(0), Fr(0)]
            base = [Fr(0), Fr(1), Fr(0)]
            e = n
        else:
            r = [Fr(1), Fr(0), Fr(0)]
            base = self.inv([Fr(0), Fr(1), Fr(0)])
            e = -n
        while e:
            if e & 1:
                r = self.mul(r, base)
            base = self.mul(base, base)
            e >>= 1
        return r


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def solve3(M, rhs):
    A = [[Fr(M[i][j]) for j in range(3)] + [Fr(rhs[i])] for i in range(3)]
    for c in range(3):
        piv = next(r for r in range(c, 3) if A[r][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]
        A[c] = [v / pv for v in A[c]]
        for r in range(3):
            if r != c and A[r][c] != 0:
                fct = A[r][c]
                A[r] = [x - fct * y for x, y in zip(A[r], A[c])]
    return [A[i][3] for i in range(3)]


# ---------------------------------------------------------------- 赋值、立方
def vp_int(n, p):
    if n == 0:
        return None
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def vp_frac(x, p):
    x = Fr(x)
    if x == 0:
        return None
    return vp_int(x.numerator, p) - vp_int(x.denominator, p)


def icbrt(n):
    """整数立方根（n>=0），返回 floor(n^(1/3))。"""
    if n < 0:
        raise ValueError
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + 2) // 3)
    while True:
        y = (2 * x + n // (x * x)) // 3
        if y >= x:
            break
        x = y
    while x * x * x > n:
        x -= 1
    while (x + 1) ** 3 <= n:
        x += 1
    return x


def is_int_cube(n):
    a = abs(n)
    r = icbrt(a)
    return r * r * r == a


def is_rat_cube(x):
    x = Fr(x)
    return is_int_cube(x.numerator) and is_int_cube(x.denominator)


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b'\x00\x00'
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


# ---------------------------------------------------------------- 精确线性方程组
def consistent_exact(rows, rhs):
    """Fraction 高斯消元。返回 (相容?, 系数矩阵的秩, 解(自由变量取 0) 或 None)。"""
    m = len(rows)
    n = len(rows[0]) if m else 0
    A = [[Fr(v) for v in r] + [Fr(b)] for r, b in zip(rows, rhs)]
    piv_cols = []
    r = 0
    for c in range(n):
        p = None
        for i in range(r, m):
            if A[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [v / pv for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                fct = A[i][c]
                A[i] = [x - fct * y for x, y in zip(A[i], A[r])]
        piv_cols.append(c)
        r += 1
        if r == m:
            break
    for i in range(r, m):
        if A[i][n] != 0:
            return False, r, None
    sol = [Fr(0)] * n
    for i, c in enumerate(piv_cols):
        sol[c] = A[i][n]
    return True, r, sol


# ---------------------------------------------------------------- 数值
def roots_cubic_b(v):
    """b_v 的三个复根（numpy 初值 + 复数 Newton 加细）。"""
    import numpy as np
    rs = np.roots([-v, 0, -1, 1])
    out = []
    for z in rs:
        z = complex(z)
        for _ in range(60):
            f = 1 - z - v * z ** 3
            d = -1 - 3 * v * z ** 2
            z2 = z - f / d
            if abs(z2 - z) < 1e-17 * max(1.0, abs(z)):
                z = z2
                break
            z = z2
        out.append(z)
    return out


def contour_residue(fun, center, radius, npts=512):
    """(1/2πi)∮ fun，圆心 center、半径 radius，梯形公式（对解析周期函数指数收敛）。"""
    import cmath
    s = 0j
    for j in range(npts):
        e = cmath.exp(2j * cmath.pi * j / npts)
        s += fun(center + radius * e) * e
    return s * radius / npts
