# -*- coding: utf-8 -*-
"""审计 a1-formulas 的公共工具（独立实现；core.py 只读引用作为「原始定义」真值源）。

真值来源：
  own_U_table(K, M)   —— 自写的高度 DP：逐个三元组检查 good(a,b,c)，O(K*(m+1)^3)，不用后缀和
  core.U_list / core.U_fast_table / core.U_multichain / core.a_direct / core.N_brute —— 原始定义程序
  own_N_dfs(k)        —— 自写 DFS：长 k、值域恰为 {0..q-1} 的合法词
大范围（k、m 到 ~250）才用引理 1 递推 lemma1_table（它先在小范围内与定义 DP 逐项比对）。
"""
import os
import sys
from fractions import Fraction
from math import comb, factorial
from functools import lru_cache

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))
import core  # noqa: E402  (只读)

RESULTS = []


def report(ok, cid, msg):
    RESULTS.append((bool(ok), cid, msg))
    print(('PASS ' if ok else 'FAIL ') + cid + ' :: ' + msg, flush=True)


def summary(tag):
    p = sum(1 for r in RESULTS if r[0])
    f = sum(1 for r in RESULTS if not r[0])
    print('SUMMARY %s pass=%d fail=%d' % (tag, p, f), flush=True)


def C(a, b):
    """报告的二项式约定：C(a,b)=0 除非 0<=b<=a（a<0 时也为 0）。"""
    if b < 0 or a < 0 or b > a:
        return 0
    return comb(a, b)


def Cgen(a, b):
    """广义二项式（上指标可为负整数），b>=0。"""
    if b < 0:
        return 0
    num = 1
    for i in range(b):
        num *= (a - i)
    return num // factorial(b) if num % factorial(b) == 0 else Fraction(num, factorial(b))


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def own_U_column(m, K):
    """自写高度 DP：[U_0(m),...,U_K(m)]。"""
    n = m + 1
    out = [1]
    if K >= 1:
        out.append(n)
    if K >= 2:
        out.append(n * n)
    if K <= 2:
        return out[:K + 1]
    cnt = [[1] * n for _ in range(n)]
    ok = [[[good(a, b, c) for c in range(n)] for b in range(n)] for a in range(n)]
    for _ in range(3, K + 1):
        new = [[0] * n for _ in range(n)]
        for a in range(n):
            for b in range(n):
                v = cnt[a][b]
                if v == 0:
                    continue
                okab = ok[a][b]
                row = new[b]
                for c in range(n):
                    if okab[c]:
                        row[c] += v
        cnt = new
        out.append(sum(map(sum, cnt)))
    return out


def own_U_table(K, M):
    cols = [own_U_column(m, K) for m in range(M + 1)]
    return [[cols[m][k] for m in range(M + 1)] for k in range(K + 1)]


def lemma1_table(K, M):
    """引理 1 递推（只在与定义 DP 比对过之后用于大范围）：T[k][m]。"""
    T = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        T[0][m] = 1
    for k in range(1, K + 1):
        for m in range(M + 1):
            prev = T[k][m - 1] if m >= 1 else 0
            km3 = k - 3
            if km3 >= 0:
                u3 = T[km3][m]
            elif km3 == -1:
                u3 = 1
            else:
                u3 = 0
            T[k][m] = prev + T[k - 1][m] + m * u3
    return T


def N_from_table(T, k, q):
    """N(k,q)=sum_i (-1)^(q-i) C(q,i) U_k(i-1)，U_0(-1)=1，U_k(-1)=0 (k>=1)。需要 q-1<=M。"""
    s = 0
    for i in range(q + 1):
        if i == 0:
            u = 1 if k == 0 else 0
        else:
            u = T[k][i - 1]
        s += (-1) ** (q - i) * comb(q, i) * u
    return s


def N_table_from_U(T, K):
    """NT[k][q]，0<=q<=k<=K（需要 T 至少有 m<=K-1 列）。"""
    return [[N_from_table(T, k, q) for q in range(K + 1)] for k in range(K + 1)]


def own_N_dfs(k):
    """自写 DFS：dict q -> N(k,q)（值域恰为 {0..q-1}）。"""
    res = {}
    if k == 0:
        return {0: 1}
    seq = []

    def rec():
        if len(seq) == k:
            s = set(seq)
            q = len(s)
            if max(seq) == q - 1:
                res[q] = res.get(q, 0) + 1
            return
        for v in range(k):
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec()
            seq.pop()
    rec()
    return res


# ------------------------- 多项式（系数列表，Fraction） -------------------------
def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def psub(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(n)])


def pscale(p, c):
    return trim([c * a for a in p])


def pmul(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            r[i + j] += a * b
    return trim(r)


def ppow(p, e):
    r = [1]
    for _ in range(e):
        r = pmul(r, p)
    return r


def peval(p, x):
    r = 0
    for a in reversed(p):
        r = r * x + a
    return r


def pdeg(p):
    p = trim(p)
    return len(p) - 1


def pdivmod(p, q):
    p = [Fraction(a) for a in trim(p)]
    q = [Fraction(a) for a in trim(q)]
    if len(p) < len(q):
        return [], trim(p)
    out = [Fraction(0)] * (len(p) - len(q) + 1)
    r = p[:]
    lq = q[-1]
    for i in range(len(p) - len(q), -1, -1):
        c = r[i + len(q) - 1] / lq
        out[i] = c
        if c:
            for j in range(len(q)):
                r[i + j] -= c * q[j]
    return trim(out), trim(r[:len(q) - 1])


def pgcd(p, q):
    a, b = trim([Fraction(x) for x in p]), trim([Fraction(x) for x in q])
    while b:
        _, r = pdivmod(a, b)
        a, b = b, r
    if not a:
        return []
    lc = a[-1]
    return [c / lc for c in a]


def pcompose_linear(p, a, b):
    """p(a*x+b)。"""
    r = []
    lin = [b, a]
    for c in reversed(p):
        r = padd(pmul(r, lin), [c])
    return r


def pderiv(p):
    return trim([i * p[i] for i in range(1, len(p))])


def interp(xs, ys):
    """Newton 插值，返回系数列表（Fraction）。"""
    n = len(xs)
    coef = [Fraction(y) for y in ys]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (xs[i] - xs[i - j])
    p = [Fraction(0)]
    for i in range(n - 1, -1, -1):
        p = padd(pmul(p, [-Fraction(xs[i]), Fraction(1)]), [coef[i]])
    return p


# ------------------------- 截断幂级数（x） -------------------------
def sinv(a, n):
    """1/a 截断到 x^(n-1)，a[0]!=0。"""
    a = list(a) + [0] * n
    inv = [Fraction(0)] * n
    inv[0] = Fraction(1, 1) / a[0]
    for i in range(1, n):
        s = 0
        for j in range(1, i + 1):
            if a[j]:
                s += a[j] * inv[i - j]
        inv[i] = -s * inv[0]
    return inv


def smul(a, b, n):
    r = [0] * n
    for i, x in enumerate(a[:n]):
        if x == 0:
            continue
        for j, y in enumerate(b[:n - i]):
            r[i + j] += x * y
    return r


def b_poly(i):
    """b_i(x)=1-x-i x^3。"""
    return [1, -1, 0, -i] if i != 0 else [1, -1]


def P_poly(m):
    p = [1]
    for i in range(0, m + 1):
        p = pmul(p, b_poly(i))
    return p


def W_poly(m):
    """W_m = 1 + x^2 * sum_{j=1}^m j P_{j-1}；W_{-1}=1。"""
    s = [1]
    for j in range(1, m + 1):
        s = padd(s, pshift(pscale(P_poly(j - 1), j), 2))
    return s


def pshift(p, k):
    return trim([0] * k + list(p)) if p else []


@lru_cache(maxsize=None)
def stirling2(n, k):
    if n == 0 and k == 0:
        return 1
    if n <= 0 or k <= 0 or k > n:
        return 0
    return k * stirling2(n - 1, k) + stirling2(n - 1, k - 1)


@lru_cache(maxsize=None)
def stirling1u(n, k):
    """无符号第一类 Stirling 数 c(n,k)。"""
    if n == 0 and k == 0:
        return 1
    if n <= 0 or k <= 0 or k > n:
        return 0
    return (n - 1) * stirling1u(n - 1, k) + stirling1u(n - 1, k - 1)


@lru_cache(maxsize=None)
def hcomp(s, lo, hi):
    """完全齐次对称多项式 h_s(lo..hi)，s<0 -> 0，空区间 h_0=1。独立递推实现。"""
    if s < 0:
        return 0
    if s == 0:
        return 1
    if lo > hi:
        return 0
    # h_s(lo..hi) = h_s(lo+1..hi) + lo*h_{s-1}(lo..hi)
    return hcomp(s, lo + 1, hi) + lo * hcomp(s - 1, lo, hi)


def c_seq(i, nmax):
    """c_i(n)=[x^n]1/(1-x-i x^3)，n=0..nmax（直接展开）。"""
    c = [0] * (nmax + 1)
    for n in range(nmax + 1):
        v = 1 if n == 0 else 0
        if n >= 1:
            v += c[n - 1]
        if n >= 3:
            v += i * c[n - 3]
        c[n] = v
    return c


def falling(a, j):
    r = 1
    for t in range(j):
        r *= (a - t)
    return r


def rising(a, j):
    r = 1
    for t in range(j):
        r *= (a + t)
    return r


def series_of_rational(num, den, n):
    return smul(num, sinv(den, n), n)


def bm_rational(seq):
    """Berlekamp–Massey over Q：返回连接多项式 C(x)（C[0]=1）与线性复杂度 L。"""
    s = [Fraction(v) for v in seq]
    Cp = [Fraction(1)]
    Bp = [Fraction(1)]
    L = 0
    mshift = 1
    b = Fraction(1)
    for n in range(len(s)):
        d = s[n]
        for i in range(1, L + 1):
            if i < len(Cp):
                d += Cp[i] * s[n - i]
        if d == 0:
            mshift += 1
            continue
        coef = d / b
        T = Cp[:]
        need = len(Bp) + mshift
        if len(Cp) < need:
            Cp = Cp + [Fraction(0)] * (need - len(Cp))
        for i in range(len(Bp)):
            Cp[i + mshift] -= coef * Bp[i]
        if 2 * L <= n:
            L = n + 1 - L
            Bp = T
            b = d
            mshift = 1
        else:
            mshift += 1
    return trim(Cp), L
