# -*- coding: utf-8 -*-
"""r-c1 复核用的独立小工具库。

刻意不调用 core.py / polylib.py 的任何函数（只有在脚本里做「交叉对照」时才导入 core）。
所有计数从第 1 节原始定义出发，自写实现：
  - good / good_rows：三元组条件（good_rows 直接按「高度列的每一行都不是 001/010」逐行字面检查）
  - U_column：高度 DP（状态 = 最后两项 (a,b)；转移规则写成 (a>=b 且 c<=a) 或 (a<b 且 c==b)，
    用差分数组做区间加法；与 core 的「对 a 求后缀和」写法不同）
  - 精确多项式（int / Fraction 系数列表，p[i] 为 x^i 系数）、截断级数、模 p 的 Berlekamp–Massey
"""
from fractions import Fraction
from math import comb, factorial
import sys

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass


# ---------------------------------------------------------------------------
# 定义级
# ---------------------------------------------------------------------------
def good(a, b, c):
    return b == c or (a >= b and a >= c)


def good_rows(a, b, c):
    """高度 (a,b,c) 的三列：第 r 行读 ([r<=a],[r<=b],[r<=c])；任何一行都不是 001、也不是 010。"""
    for r in range(1, max(a, b, c) + 1):
        t = (r <= a, r <= b, r <= c)
        if t == (False, False, True) or t == (False, True, False):
            return False
    return True


def legal_next(a, b, c):
    """U_column 用的转移规则（与 good 等价，单独核对）。"""
    return c <= a if a >= b else c == b


def U_column(m, K):
    """[U_0(m), ..., U_K(m)]（m>=0）。"""
    out = [1]
    if K == 0:
        return out
    out.append(m + 1)
    if K == 1:
        return out
    n = m + 1
    cnt = [[1] * n for _ in range(n)]          # cnt[a][b]：最后两项为 (a,b)
    out.append(n * n)
    for _ in range(3, K + 1):
        new = [[0] * n for _ in range(n)]      # new[b][c]
        for b in range(n):
            diff = [0] * (n + 1)
            row = new[b]
            for a in range(n):
                v = cnt[a][b]
                if v:
                    if a >= b:
                        diff[0] += v
                        diff[a + 1] -= v
                    else:
                        row[b] += v
            acc = 0
            for c in range(n):
                acc += diff[c]
                if acc:
                    row[c] += acc
        cnt = new
        out.append(sum(map(sum, cnt)))
    return out


def U_table(K, M):
    """T[k][m]，0<=k<=K，0<=m<=M。"""
    cols = [U_column(m, K) for m in range(M + 1)]
    return [[cols[m][k] for m in range(M + 1)] for k in range(K + 1)]


def Ub(T, k, m):
    """带引理 1 边界约定的取值：U_{-1}≡1，U_{-2}≡0（k<=-2 都取 0），U_k(-1)=0（k>=1），U_0(-1)=1。"""
    if k == -1:
        return 1
    if k < -1:
        return 0
    if m == -1:
        return 1 if k == 0 else 0
    return T[k][m]


# ---------------------------------------------------------------------------
# 多项式（系数列表，低次在前）
# ---------------------------------------------------------------------------
def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def sub(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(n)])


def scal(p, c):
    return trim([c * a for a in p])


def mul(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return trim(r)


def shiftx(p, k):
    return trim([0] * k + list(p)) if p else []


def ev(p, x):
    r = 0
    for a in reversed(p):
        r = r * x + a
    return r


def deriv(p):
    return trim([i * p[i] for i in range(1, len(p))])


def divmod_poly(p, q):
    p = [Fraction(a) for a in trim(p)]
    q = [Fraction(a) for a in trim(q)]
    out = [Fraction(0)] * max(len(p) - len(q) + 1, 0)
    while p and len(p) >= len(q):
        c = p[-1] / q[-1]
        d = len(p) - len(q)
        out[d] = c
        for i, b in enumerate(q):
            p[i + d] -= c * b
        p = trim(p)
    return trim(out), p


def gcd_poly(p, q):
    a, b = trim(p), trim(q)
    while b:
        a, b = b, divmod_poly(a, b)[1]
    if not a:
        return []
    lead = Fraction(a[-1])
    return [Fraction(c) / lead for c in a]


def poly_shift_arg(p, h):
    """返回 p(x+h) 的系数（h 为整数或 Fraction）。"""
    n = len(p)
    out = [0] * n
    for i, a in enumerate(p):
        if a:
            # a*(x+h)^i
            for j in range(i + 1):
                out[j] += a * comb(i, j) * h ** (i - j)
    return trim(out)


def bpoly(i):
    return trim([1, -1, 0, -i])


def Ppoly(m):
    p = [1]
    for i in range(m + 1):
        p = mul(p, bpoly(i))
    return p


def Wpoly(m):
    w = [1]
    for j in range(1, m + 1):
        w = add(w, shiftx(scal(Ppoly(j - 1), j), 2))
    return w


# ---------------------------------------------------------------------------
# 截断级数
# ---------------------------------------------------------------------------
def ser_mul(a, b, n):
    r = [0] * n
    for i in range(min(len(a), n)):
        x = a[i]
        if x:
            for j in range(min(len(b), n - i)):
                r[i + j] += x * b[j]
    return r


def ser_inv(p, n):
    """1/p 的前 n 项（p[0] 必须是 ±1 或用 Fraction）。"""
    p = list(p) + [0] * max(0, n - len(p))
    c0 = p[0]
    r = [0] * n
    if c0 in (1, -1):
        r[0] = c0
        for k in range(1, n):
            s = 0
            for i in range(1, k + 1):
                if p[i]:
                    s += p[i] * r[k - i]
            r[k] = -s * c0
    else:
        inv0 = Fraction(1) / Fraction(c0)
        r[0] = inv0
        for k in range(1, n):
            s = 0
            for i in range(1, k + 1):
                if p[i]:
                    s += p[i] * r[k - i]
            r[k] = -s * inv0
    return r


# ---------------------------------------------------------------------------
# 模 p 的 Berlekamp–Massey
# ---------------------------------------------------------------------------
def bm_mod(seq, p):
    s = [v % p for v in seq]
    C, B = [1], [1]
    L, sh, b = 0, 1, 1
    for n in range(len(s)):
        d = s[n]
        for i in range(1, L + 1):
            if i < len(C):
                d = (d + C[i] * s[n - i]) % p
        if d == 0:
            sh += 1
            continue
        coef = d * pow(b, p - 2, p) % p
        T = C[:]
        need = len(B) + sh
        if len(C) < need:
            C = C + [0] * (need - len(C))
        for i, bi in enumerate(B):
            C[i + sh] = (C[i + sh] - coef * bi) % p
        if 2 * L <= n:
            L = n + 1 - L
            B, b, sh = T, d, 1
        else:
            sh += 1
    while C and C[-1] == 0:
        C.pop()
    return C, L


def stirling2(nmax):
    S = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    S[0][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
    return S


def binom0(a, b):
    """组合数，约定：除非 0<=b<=a，否则为 0。"""
    if b < 0 or a < 0 or b > a:
        return 0
    return comb(a, b)


class Reporter:
    def __init__(self, tag):
        self.tag = tag
        self.np = 0
        self.nf = 0

    def __call__(self, cid, ok, desc):
        if ok:
            self.np += 1
        else:
            self.nf += 1
        print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)

    def summary(self):
        print('SUMMARY %s pass=%d fail=%d' % (self.tag, self.np, self.nf), flush=True)
        return self.nf == 0
