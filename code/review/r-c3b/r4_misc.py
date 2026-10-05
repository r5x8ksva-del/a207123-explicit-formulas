# -*- coding: utf-8 -*-
"""r-c3b 复核脚本 4：杂项核对。
 (a) c3b 的 N 实验参数：窗口 [A..40]x[B..40] 中真正非零的方程行数（N(k,q)=0 当 q>k 造成全零行），
     报告「未知量 / 非零行」的真实余量；
 (b) GCD 例外情形 m=n^2(n-1)：二次因子 q_n=1+(n-1)x+n(n-1)x^2 不整除 W_m —— 在 F_p[x]/(q_n) 中算 W_m 的余式，
     n=2..60，两个素数。严格性：若 q_n | W_m（Q 上），由 Gauss 引理 W_m=q_n*g, g∈Z[x]，模 p（p∤n(n-1)）余式为 0；
     所以模 p 余式非零 => q_n ∤ W_m。另核对 c1 的 Gauss 引理证明所需成分：W_m(1)=1、q_n(1)=n^2、(1-nx)|_{x=1}=1-n；
 (c) 对 n=2..8 用精确 Fraction 复算一遍（与 c3b 的 C3B-GCD2 范围相同，但代码独立）；
 (d) c_4 = 215/2：精确有理数 G_3(1/2)+1 = 215，以及 U_k(4)/2^k -> 215/2 的数值趋势（标明的数值检查）。
"""
import sys, os, time
from fractions import Fraction as Fr
from math import comb
from collections import defaultdict

T0 = time.time()


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def U_list(m, K):
    o = [1, m + 1]
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    o.append(sum(cnt.values()))
    for k in range(3, K + 1):
        new = defaultdict(int)
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] += v
        cnt = new
        o.append(sum(cnt.values()))
    return o


# ---------------- (a) ----------------
K = M = 40
cols = [U_list(m, K) for m in range(M + 1)]
U = [[cols[m][k] for m in range(M + 1)] for k in range(K + 1)]


def Nval(k, q):
    s = 0
    for i in range(q + 1):
        u = (1 if k == 0 else 0) if i == 0 else U[k][i - 1]
        s += (-1) ** (q - i) * comb(q, i) * u
    return s


N = [[Nval(k, q) for q in range(M + 1)] for k in range(K + 1)]


def nonzero_rows(A, B):
    cnt = 0
    for k in range(A, K + 1):
        for q in range(B, M + 1):
            if any(N[k - a][q - b] != 0 for a in range(A + 1) for b in range(B + 1)):
                cnt += 1
    return cnt


print('(a) c3b N-experiment windows: unknowns vs non-zero equation rows')
for (A, B, D, kind) in [(6, 6, 6, 'konly'), (10, 3, 6, 'konly'), (3, 10, 6, 'konly'), (4, 4, 12, 'konly'),
                        (15, 1, 8, 'konly'), (1, 15, 8, 'konly'),
                        (3, 2, 1, 'tot'), (3, 2, 3, 'tot'), (5, 3, 2, 'tot'), (6, 3, 3, 'tot'), (4, 4, 4, 'tot'),
                        (6, 4, 2, 'tot'), (3, 1, 3, 'tot'), (2, 4, 3, 'tot')]:
    nm = (D + 1) if kind == 'konly' else (D + 1) * (D + 2) // 2
    nunk = (A + 1) * (B + 1) * nm
    rows = (K + 1 - A) * (M + 1 - B)
    nz = nonzero_rows(A, B)
    print('   N %-5s (A,B,D)=(%d,%d,%d): unknowns=%d, rows=%d, NON-ZERO rows=%d (zero rows %d)'
          % (kind, A, B, D, nunk, rows, nz, rows - nz))
for (A, B, Dk, Dq) in [(4, 3, 3, 2), (5, 4, 1, 3), (3, 3, 5, 0)]:
    nunk = (A + 1) * (B + 1) * (Dk + 1) * (Dq + 1)
    rows = (K + 1 - A) * (M + 1 - B)
    nz = nonzero_rows(A, B)
    print('   N sep   (A,B,Dk,Dq)=(%d,%d,%d,%d): unknowns=%d, rows=%d, NON-ZERO rows=%d' % (A, B, Dk, Dq, nunk, rows, nz))


# ---------------- (b) ----------------
def W_mod_q_modp(n, p):
    """W_m mod (q_n, p), m = n^2(n-1). Elements of F_p[x]/(q_n) as pairs (c0, c1) meaning c0 + c1 x.
    q_n = n(n-1) x^2 + (n-1) x + 1  =>  x^2 = -((n-1) x + 1) / (n(n-1))."""
    m = n * n * (n - 1)
    lc = n * (n - 1) % p
    il = pow(lc, -1, p)
    a1 = (-(n - 1) * il) % p   # x^2 = a1 x + a0
    a0 = (-1 * il) % p

    def mul(u, v):
        c0 = u[0] * v[0]
        c1 = u[0] * v[1] + u[1] * v[0]
        c2 = u[1] * v[1]
        return ((c0 + c2 * a0) % p, (c1 + c2 * a1) % p)
    X = (0, 1)
    X2 = mul(X, X)
    X3 = mul(X2, X)
    Pm = (1, 0)          # P_{v-1}
    Wm = (1, 0)          # W_{v-1}
    for v in range(0, m + 1):
        # W_v = W_{v-1} + v x^2 P_{v-1}
        t = mul(X2, Pm)
        Wm = ((Wm[0] + v * t[0]) % p, (Wm[1] + v * t[1]) % p)
        # P_v = P_{v-1} * (1 - x - v x^3)
        bv = ((1 - v * X3[0]) % p, (-1 - v * X3[1]) % p)
        Pm = mul(Pm, bv)
    return Wm


ok = True
primes = [1000000007, 998244353]
bad = []
for n in range(2, 61):
    for p in primes:
        if (n * (n - 1)) % p == 0:
            continue
        r = W_mod_q_modp(n, p)
        if r == (0, 0):
            bad.append((n, p))
            ok = False
print('(b) W_m mod q_n is NON-ZERO mod p (=> q_n does not divide W_m over Q), n=2..60 (m up to %d), primes %s: %s %s'
      % (60 * 60 * 59, primes, 'PASS' if ok else 'FAIL', bad))


# Gauss-lemma ingredients for c1's all-m proof
def b_poly(i):
    return [1, -1, 0, -i]


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


P = {-1: [1]}
W = {-1: [1]}
ok = True
for m in range(0, 301):
    P[m] = pmul(P[m - 1], b_poly(m))
    W[m] = padd(W[m - 1], [0, 0] + [m * c for c in P[m - 1]])
    if sum(W[m]) != 1:       # W_m(1)
        ok = False
    if any(not isinstance(c, int) for c in W[m]):
        ok = False
ok2 = all(1 + (n - 1) + n * (n - 1) == n * n for n in range(2, 1000)) and all(
    pmul([1, -n], [1, n - 1, n * (n - 1)]) == b_poly(n * n * (n - 1)) for n in range(2, 200))
print('(b\') c1 Gauss-lemma ingredients: W_m in Z[x] with W_m(1)=1 (0<=m<=300): %s; b_{n^2(n-1)}=(1-nx)q_n and q_n(1)=n^2 (n<200/1000): %s'
      % ('PASS' if ok else 'FAIL', 'PASS' if ok2 else 'FAIL'))


# ---------------- (c) exact Fraction re-check n=2..8 ----------------
def pdivmod_rem(p, q):
    p = [Fr(c) for c in p]
    while len(p) >= len(q):
        if p[-1] == 0:
            p.pop()
            continue
        c = p[-1] / q[-1]
        d = len(p) - len(q)
        for i, b in enumerate(q):
            p[i + d] -= c * b
        p.pop()
    while p and p[-1] == 0:
        p.pop()
    return p


ok = True
for n in range(2, 9):
    m = n * n * (n - 1)
    q = [Fr(1), Fr(n - 1), Fr(n * (n - 1))]
    Pm, Wm = [Fr(1)], [Fr(1)]
    for v in range(0, m + 1):
        Wm = pdivmod_rem(padd(Wm, [0, 0] + [v * c for c in Pm]), q)
        Pm = pdivmod_rem(pmul(Pm, b_poly(v)), q)
    if not Wm:
        ok = False
print('(c) exact Fraction: q_n does not divide W_m, n=2..8 (m=4..448): %s' % ('PASS' if ok else 'FAIL'))

# ---------------- (d) c_4 ----------------
x = Fr(1, 2)


def ev(poly, x):
    r = Fr(0)
    for c in reversed(poly):
        r = r * x + c
    return r


G3 = ev(W[3], x) / ev(P[3], x)
c4 = (G3 + 4 * x * x) / (x * (1 + 12 * x * x))
c4b = ev(W[4], x) / ((1 + 3 * 4 * x * x) * 24 * x ** 13)
print('(d) exact: G_3(1/2)=%s, G_3(1/2)+1=%s, c_4=%s, W_4(1/2)/((1+12x^2)4!x^13)=%s  -> %s'
      % (G3, G3 + 1, c4, c4b, 'PASS' if (G3 + 1 == 215 and c4 == Fr(215, 2) == c4b) else 'FAIL'))
col = U_list(4, 400)
for k in (100, 200, 300, 400):
    print('    [numeric] k=%d: U_k(4)/2^k - 215/2 = %.3e' % (k, float(Fr(col[k], 2 ** k) - Fr(215, 2))))
print('elapsed %.1fs' % (time.time() - T0))
