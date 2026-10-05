# -*- coding: utf-8 -*-
"""r-c2b 复核脚本 5：定理 6（u 型单和不存在）的基本复核。

(A) 留数元的独立推导：G_m = W_m(x)/P_m(x)，P_m = (1-x)^{m+1} prod_{v=1}^m (1-v u)（因 x^3 = u(1-x)），
    所以在 u=1/i 处 G_m 坐标的留数 ∝ W_m(x)(1-x)^{-(m+1)} 在 K_i=Q[x]/(x^3+x/i-1/i) 中的像（E 部分用 W_m-1）。
    这里的 W_m 直接由多项式 1 + x^2 sum_j j P_{j-1}(x) 在 K_i 里约化得到，K_i 的逆用扩展欧几里得；
    范数用结式 Res(f_i, g)（Sylvester 5x5 行列式）计算——与作者的「(1-x)^{-n}=i^{-n}x^{-3n}」与乘法矩阵行列式都不同。
    与作者 [cert] 的 N 值比较：作者的 nu_i = 本脚本的元素 / prod_{v=1..m, v!=i}(1-v/i)。
(B) 经验检验：U_k(m)（m=1..4）、E(k,m)（m=2..4）在宽盒 c∈[-40,40], d∈[-10,40] 内用 k<=60 的精确消元，
    统计「相容」的 (c,d)（理论上应为 0；完整部分 A_m 作对照应恰有若干个相容且检验数很多）。
"""
import sys, os, re, time
from fractions import Fraction
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass

T0 = time.time()


# ---------------- 多项式（Fraction 系数，升幂） ----------------
def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def pmul(a, b):
    if not a or not b:
        return []
    r = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return trim(r)


def pdivmod(a, b):
    a = [Fraction(x) for x in trim(a)]
    b = [Fraction(x) for x in trim(b)]
    q = [Fraction(0)] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and a:
        c = a[-1] / b[-1]
        d = len(a) - len(b)
        q[d] += c
        for i, y in enumerate(b):
            a[i + d] -= c * y
        a = trim(a)
    return trim(q), a


def pinv_mod(a, f):
    """a^{-1} mod f（扩展欧几里得）。"""
    r0, r1 = trim(f), trim(a)
    s0, s1 = [], [Fraction(1)]
    while r1 and len(r1) > 1:
        q, r = pdivmod(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, padd(s0, [-x for x in pmul(q, s1)])
    if not r1:
        raise ZeroDivisionError('not invertible')
    c = r1[0]
    return pdivmod([x / c for x in s1], f)[1]


def det(M):
    M = [[Fraction(x) for x in row] for row in M]
    n = len(M)
    d = Fraction(1)
    for i in range(n):
        piv = next((r for r in range(i, n) if M[r][i] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != i:
            M[i], M[piv] = M[piv], M[i]
            d = -d
        d *= M[i][i]
        for r in range(i + 1, n):
            f = M[r][i] / M[i][i]
            if f:
                for c in range(i, n):
                    M[r][c] -= f * M[i][c]
    return d


def resultant(f, g):
    """Res(f,g)，f,g 升幂系数；Sylvester 矩阵。"""
    f = trim(f); g = trim(g)
    m, n = len(f) - 1, len(g) - 1
    if n < 0:
        return Fraction(0)
    if n == 0:
        return Fraction(g[0]) ** m
    F = f[::-1]; G = g[::-1]       # 降幂
    N = m + n
    S = []
    for i in range(n):
        S.append([0] * i + F + [0] * (N - m - 1 - i))
    for i in range(m):
        S.append([0] * i + G + [0] * (N - n - 1 - i))
    return det(S)


def b_poly(v):
    return trim([Fraction(1), Fraction(-1), Fraction(0), Fraction(-v)])


def W_poly(m):
    """W_m(x) = 1 + x^2 sum_{j=1}^m j P_{j-1}(x)（y=1）。"""
    W = [Fraction(1)]
    P = [Fraction(1)]
    for j in range(1, m + 1):
        P = pmul(P, b_poly(j - 1))           # P_{j-1}
        W = padd(W, pmul([Fraction(0), Fraction(0), Fraction(j)], P))
    return W


def is_field(i):
    q = 2
    while q * q * (q - 1) <= i:
        if q * q * (q - 1) == i:
            return False
        q += 1
    return True


def element(m, i, which):
    f = [Fraction(-1, i), Fraction(1, i), Fraction(0), Fraction(1)]   # x^3 + x/i - 1/i
    W = W_poly(m)
    if which == 'E':
        W = padd(W, [Fraction(-1)])
    one_minus_x = [Fraction(1), Fraction(-1)]
    pw = [Fraction(1)]
    for _ in range(m + 1):
        pw = pmul(pw, one_minus_x)
    num = pdivmod(W, f)[1]
    inv = pinv_mod(pdivmod(pw, f)[1], f)
    return pdivmod(pmul(num, inv), f)[1], f


def norm(g, f):
    return resultant(f, g) if g else Fraction(0)


def prime_factors(n):
    ps = []
    d = 2
    while d * d <= n and d < 10 ** 6:
        if n % d == 0:
            ps.append(d)
            while n % d == 0:
                n //= d
        d += 1
    return ps, n


def iroot3(n):
    lo, hi = 0, 1
    while hi ** 3 <= n:
        hi *= 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** 3 <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo


def ifree_is_cube(Nv, i):
    num, den = abs(Nv.numerator), Nv.denominator
    for p in prime_factors(i)[0] + ([prime_factors(i)[1]] if prime_factors(i)[1] > 1 else []):
        while num % p == 0:
            num //= p
        while den % p == 0:
            den //= p
    return iroot3(num) ** 3 == num and iroot3(den) ** 3 == den


# 读作者 [cert] 行
cert = {}
logp = os.path.join(ROOT, 'logs', 'c2b_check_run3.log')
for line in open(logp, encoding='utf-8'):
    mm = re.match(r'\s*\[cert\] (E|U) m=(\d+): u=1/(\d+) N=(\S+) (.*)$', line)
    if mm:
        cert[(mm.group(1), int(mm.group(2)))] = (int(mm.group(3)), mm.group(4), mm.group(5))

okA = True
match_vals = 0
mism = []
mine = {}
for which in ('U', 'E'):
    for m in range(1, 31):
        if which == 'E' and m == 1:
            continue
        found = None
        for i in range(m, 0, -1):
            if not is_field(i):
                continue
            g, f = element(m, i, which)
            Nv = norm(g, f)
            if Nv == 0:
                continue
            if not ifree_is_cube(Nv, i):
                found = (i, Nv)
                break
        mine[(which, m)] = found
        if found is None:
            okA = False
            continue
        i, Nv = found
        # 换算成作者的归一化
        cfac = Fraction(1)
        for v in range(1, m + 1):
            if v != i:
                cfac *= (1 - Fraction(v, i))
        Nauthor = Nv / cfac ** 3
        a = cert.get((which, m))
        if a is None or a[0] != i:
            mism.append((which, m, i, a))
            continue
        s_auth = a[1]
        s_mine = str(Nauthor)
        if s_auth.endswith('...'):
            same = s_mine.startswith(s_auth[:-3])
        else:
            same = (s_mine == s_auth)
        if same:
            match_vals += 1
        else:
            mism.append((which, m, i, s_auth, s_mine[:40]))
print('(A) 独立推导的留数元（来自 W_m/P_m）+ 结式范数：所有 m 都找到 i-free 部分非立方的极点：', okA)
print('    与作者 [cert] 的极点与 N 值一致：%d / %d；不一致：%s' % (match_vals, len(mine), mism))
# m=2 的 E 手算：N=17
g, f = element(2, 2, 'E')
Nv = norm(g, f)
c = Fraction(1) * (1 - Fraction(1, 2))
print('    m=2,E,i=2：作者归一化的 N =', Nv / c ** 3, '（作者手算 17）')

# 对照：完整部分（只有 j=0 项）的元素是 (1-x)^{-(m+1)}，判据不应报阻碍
okS = True
for m in range(1, 31):
    for i in range(1, m + 1):
        if not is_field(i):
            continue
        f = [Fraction(-1, i), Fraction(1, i), Fraction(0), Fraction(1)]
        pw = [Fraction(1)]
        for _ in range(m + 1):
            pw = pmul(pw, [Fraction(1), Fraction(-1)])
        g = pinv_mod(pdivmod(pw, f)[1], f)
        if not ifree_is_cube(norm(g, f), i):
            okS = False
print('    对照 A_m：所有域极点都不报阻碍 (m<=30)：', okS)
print('[time A] %.1fs' % (time.time() - T0), flush=True)


# ---------------- (B) 宽盒经验检验 ----------------
def good(a, b, c):
    return b == c or (a >= b and a >= c)


def C(n, r):
    if n < 0 or r < 0 or r > n:
        return 0
    return comb(n, r)


def split_dp(K, m):
    comp = [0] * (K + 1); ascd = [0] * (K + 1)
    comp[0] = 1; comp[1] = m + 1
    st = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    for (a, b), v in st.items():
        (ascd if a < b else comp)[2] += v
    for k in range(3, K + 1):
        nst = {}
        for (a, b), v in st.items():
            for cc in range(m + 1):
                if good(a, b, cc):
                    nst[(b, cc)] = nst.get((b, cc), 0) + v
        st = nst
        for (b, cc), v in st.items():
            (ascd if b < cc else comp)[k] += v
    return comp, ascd


def solve_u(V, c, d):
    kmax = len(V) - 1
    cols = []
    for s in range(0, kmax + 60):
        r = d + s
        if r < 0:
            continue
        if max(0, r + 2 * s - c) <= kmax:
            cols.append(s)
        else:
            break
    piv = {}
    checks = 0
    for k in range(kmax + 1):
        row = {}
        for s in cols:
            v = C(k + c - 2 * s, d + s)
            if v:
                row[s] = Fraction(v)
        rhs = Fraction(V[k])
        for pc in [p for p in row if p in piv]:
            fct = row.get(pc, 0)
            if not fct:
                continue
            prow, prhs = piv[pc]
            for cc, vv in prow.items():
                nv = row.get(cc, 0) - fct * vv
                if nv:
                    row[cc] = nv
                else:
                    row.pop(cc, None)
            rhs -= fct * prhs
        if not row:
            if rhs != 0:
                return False, checks
            checks += 1
            continue
        pc = min(row)
        inv = 1 / row[pc]
        prow = {cc: vv * inv for cc, vv in row.items()}
        prhs = rhs * inv
        for q in list(piv):
            qrow, qrhs = piv[q]
            fct = qrow.get(pc, 0)
            if fct:
                for cc, vv in prow.items():
                    nv = qrow.get(cc, 0) - fct * vv
                    if nv:
                        qrow[cc] = nv
                    else:
                        qrow.pop(cc, None)
                piv[q] = (qrow, qrhs - fct * prhs)
        piv[pc] = (prow, prhs)
    return True, checks


KB = 60
for m in range(1, 5):
    cp, ad = split_dp(KB, m)
    U = [cp[k] + ad[k] for k in range(KB + 1)]
    for name, V in (('U', U), ('E', ad), ('A', cp)):
        if name == 'E' and m == 1:
            continue
        cons = []
        for c in range(-40, 41):
            for d in range(-10, 41):
                ok, ch = solve_u(V, c, d)
                if ok:
                    cons.append((c, d, ch))
        informative = [x for x in cons if x[2] >= 5]
        print('(B) %s m=%d: (c,d) in [-40,40]x[-10,40], k<=60：相容 %d 个，其中检验数>=5 的 %d 个 %s' %
              (name, m, len(cons), len(informative), informative[:6]), flush=True)
print('[time] %.1fs' % (time.time() - T0))
