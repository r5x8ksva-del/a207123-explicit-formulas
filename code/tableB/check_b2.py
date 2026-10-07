# -*- coding: utf-8 -*-
"""表 B 的 B2（两族 u 型和不存在）的核对脚本（2026-10-08）。证明见 notes/08-主Agent-表B-B2-两族u型和.md。

记号：b_i = 1 - x - i x^3，eta 为 b_i 的根，K_i = Q(eta)（i=1,2,3 时 b_i 在 Q 上不可约）。
  Wt_i(x) = 1 + sum_{j=1}^{i} j * i^(j) * x^(3j+2)（i^(j) 为下降阶乘）；U 部分用 Wt_i，E 部分用 Wt_i - 1。
  D_i(n,b) := pi(eta^b) ∧ pi(Wt eta^n)，pi = 基 (1,eta,eta^2) 下后两个坐标，∧ = 2x2 行列式。
  条件 (F_i)：D_i(n,b) = 0 ⇔ 1, eta^b, Wt eta^n 在 Q 上线性相关。
逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b2 pass=<n> fail=<n>」。
  b2-gf       G_m = W_m/P_m 的展开与 U 的 DP 一致（m<=5, k<=30）；E_m = (W_m-1)/P_m 的展开等于按定义枚举的「以上升结尾」
              的合法序列数（m<=3, k<=8）
  b2-utype    u 型族的母函数：sum_k C(k+c-2s, m+s+d) x^k = x^(-2(m+d)-c-3) u^(s+m+d+1) + Laurent 多项式（若干参数，到 x^40）
  b2-res      纤维 i 上的留数元：u'(eta) Res_eta G_m = (-1)^(m-i+1) Wt_i(eta) eta^(-3m-3)/(i!(m-i)! i^2)，E 同理（Wt_i - 1），
              在 K_i 中精确成立（i=1,2,3，i<=m<=i+7）；并核对 W_m(eta) = Wt_i(eta)
  b2-m1       反向检查：m=1 的 F3 型两族表示（T2.5(1)）对 k<=40 成立，对应 (n,b)=(1,4)、(-3,-4) 满足 (F_1)，但不满足 (F_2)
  b2-E2       正向对照（复核者 s9-b2 指出）：E_2 有两族表示 x^-4u^2/((1-u)(1-2u)) + 2x^-1u/(1-2u)（与 (W_2-1)/P_2、按定义枚举一致）；
              对应的 6 个公共解满足 E 的纤维 1、2、不满足纤维 3；G_1 = x^-6u^2/(1-u) + x^-1u/(1-u) 对应的 (0,5)、(-5,-5) 满足 U 的纤维 1
  b2-small    |n|,|b|<=40 内各纤维条件的全部解（精确）；U 的 (F_1)∧(F_2)、E 的 (F_1)∧(F_2)∧(F_3) 无公共解
  b2-primes   证书素数：素性、eta 模 l 的阶（逐次乘方求得）整除 T=5040
  b2-sieve-U  筛法：b ≢ 0 (mod 5040) 的每个剩余类 (n,b) 都有某个证书素数 l 使 D_i(n,b) ≢ 0 (mod l)（纤维 1、2）
  b2-padic-U  l 进导数：对每个 n mod 5040，有某个证书素数 l（周期 P | 5040）使 E_l(n) := pi(mu) ∧ pi(Wt eta^n) ≢ 0 (mod l)，
              eta^P = 1 + l mu；mu 模 l 用模 l^2 的乘方算出，纤维 1 另用大整数精确算 xi^P 复核
  b2-sieve-E、b2-padic-E  同上，E 部分，纤维 1、2、3
  b2-reverse  反向检查：(a) 只用纤维 1 时，小范围内的真解所在的类都没有被筛掉；(b) E 的纤维 1 在 n ≡ -5 时 l 进检验必然失效
              （平凡族），确实要靠纤维 2、3；(c) 把纤维 2 的元素换成 1（人为制造公共解）后，筛法保留了公共解 (0,-3) 所在的类
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_table  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []
T = 5040
# 证书素数：纤维 i -> [(l, 周期 P)]，P = eta 在 (Z_l[eta]/l)^x 中的阶，均整除 5040
CERT = {
    1: [(3, 8), (11, 60), (13, 168), (29, 840), (2521, 2520)],
    2: [(7, 48), (17, 72), (19, 18), (41, 280), (71, 5040), (127, 126)],
    3: [(13, 84), (71, 70)],
}


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


# ---------------- 有理多项式与数域 Q[x]/(b_i) ----------------
def pmul(a, b):
    r = [Fr(0)] * (len(a) + len(b) - 1)
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


def pderiv(a):
    return [i * a[i] for i in range(1, len(a))] or [Fr(0)]


def b_poly(v):
    return [Fr(1), Fr(-1), Fr(0), Fr(-v)]


def P_poly(m):
    p = [Fr(1)]
    for v in range(m + 1):
        p = pmul(p, b_poly(v))
    return p


def W_poly(m):
    w = [Fr(1)]
    for j in range(1, m + 1):
        w = padd(w, pscale(pmul([Fr(0), Fr(0), Fr(1)], P_poly(j - 1)), Fr(j)))
    return w


class Field:
    """Q[x]/(i x^3 + x - 1)，元素为长度 3 的 Fraction 列表。"""

    def __init__(self, i):
        self.i = i

    def red(self, poly):
        c = [Fr(x) for x in poly] + [Fr(0)] * 3
        for d in range(len(c) - 1, 2, -1):
            v = c[d]
            if v:
                c[d] = Fr(0)
                # x^d = x^(d-3) * (1 - x)/i
                c[d - 3] += v / self.i
                c[d - 2] -= v / self.i
        return c[:3]

    def mul(self, a, b):
        return self.red(pmul(a, b))

    def inv(self, a):
        cols = [self.mul(a, e) for e in ([1, 0, 0], [0, 1, 0], [0, 0, 1])]
        M = [[cols[j][r] for j in range(3)] + [Fr(1 if r == 0 else 0)] for r in range(3)]
        for c in range(3):
            p = next(r for r in range(c, 3) if M[r][c] != 0)
            M[c], M[p] = M[p], M[c]
            pv = M[c][c]
            M[c] = [v / pv for v in M[c]]
            for r in range(3):
                if r != c and M[r][c] != 0:
                    f = M[r][c]
                    M[r] = [M[r][t] - f * M[c][t] for t in range(4)]
        return [M[r][3] for r in range(3)]

    def pw(self, e):
        x = [Fr(0), Fr(1), Fr(0)]
        if e < 0:
            x = self.inv(x)
            e = -e
        r = [Fr(1), Fr(0), Fr(0)]
        for _ in range(e):
            r = self.mul(r, x)
        return r

    def ev(self, poly):
        return self.red(poly)


def falling(i, j):
    r = 1
    for t in range(j):
        r *= i - t
    return r


def Wt_poly(i, kind):
    w = [Fr(1 if kind == 'U' else 0)]
    for j in range(1, i + 1):
        mono = [Fr(0)] * (3 * j + 2) + [Fr(j * falling(i, j))]
        w = padd(w, mono)
    return w


def D_exact(F, elem, n, b, cache):
    if b not in cache:
        cache[b] = F.pw(b)
    if ('W', n) not in cache:
        cache[('W', n)] = F.mul(elem, F.pw(n))
    v, w = cache[b], cache[('W', n)]
    return v[1] * w[2] - v[2] * w[1]


# ---------------- 检查 1：母函数 ----------------
def series_div(num, den, K):
    """num/den 的幂级数系数（den[0] != 0），到 x^K。"""
    out = []
    num = list(num) + [Fr(0)] * (K + 1)
    for k in range(K + 1):
        v = num[k] - sum(den[j] * out[k - j] for j in range(1, min(k, len(den) - 1) + 1))
        out.append(v / den[0])
    return out


def legal(seq):
    for i in range(len(seq) - 2):
        a, b, c = seq[i], seq[i + 1], seq[i + 2]
        if not (b == c or (a >= b and a >= c)):
            return False
    return True


def check_gf():
    K = 30
    Ut = U_fast_table(K, 5)
    ok = True
    for m in range(0, 6):
        s = series_div(W_poly(m), P_poly(m), K)
        if any(s[k] != Ut[k][m] for k in range(K + 1)):
            ok = False
    # E_m：以上升结尾（h_{k-1} < h_k）的合法序列数
    from itertools import product
    okE = True
    for m in range(1, 4):
        s = series_div(padd(W_poly(m), [Fr(-1)]), P_poly(m), 8)
        for k in range(0, 9):
            cnt = 0
            for seq in product(range(m + 1), repeat=k):
                if k >= 2 and seq[-2] < seq[-1] and legal(seq):
                    cnt += 1
            if s[k] != cnt:
                okE = False
    report('b2-gf', ok and okE, 'G_m=W_m/P_m 与 DP 一致（m<=5,k<=30）：%s；E_m=(W_m-1)/P_m 与按定义枚举「以上升结尾」一致（m<=3,k<=8）：%s' % (ok, okE))


# ---------------- 检查 2：u 型族的母函数 ----------------
def check_utype():
    K = 40
    ok = True
    for (m, c, d, s) in [(1, 2, 0, 0), (1, 0, -1, 2), (2, 3, 1, 1), (3, -2, 0, 4), (2, 5, -2, 3)]:
        r = m + s + d
        g = -2 * (m + d) - c - 3
        e = s + m + d + 1
        # 左边：k 从 0 到 K（组合约定；k+c-2s<0 或 <r 时为 0）
        lhs = {k: (comb(k + c - 2 * s, r) if (k + c - 2 * s >= 0 and r >= 0) else 0) for k in range(K + 1)}
        # 右边：x^g u^e = x^(g+3e) (1-x)^(-e)，e>=1 时为 x^(g+3e) sum_j C(j+e-1, e-1) x^j
        base = g + 3 * e
        rhs = {k: (comb(k - base + e - 1, e - 1) if k - base >= 0 else 0) for k in range(K + 1)}
        # 允许有限个 k 不同（Laurent 多项式）：只比较 k >= max(0, base) + 3
        lo = max(0, base, -c + 2 * s + r) + 3
        if any(lhs[k] != rhs[k] for k in range(lo, K + 1)):
            ok = False
    report('b2-utype', ok, 'sum_k C(k+c-2s,m+s+d)x^k 与 x^(-2(m+d)-c-3)u^(s+m+d+1) 在 x^40 内只差 Laurent 多项式（5 组参数）')


# ---------------- 检查 3：留数元 ----------------
def check_residues():
    ok = True
    okW = True
    cnt = 0
    for i in (1, 2, 3):
        F = Field(i)
        eta = [Fr(0), Fr(1), Fr(0)]
        one = [Fr(1), Fr(0), Fr(0)]
        # u'(eta) = eta^2 (3 - 2 eta)/(1 - eta)^2
        om = [Fr(1), Fr(-1), Fr(0)]
        up = F.mul(F.mul(F.mul(eta, eta), [Fr(3), Fr(-2), Fr(0)]), F.inv(F.mul(om, om)))
        for kind in ('U', 'E'):
            Wt = F.ev(Wt_poly(i, kind))
            for m in range(i, i + 8):
                Pm = P_poly(m)
                Wm = W_poly(m)
                if kind == 'E':
                    Wm = padd(Wm, [Fr(-1)])
                # P_m(eta) = 0，eta 为单根
                if any(F.ev(Pm)):
                    ok = False
                res = F.mul(F.ev(Wm), F.inv(F.ev(pderiv(Pm))))
                lhs = F.mul(up, res)
                const = Fr((-1) ** (m - i + 1), factorial(i) * factorial(m - i) * i * i)
                rhs = [const * v for v in F.mul(Wt, F.pw(-3 * m - 3))]
                if lhs != rhs:
                    ok = False
                if kind == 'U' and F.ev(W_poly(m)) != F.ev(Wt_poly(i, 'U')):
                    okW = False
                cnt += 1
    report('b2-res', ok and okW, '留数元公式在 K_i 中精确成立（i=1,2,3；U、E；i<=m<=i+7，共 %d 例）；W_m(eta)=Wt_i(eta)：%s' % (cnt, okW))


# ---------------- 检查 4：m=1 的反向检查 ----------------
def check_m1():
    K = 40
    Ut = U_fast_table(K, 1)
    ok = True
    for k in range(K + 1):
        v = sum(comb(k + 2 - 2 * s, 1 + s) for s in range(0, k + 2) if k + 2 - 2 * s >= 0) \
            - sum(comb(k - 2 * s, s) for s in range(0, k + 1) if k - 2 * s >= 0)
        if v != Ut[k][1]:
            ok = False
    # 两族：C(k+2-2s, 1+s)（c=2,d=0）与 C(k-2s, s)（c=0,d=-1），m=1：g = -2(m+d)-c-3
    g1, g2 = -2 * (1 + 0) - 2 - 3, -2 * (1 - 1) - 0 - 3
    pairs = [(-3 * 1 - 3 - g1, g2 - g1), (-3 * 1 - 3 - g2, g1 - g2)]
    F1, F2 = Field(1), Field(2)
    W1, W2 = F1.ev(Wt_poly(1, 'U')), F2.ev(Wt_poly(2, 'U'))
    d1 = [D_exact(F1, W1, n, b, {}) for (n, b) in pairs]
    d2 = [D_exact(F2, W2, n, b, {}) for (n, b) in pairs]
    good = ok and (g1, g2) == (-7, -3) and pairs == [(1, 4), (-3, -4)] and all(v == 0 for v in d1) and all(v != 0 for v in d2)
    report('b2-m1', good, 'F3 型 m=1 两族表示成立（k<=40）：%s；(g1,g2)=%s，(n,b)=%s；D_1=%s，D_2=%s' % (ok, (g1, g2), pairs, d1, [str(v) for v in d2]))


# ---------------- 检查 4b：E 的 m=2 有两族表示（复核者 s9-b2 指出）；G_1 的另一种两族表示 ----------------
def check_E2():
    from itertools import product
    K = 60
    # 两族式：E(k,2) = sum_s (2^(s+1)-1) C(k-1-2s, s+1) + sum_s 2^(s+1) C(k-2-2s, s)
    def formula(k):
        a = sum((2 ** (s + 1) - 1) * comb(k - 1 - 2 * s, s + 1) for s in range(0, k + 1) if k - 1 - 2 * s >= 0)
        b = sum(2 ** (s + 1) * comb(k - 2 - 2 * s, s) for s in range(0, k + 1) if k - 2 - 2 * s >= 0)
        return a + b
    ser = series_div(padd(W_poly(2), [Fr(-1)]), P_poly(2), K)
    ok_ser = all(formula(k) == ser[k] for k in range(K + 1))
    ok_enum = True
    for k in range(0, 10):
        cnt = sum(1 for seq in product(range(3), repeat=k) if k >= 2 and seq[-2] < seq[-1] and legal(seq))
        if cnt != formula(k):
            ok_enum = False
    # 6 个公共解满足 E 的纤维 1、2，不满足纤维 3
    pts = [(-5, 3), (-8, -3), (-5, 1), (-6, -1), (-6, 2), (-8, -2)]
    F = {i: Field(i) for i in (1, 2, 3)}
    W = {i: F[i].ev(Wt_poly(i, 'E')) for i in (1, 2, 3)}
    d12 = all(D_exact(F[i], W[i], n, b, {}) == 0 for (n, b) in pts for i in (1, 2))
    d3 = [D_exact(F[3], W[3], n, b, {}) for (n, b) in pts]
    # 指数对 {g1,g2}={-4,-1}（m=2）对应 (n,b)=(-3m-3-g1, g2-g1)
    pair_ok = (-3 * 2 - 3 + 4, -1 + 4) == (-5, 3) and (-3 * 2 - 3 + 1, -4 + 1) == (-8, -3)
    # G_1 = x^-6 u^2/(1-u) + x^-1 u/(1-u)：对应 (n,b)=(0,5)、(-5,-5) 满足 U 的纤维 1
    F1 = Field(1)
    W1 = F1.ev(Wt_poly(1, 'U'))
    g1_ok = D_exact(F1, W1, 0, 5, {}) == 0 and D_exact(F1, W1, -5, -5, {}) == 0
    # 级数核对 G_1：按 [x^k] x^g u^e = C(k-g-3e+e-1, e-1)（k-g-3e>=0）逐项展开 x^-6 sum_{e>=2} u^e + x^-1 sum_{e>=1} u^e，
    # 与 U_k(1) 的 DP 比较
    Ut = U_fast_table(40, 1)

    def xgue(k, g, e):
        t = k - g - 3 * e
        return comb(t + e - 1, e - 1) if t >= 0 else 0
    g1_ser = all(sum(xgue(k, -6, e) for e in range(2, k + 8)) + sum(xgue(k, -1, e) for e in range(1, k + 3)) == Ut[k][1]
                 for k in range(41))
    ok = ok_ser and ok_enum and d12 and all(v != 0 for v in d3) and pair_ok and g1_ok and g1_ser
    report('b2-E2', ok, 'E_2 的两族式与 (W_2-1)/P_2 一致（k<=60）：%s，与按定义枚举一致（k<=9）：%s；6 个公共解满足 E 的纤维 1、2：%s，'
           '纤维 3 的 D_3=%s（都不为 0）；G_1=x^-6u^2/(1-u)+x^-1u/(1-u)（级数一致：%s）对应的 (0,5)、(-5,-5) 满足 U 的纤维 1：%s'
           % (ok_ser, ok_enum, d12, [str(v) for v in d3], g1_ser, g1_ok))


# ---------------- 检查 5：小范围精确解 ----------------
def small_solutions(i, kind, R=40):
    F = Field(i)
    W = F.ev(Wt_poly(i, kind))
    cache = {}
    sols = set()
    for n in range(-R, R + 1):
        for b in range(-R, R + 1):
            if b and D_exact(F, W, n, b, cache) == 0:
                sols.add((n, b))
    return sols


def check_small():
    S = {}
    for kind, fibers in (('U', (1, 2)), ('E', (1, 2, 3))):
        for i in fibers:
            S[(kind, i)] = small_solutions(i, kind)
    cu = S[('U', 1)] & S[('U', 2)]
    ce = S[('E', 1)] & S[('E', 2)] & S[('E', 3)]
    desc = '；'.join('%s 纤维%d：%d 个' % (k, i, len(v)) for (k, i), v in sorted(S.items()))
    report('b2-small', not cu and not ce,
           '|n|,|b|<=40 的精确解（b≠0）：%s；U 公共解 %s，E 公共解 %s；U 纤维 2 的解 %s，E 纤维 3 的解 %s'
           % (desc, sorted(cu), sorted(ce), sorted(S[('U', 2)]), sorted(S[('E', 3)])))
    return S


# ---------------- 模 l 的运算 ----------------
def mod_consts(i, mod):
    inv = pow(i, -1, mod)
    return inv  # x^3 = inv*(1 - x)


def mulm(a, b, i, mod):
    inv = pow(i, -1, mod)
    r = [0] * 5
    for p in range(3):
        if a[p]:
            for q in range(3):
                r[p + q] += a[p] * b[q]
    for d in (4, 3):
        v = r[d] % mod
        if v:
            r[d - 3] += v * inv
            r[d - 2] -= v * inv
    return [r[0] % mod, r[1] % mod, r[2] % mod]


def powm(e, i, mod):
    res, base = [1, 0, 0], [0, 1, 0]
    while e:
        if e & 1:
            res = mulm(res, base, i, mod)
        base = mulm(base, base, i, mod)
        e >>= 1
    return res


def elem_mod(i, kind, mod):
    acc = [1 % mod, 0, 0] if kind == 'U' else [0, 0, 0]
    for j in range(1, i + 1):
        v = powm(3 * j + 2, i, mod)
        cf = j * falling(i, j)
        acc = [(acc[t] + cf * v[t]) % mod for t in range(3)]
    return acc


def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def disc(i):
    # i x^3 + 0 x^2 + x - 1
    a, b, c, d = i, 0, 1, -1
    return b * b * c * c - 4 * a * c ** 3 - 4 * b ** 3 * d - 27 * a * a * d * d + 18 * a * b * c * d


def check_primes():
    ok = True
    info = []
    for i, lst in CERT.items():
        for (l, P) in lst:
            good = is_prime(l) and l % 2 == 1 and i % l != 0 and disc(i) % l != 0 and T % P == 0
            # 逐次乘方求阶
            cur, order = [1, 0, 0], None
            for e in range(1, T + 1):
                cur = mulm(cur, [0, 1, 0], i, l)
                if cur == [1, 0, 0]:
                    order = e
                    break
            good = good and order == P
            ok = ok and good
            info.append('%d:%d->%s' % (i, l, order))
    report('b2-primes', ok, '证书素数均为奇素数、不整除 i 与判别式，阶逐次乘方求得且整除 5040：%s' % ', '.join(info))


def tables(i, kind, l, P, elem=None):
    W = elem_mod(i, kind, l) if elem is None else elem
    beta = np.zeros((P, 2), dtype=np.int64)
    gam = np.zeros((P, 2), dtype=np.int64)
    cur, curW = [1, 0, 0], W[:]
    for e in range(P):
        beta[e] = cur[1:]
        gam[e] = curW[1:]
        cur = mulm(cur, [0, 1, 0], i, l)
        curW = mulm(curW, [0, 1, 0], i, l)
    assert cur == [1, 0, 0]
    return beta, gam


def mu_mod(i, l, P):
    y = powm(P, i, l * l)
    assert y[0] % l == 1 and y[1] % l == 0 and y[2] % l == 0
    return ((y[1] // l) % l, (y[2] // l) % l)


def sieve(kind, fibers, elems=None):
    """返回 b0≠0 的幸存类列表与每个类的 n0（numpy 筛）。"""
    tabs = {}
    for i in fibers:
        for (l, P) in CERT[i]:
            e = None if elems is None or i not in elems else elems[i](l)
            tabs[(i, l)] = (P,) + tables(i, kind, l, P, e)
    n_idx = np.arange(T)
    surv = []
    for b0 in range(1, T):
        alive = np.ones(T, dtype=bool)
        for i in fibers:
            for (l, P) in CERT[i]:
                _, beta, gam = tabs[(i, l)]
                bb = beta[b0 % P]
                g = gam[n_idx % P]
                alive &= ((bb[0] * g[:, 1] - bb[1] * g[:, 0]) % l == 0)
            if not alive.any():
                break
        surv.extend((int(n0), b0) for n0 in np.nonzero(alive)[0])
    return surv, tabs


def padic(kind, fibers, tabs, exclude_fibers=()):
    """对每个 n0 mod T 找证书素数；返回 (未解决的 n0 列表, 每个纤维用到的次数)。"""
    mus = {(i, l): mu_mod(i, l, P) for i in fibers for (l, P) in CERT[i]}
    unresolved, used = [], {}
    for n0 in range(T):
        hit = None
        for i in fibers:
            if i in exclude_fibers:
                continue
            for (l, P) in CERT[i]:
                m1, m2 = mus[(i, l)]
                gg = tabs[(i, l)][2][n0 % P]
                if (m1 * int(gg[1]) - m2 * int(gg[0])) % l:
                    hit = (i, l)
                    break
            if hit:
                break
        if hit is None:
            unresolved.append(n0)
        else:
            used[hit] = used.get(hit, 0) + 1
    return unresolved, used


def check_mu_exact():
    """纤维 1：用大整数精确算 xi^P（Z[xi] 中，xi^3 = 1 - xi），与模 l^2 的 mu 比较。"""
    ok = True
    for (l, P) in CERT[1]:
        a = [1, 0, 0]
        x = [0, 1, 0]

        def mul_int(u, v):
            r = [0] * 5
            for p in range(3):
                for q in range(3):
                    r[p + q] += u[p] * v[q]
            for d in (4, 3):
                w = r[d]
                r[d] = 0
                r[d - 3] += w
                r[d - 2] -= w
            return r[:3]
        base, e = x, P
        while e:
            if e & 1:
                a = mul_int(a, base)
            base = mul_int(base, base)
            e >>= 1
        if not (a[0] % l == 1 and a[1] % l == 0 and a[2] % l == 0):
            ok = False
            continue
        mu = [(a[0] - 1) // l, a[1] // l, a[2] // l]
        if ((mu[1] % l, mu[2] % l)) != mu_mod(1, l, P):
            ok = False
    return ok


def main():
    t0 = time.time()
    check_gf()
    check_utype()
    check_residues()
    check_m1()
    check_E2()
    S = check_small()
    check_primes()
    # U
    survU, tabsU = sieve('U', (1, 2))
    report('b2-sieve-U', not survU, 'T=5040，纤维 1、2：b≢0 的 %d 个剩余类全部被筛掉（幸存 %d 个）' % (T * (T - 1), len(survU)))
    unrU, usedU = padic('U', (1, 2), tabsU)
    okmu = check_mu_exact()
    report('b2-padic-U', not unrU and okmu, 'b≡0 (mod 5040)、b≠0：每个 n0 mod 5040 都有证书（未解决 %d 个）；用到的素数 %s；纤维 1 的 mu 大整数复核：%s'
           % (len(unrU), dict(sorted(usedU.items())), okmu))
    # E
    survE, tabsE = sieve('E', (1, 2, 3))
    report('b2-sieve-E', not survE, 'T=5040，纤维 1、2、3：b≢0 的剩余类全部被筛掉（幸存 %d 个）' % len(survE))
    unrE, usedE = padic('E', (1, 2, 3), tabsE)
    report('b2-padic-E', not unrE, 'b≡0 (mod 5040)、b≠0：每个 n0 都有证书（未解决 %d 个）；用到的素数 %s' % (len(unrE), dict(sorted(usedE.items()))))
    # 反向检查
    surv1, _ = sieve('U', (1,))
    s1set = {(n % T, b % T) for (n, b) in surv1}
    need = {(n % T, b % T) for (n, b) in S[('U', 1)] if b % T}
    ra = need <= s1set
    unrE1, _ = padic('E', (1,), tabsE)
    rb = ((-5) % T) in unrE1
    survM, _ = sieve('U', (1, 2), elems={2: lambda l: [1, 0, 0]})
    rc = (0, (-3) % T) in {(n, b) for (n, b) in survM}
    report('b2-reverse', ra and rb and rc,
           '(a) 只用纤维 1 时真解的类全部幸存：%s（幸存 %d 类，真解 %d 类）；(b) E 纤维 1 在 n≡-5 时 l 进检验失效：%s；'
           '(c) 纤维 2 元素换成 1 后公共解 (0,-3) 的类幸存：%s（幸存 %d 类）' % (ra, len(s1set), len(need), rb, rc, len(survM)))
    print('time %.1fs' % (time.time() - t0))
    npass = sum(RESULTS)
    nfail = len(RESULTS) - npass
    print('SUMMARY b2 pass=%d fail=%d' % (npass, nfail))
    return 0 if nfail == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
