# -*- coding: utf-8 -*-
"""复核者 s10-b3 的公共工具（只用标准库，不导入 code/core.py，也不复用 code/tableB/ 或其他复核者的脚本）。

内容：
  * binom：论文第 2 节的约定（0<=b<=a 之外为 0，a<0 也为 0）；
  * U_dp / U_up_dp：按定义（三元组 good）自写的 DP，给出 U_k(m) 与「以上升结尾」的 U^up_k(m)；
  * U_brute：直接枚举 {0..m}^k；
  * 整系数多项式与幂级数（用于 W_m/P_m 的展开）；
  * 数域 K=Q(xi)=Q[X]/(X^3+X-1) 的精确运算（Fraction 三元组 a0+a1*xi+a2*xi^2），以及 K 上的多项式与 gcd。
"""
from fractions import Fraction
from math import comb
import itertools


# ---------------------------------------------------------------- 组合部分
def binom(a, b):
    """论文约定：除非 0<=b<=a，否则为 0（a<0 时也为 0）。"""
    if b < 0 or a < 0 or b > a:
        return 0
    return comb(a, b)


def good(a, b, c):
    return b == c or a >= max(b, c)


def _dp_counts(m, K):
    """返回列表 cnts，cnts[k] 是长度 k 的合法序列按最后两项 (a,b) 的计数字典（k>=2）。"""
    vals = range(m + 1)
    out = {}
    cnt = {(a, b): 1 for a in vals for b in vals}
    if K >= 2:
        out[2] = dict(cnt)
    for k in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in vals:
                if good(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
        cnt = new
        out[k] = dict(cnt)
    return out


def U_dp(m, K):
    """[U_0(m),...,U_K(m)]。"""
    res = []
    d = _dp_counts(m, K)
    for k in range(K + 1):
        if k == 0:
            res.append(1)
        elif k == 1:
            res.append(m + 1)
        else:
            res.append(sum(d[k].values()))
    return res


def U_up_dp(m, K):
    """[U^up_0(m),...,U^up_K(m)]：以上升结尾（h_{k-1}<h_k）的合法序列数。"""
    res = []
    d = _dp_counts(m, K)
    for k in range(K + 1):
        if k <= 1:
            res.append(0)
        else:
            res.append(sum(v for (a, b), v in d[k].items() if a < b))
    return res


def U_brute(m, k):
    tot = 0
    for h in itertools.product(range(m + 1), repeat=k):
        if all(good(h[j], h[j + 1], h[j + 2]) for j in range(k - 2)):
            tot += 1
    return tot


# ---------------------------------------------------------------- 整系数多项式 / 幂级数
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


def b_poly(i):
    """b_i(x)=1-x-i*x^3（系数从低到高）。"""
    return [1, -1, 0, -i]


def P_poly(m):
    p = [1]
    for i in range(m + 1):
        p = pmul(p, b_poly(i))
    return p


def W_poly(m):
    """W_m=1+x^2*sum_{j=1}^m j*P_{j-1}。"""
    w = [1]
    for j in range(1, m + 1):
        w = padd(w, [0, 0] + [j * c for c in P_poly(j - 1)])
    return w


def series_div(num, den, K):
    """num/den 的幂级数前 K+1 项（den[0]=+-1，整数运算）。"""
    assert den[0] in (1, -1)
    out = []
    for k in range(K + 1):
        s = num[k] if k < len(num) else 0
        for j in range(1, min(k, len(den) - 1) + 1):
            s -= den[j] * out[k - j]
        out.append(s * den[0])
    return out


# ---------------------------------------------------------------- 数域 K=Q(xi)，xi^3=1-xi
F0 = Fraction(0)
F1 = Fraction(1)


def K(a0=0, a1=0, a2=0):
    return (Fraction(a0), Fraction(a1), Fraction(a2))


KZERO = K(0)
KONE = K(1)
XI = K(0, 1, 0)


def kadd(x, y):
    return (x[0] + y[0], x[1] + y[1], x[2] + y[2])


def ksub(x, y):
    return (x[0] - y[0], x[1] - y[1], x[2] - y[2])


def kneg(x):
    return (-x[0], -x[1], -x[2])


def kmul(x, y):
    c0 = x[0] * y[0]
    c1 = x[0] * y[1] + x[1] * y[0]
    c2 = x[0] * y[2] + x[1] * y[1] + x[2] * y[0]
    c3 = x[1] * y[2] + x[2] * y[1]
    c4 = x[2] * y[2]
    # xi^3 = 1 - xi, xi^4 = xi - xi^2
    return (c0 + c3, c1 - c3 + c4, c2 - c4)


def kscale(x, q):
    q = Fraction(q)
    return (x[0] * q, x[1] * q, x[2] * q)


def kiszero(x):
    return x[0] == 0 and x[1] == 0 and x[2] == 0


def kmatrix(x):
    """乘 x 的矩阵（列：x*1, x*xi, x*xi^2，行：1, xi, xi^2 的系数）。"""
    cols = [x, kmul(x, XI), kmul(x, kmul(XI, XI))]
    return [[cols[j][i] for j in range(3)] for i in range(3)]


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def knorm(x):
    return det3(kmatrix(x))


def ktrace(x):
    M = kmatrix(x)
    return M[0][0] + M[1][1] + M[2][2]


def kinv(x):
    """解 kmatrix(x) * y = e_1（Cramer 法则）。"""
    M = kmatrix(x)
    D = det3(M)
    if D == 0:
        raise ZeroDivisionError("zero in K")
    rhs = [F1, F0, F0]
    y = []
    for j in range(3):
        Mj = [row[:] for row in M]
        for i in range(3):
            Mj[i][j] = rhs[i]
        y.append(det3(Mj) / D)
    return (y[0], y[1], y[2])


def kpow(x, n):
    if n < 0:
        return kpow(kinv(x), -n)
    r = KONE
    b = x
    while n:
        if n & 1:
            r = kmul(r, b)
        b = kmul(b, b)
        n >>= 1
    return r


def k_is_rational(x):
    return x[1] == 0 and x[2] == 0


def keval_intpoly(p, z):
    """整系数多项式 p（低到高）在 z∈K 处的值（Horner）。"""
    r = KZERO
    for c in reversed(p):
        r = kadd(kmul(r, z), K(c))
    return r


# ---------------------------------------------------------------- K 上的多项式（低到高，元素为 K 的三元组）
def kp_trim(p):
    p = list(p)
    while p and kiszero(p[-1]):
        p.pop()
    return p


def kp_deg(p):
    p = kp_trim(p)
    return len(p) - 1  # 零多项式为 -1


def kp_from_int(p):
    return kp_trim([K(c) for c in p])


def kp_add(p, q):
    n = max(len(p), len(q))
    return kp_trim([kadd(p[i] if i < len(p) else KZERO, q[i] if i < len(q) else KZERO) for i in range(n)])


def kp_sub(p, q):
    n = max(len(p), len(q))
    return kp_trim([ksub(p[i] if i < len(p) else KZERO, q[i] if i < len(q) else KZERO) for i in range(n)])


def kp_mul(p, q):
    if not p or not q:
        return []
    r = [KZERO] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if kiszero(a):
            continue
        for j, b in enumerate(q):
            if kiszero(b):
                continue
            r[i + j] = kadd(r[i + j], kmul(a, b))
    return kp_trim(r)


def kp_scale(p, c):
    return kp_trim([kmul(a, c) for a in p])


def kp_monic(p):
    p = kp_trim(p)
    if not p:
        return p
    return kp_scale(p, kinv(p[-1]))


def kp_rem(p, q):
    p = kp_trim(p)
    q = kp_monic(q)
    dq = len(q) - 1
    if dq < 0:
        raise ZeroDivisionError
    p = list(p)
    while len(p) - 1 >= dq and p:
        c = p[-1]
        shift = len(p) - 1 - dq
        for i in range(dq + 1):
            p[shift + i] = ksub(p[shift + i], kmul(c, q[i]))
        p = kp_trim(p)
    return p


def kp_gcd(p, q):
    a, b = kp_monic(p), kp_monic(q)
    while b:
        a, b = b, kp_monic(kp_rem(a, b))
    return kp_monic(a)


def kp_deriv(p):
    return kp_trim([kscale(p[i], i) for i in range(1, len(p))])


def kp_pow(p, n):
    r = [KONE]
    for _ in range(n):
        r = kp_mul(r, p)
    return r


def kp_eval(p, z):
    r = KZERO
    for c in reversed(p):
        r = kadd(kmul(r, z), c)
    return r


# ---------------------------------------------------------------- xi 的有理区间（二分 X^3+X-1，单调增）
def xi_interval(bits=200):
    lo, hi = Fraction(0), Fraction(1)
    for _ in range(bits):
        mid = (lo + hi) / 2
        if mid ** 3 + mid - 1 < 0:
            lo = mid
        else:
            hi = mid
    return lo, hi
