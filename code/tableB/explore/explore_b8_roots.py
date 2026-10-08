# -*- coding: utf-8 -*-
"""表 B 的 B8 探索：u_k(m) 在 m<-s_k 处的实根位置（离整数多近）。

v_k(m) := u_k(m)/((m+1)(m+2)...(m+s_k))，次数 r=floor(2k/3)。
用精确有理数 Sturm 序列数 v_k 的全部实根，再用二分把每个根定位到 1e-12，
输出 y=-m 的值与它到最近整数的距离。只用标准库 + core.py 取真值。
"""
import sys
from fractions import Fraction
from math import comb
sys.path.insert(0, __file__.rsplit('code', 1)[0] + 'code')
from core import U_fast_table, N_from_U  # noqa: E402


def N_table(K):
    """N[k][q]，0<=k<=K，由三角递推（T1.4(2)）；k<=8 用 DP 容斥核对。"""
    N = [[0] * (K + 2) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1], N[2][2] = 1, 2
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            v = N[k - 1][q - 1] + N[k - 1][q]
            t = 0
            if q - 2 >= 0:
                t += N[k - 3][q - 2]
            t += 2 * N[k - 3][q - 1] + N[k - 3][q]
            N[k][q] = v + (q - 1) * t
    T = U_fast_table(min(K, 8), min(K, 8) + 1)
    for k in range(1, min(K, 8) + 1):
        for q in range(0, k + 1):
            assert N[k][q] == N_from_U(T, k, q), (k, q)
    return N


def poly_mul(a, b):
    c = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                c[i + j] += x * y
    return c


def u_poly(N, k):
    """u_k(m) 的单项式系数（升幂，Fraction）。"""
    res = [Fraction(0)] * (k + 1)
    # C(m+1,q) = prod_{i=0}^{q-1}(m+1-i)/q!
    b = [Fraction(1)]
    for q in range(0, k + 1):
        if q > 0:
            b = poly_mul(b, [Fraction(1 - (q - 1)), Fraction(1)])
            b = [x / q for x in b]
        if N[k][q]:
            for i, x in enumerate(b):
                res[i] += N[k][q] * x
    while len(res) > 1 and res[-1] == 0:
        res.pop()
    return res


def poly_divexact_linear(p, r):
    """p(m)/(m-r)，要求整除。p 升幂。"""
    n = len(p) - 1
    q = [Fraction(0)] * n
    rem = Fraction(0)
    # 降幂综合除法
    coeffs = p[::-1]
    out = []
    acc = Fraction(0)
    for c in coeffs:
        acc = acc * r + c
        out.append(acc)
    rem = out[-1]
    assert rem == 0, ('not divisible', r, rem)
    qd = out[:-1]
    return qd[::-1]


def peval(p, x):
    s = Fraction(0)
    for c in reversed(p):
        s = s * x + c
    return s


def pderiv(p):
    return [i * p[i] for i in range(1, len(p))] or [Fraction(0)]


def prem(a, b):
    a = list(a)
    while len(a) >= len(b) and any(a):
        if a[-1] == 0:
            a.pop()
            continue
        f = a[-1] / b[-1]
        sh = len(a) - len(b)
        for i, y in enumerate(b):
            a[sh + i] -= f * y
        a.pop()
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a or [Fraction(0)]


def sturm(p):
    seq = [p, pderiv(p)]
    while True:
        r = prem(seq[-2], seq[-1])
        if all(x == 0 for x in r):
            break
        seq.append([-x for x in r])
        if len(seq[-1]) == 1:
            break
    # 归一化：除以首项绝对值，避免分数膨胀
    out = []
    for s in seq:
        lc = abs(s[-1])
        out.append([x / lc for x in s])
    return out


def sign_changes_at(seq, x):
    vals = [peval(s, x) for s in seq]
    vals = [v for v in vals if v != 0]
    return sum(1 for i in range(len(vals) - 1) if (vals[i] > 0) != (vals[i + 1] > 0))


def count_roots(seq, a, b):
    """(a,b] 中的不同实根数。"""
    return sign_changes_at(seq, a) - sign_changes_at(seq, b)


def isolate(seq, a, b, out):
    n = count_roots(seq, a, b)
    if n == 0:
        return
    if n == 1 and b - a < Fraction(1, 2 ** 40):
        out.append((a, b))
        return
    if n == 1:
        # 二分到足够细
        p = seq[0]
        while b - a > Fraction(1, 2 ** 40):
            c = (a + b) / 2
            if count_roots(seq, a, c) == 1:
                b = c
            else:
                a = c
        out.append((a, b))
        return
    c = (a + b) / 2
    isolate(seq, a, c, out)
    isolate(seq, c, b, out)


def main(K=45):
    N = N_table(K)
    print('k  s_k  deg v  #real  roots y=-m (dist to nearest integer)')
    mind = []
    for k in range(2, K + 1):
        s = (k + 2) // 3
        u = u_poly(N, k)
        v = u
        for i in range(1, s + 1):
            v = poly_divexact_linear(v, Fraction(-i))
        seq = sturm(v)
        # Cauchy 界
        lc = abs(v[-1])
        B = 1 + max(abs(c) / lc for c in v[:-1])
        B = Fraction(int(B) + 1)
        roots = []
        isolate(seq, -B, B, roots)
        ys = []
        for a, b in roots:
            mid = (a + b) / 2
            ys.append(-float(mid))
        ys.sort()
        desc = []
        for y in ys:
            d = abs(y - round(y))
            desc.append('%.4f(%.3f)' % (y, d))
            if y > s:
                mind.append((d, k, y))
        print('%2d %3d %4d %4d  %s' % (k, s, len(v) - 1, len(ys), ' '.join(desc)))
    mind.sort()
    print('closest-to-integer roots with y>s_k:', [(round(d, 5), k, round(y, 4)) for d, k, y in mind[:12]])


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 45)
