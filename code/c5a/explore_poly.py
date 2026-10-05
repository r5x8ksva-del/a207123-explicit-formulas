# -*- coding: utf-8 -*-
"""c5a 探索 3：固定 k、m->oo。
- 由高度 DP 表 + 容斥得 N(k,q)（k<=60）；另用 Newton 前向差分直接求 U_k(m) 关于 m 的系数，二者互相独立地给出 [m^j]U_k
- D(k,d) = N(k,k-d)：由三角递推推出 d<=3 的多项式（符号求和），并找出精确成立门槛
- A_d(k) = k! [m^{k-d}] U_k(m)，d<=3
"""
import os, sys, time
from fractions import Fraction
from math import factorial, comb

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_fast_table, N_from_U, binom
from polylib import padd, psub, pmul, pscale, peval, interpolate, trim


def poly_shift(p, a):
    """p(k + a) 的系数（a 为整数）。"""
    res = []
    # Horner: p(k+a) = sum c_i (k+a)^i
    for c in reversed(p):
        res = padd(pmul(res, [a, 1]), [c]) if res else [c]
    return trim(res)


def indefinite_sum(delta, k0, val0):
    """返回多项式 p，满足 p(k) - p(k-1) = delta(k)（多项式恒等式）且 p(k0) = val0。"""
    n = len(delta)  # degree+1
    xs, ys = [], []
    v = Fraction(val0)
    for t in range(n + 1):
        k = k0 + t
        if t > 0:
            v += peval(delta, k)
        xs.append(k)
        ys.append(v)
    p = interpolate(xs, ys)
    # 验证恒等式
    assert trim(psub(psub(p, poly_shift(p, -1)), delta)) == [], 'indefinite sum identity failed'
    return p


def fmt_poly(p, var='k'):
    terms = []
    for i in range(len(p) - 1, -1, -1):
        c = p[i]
        if c == 0:
            continue
        terms.append('(%s)%s' % (c, '' if i == 0 else ('*%s' % var if i == 1 else '*%s^%d' % (var, i))))
    return ' + '.join(terms) if terms else '0'


def main():
    t0 = time.time()
    out = []
    K = 60
    T = U_fast_table(K, K)        # T[k][m], m<=60
    out.append('DP table built %.1fs' % (time.time() - t0))
    N = {(k, q): N_from_U(T, k, q) for k in range(0, K + 1) for q in range(0, k + 1)}
    D = lambda k, d: N.get((k, k - d), 0) if k - d >= 0 else 0
    # coefficient of m^j in U_k(m): (a) via N and C(m+1,q); (b) via forward differences
    def coeffs_from_N(k):
        c = [Fraction(0)] * (k + 1)
        for q in range(0, k + 1):
            # C(m+1, q) = (m+1)m...(m-q+2)/q!
            p = [Fraction(1)]
            for i in range(-1, q - 1):
                p = pmul(p, [Fraction(-i), Fraction(1)])
            for j, a in enumerate(p):
                c[j] += N[(k, q)] * a / factorial(q)
        return c

    def coeffs_from_diff(k):
        vals = [T[k][m] for m in range(k + 1)]
        diffs = []
        cur = vals[:]
        for q in range(k + 1):
            diffs.append(cur[0])
            cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
        c = [Fraction(0)] * (k + 1)
        for q in range(k + 1):
            p = [Fraction(1)]
            for i in range(q):
                p = pmul(p, [Fraction(-i), Fraction(1)])
            for j, a in enumerate(p):
                c[j] += diffs[q] * a / factorial(q)
        return c

    CO = {}
    agree = True
    for k in range(0, K + 1):
        a = coeffs_from_N(k)
        if k <= 40:
            b = coeffs_from_diff(k)
            if a != b:
                agree = False
        CO[k] = a
    out.append('coeffs via N vs via forward differences agree (k<=40): %s  (%.1fs)' % (agree, time.time() - t0))

    # D(k,0), D(k,1)
    out.append('D(k,0)=2 for 2<=k<=60: %s' % all(D(k, 0) == 2 for k in range(2, K + 1)))
    out.append('D(k,1)=k^2-k-4 for 4<=k<=60: %s ; k=1..3: %s' % (
        all(D(k, 1) == k * k - k - 4 for k in range(4, K + 1)), [D(k, 1) for k in range(1, 4)]))
    # symbolic D(k,2)
    D1 = [Fraction(-4), Fraction(-1), Fraction(1)]
    D0 = [Fraction(2)]
    # delta2(k) = D(k-1,1) + (k-3)[D(k-3,1) + 2 D(k-3,0)]  valid k>=7
    delta2 = padd(poly_shift(D1, -1), pmul([Fraction(-3), Fraction(1)], padd(poly_shift(D1, -3), pscale(D0, 2))))
    out.append('delta2(k) = %s' % fmt_poly(delta2))
    P2 = indefinite_sum(delta2, 6, D(6, 2))
    out.append('D(k,2) = %s' % fmt_poly(P2))
    ok_from = min(k for k in range(1, K + 1) if all(peval(P2, kk) == D(kk, 2) for kk in range(k, K + 1)))
    out.append('   D(k,2) poly matches data exactly for k>=%d (k<=60); values below: %s vs poly %s' % (
        ok_from, [D(k, 2) for k in range(1, ok_from)], [peval(P2, k) for k in range(1, ok_from)]))
    # symbolic D(k,3): delta3(k) = D(k-1,2) + (k-4)[D(k-3,2) + 2D(k-3,1) + D(k-3,0)]
    delta3 = padd(poly_shift(P2, -1), pmul([Fraction(-4), Fraction(1)],
                                          padd(padd(poly_shift(P2, -3), pscale(poly_shift(D1, -3), 2)), D0)))
    out.append('delta3(k) = %s' % fmt_poly(delta3))
    P3 = indefinite_sum(delta3, 8, D(8, 3))
    out.append('D(k,3) = %s' % fmt_poly(P3))
    ok_from = min(k for k in range(1, K + 1) if all(peval(P3, kk) == D(kk, 3) for kk in range(k, K + 1)))
    out.append('   D(k,3) poly matches data exactly for k>=%d (k<=60); values below: %s vs poly %s' % (
        ok_from, [D(k, 3) for k in range(1, ok_from)], [peval(P3, k) for k in range(1, ok_from)]))
    # integer-ness: 2^d d! * D ?
    for name, P, sc in (('D2', P2, 4), ('D3', P3, 24)):
        out.append('   %d*%s coefficients: %s' % (sc, name, [c * sc for c in P]))
    # e_j(-1,0,...,n-2) polynomials in n, j<=3
    epolys = []
    for j in range(0, 4):
        xs = list(range(1, 2 * j + 4))
        def e_val(n, j=j):
            vals = list(range(-1, n - 1))
            row = [1] + [0] * j
            for v in vals:
                for t in range(j, 0, -1):
                    row[t] += v * row[t - 1]
            return row[j]
        ys = [e_val(n) for n in xs]
        ep = interpolate(xs, ys)
        okn = all(peval(ep, n) == e_val(n) for n in range(1, 70))
        epolys.append(ep)
        out.append('e_%d(-1..n-2) = %s   (checked n=1..69: %s)' % (j, fmt_poly(ep, 'n'), okn))
    # A_d(k) = k! [m^{k-d}] U_k(m) = sum_{e=0}^d D(k,e) (-1)^{d-e} e_{d-e}(-1..k-e-2) * k!/(k-e)!
    Dp = [D0, D1, P2, P3]
    for d in range(0, 4):
        A = []
        for e in range(0, d + 1):
            ff = [Fraction(1)]
            for i in range(e):
                ff = pmul(ff, [Fraction(-i), Fraction(1)])          # k!/(k-e)! = k(k-1)...(k-e+1)
            term = pmul(pmul(Dp[e], poly_shift(epolys[d - e], -e)), ff)
            A = padd(A, pscale(term, (-1) ** (d - e)))
        out.append('A_%d(k) = k! [m^{k-%d}] U_k = %s' % (d, d, fmt_poly(A)))
        good = [k for k in range(1, K + 1) if k - d >= 0 and CO[k][k - d] * factorial(k) == peval(A, k)]
        ok_from = min(k for k in range(1, K + 1) if all((CO[kk][kk - d] * factorial(kk) == peval(A, kk)) for kk in range(k, K + 1)))
        out.append('   matches DP coefficients for k>=%d (up to 60); failing k below: %s' % (
            ok_from, [k for k in range(max(d, 1), ok_from) if k not in good]))
        # factorization attempts
        out.append('   A_%d at small k (data): %s' % (d, [CO[k][k - d] * factorial(k) for k in range(max(d, 1), 10)]))
    out.append('elapsed %.1fs' % (time.time() - t0))
    print('\n'.join(out))


if __name__ == '__main__':
    main()
