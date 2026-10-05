# -*- coding: utf-8 -*-
"""c5a 探索 2：精确有理核对。
(1) Binet/谱分解：U_k(m) = (-1)^m/m! + sum_{j=1}^m (-1)^{m-j}/(m-j)! * L_j( y^{k+3(m-j)} * gt_j(y) )
    L_j(P) := [y^2](P mod f_j)，f_j = y^3 - y^2 - j，gt_j(y) = y^{3j+2}/j! + sum_{i<j} (j-i) y^{3i}/i!
    （L_j(P) = sum_{sigma: f_j(sigma)=0} P(sigma)/f_j'(sigma)，Lagrange 恒等式）
(2) 过滤序列：v_k = [x^k] P_{m-1}(x) G_m(x) = sum_i P_{m-1}[i] U_{k-i}(m)，对 k>=3m 应等于 m! L_m(gt_m(y) y^{k-3m})
(3) c_m 在 Q[y]/(f_m) 中的精确表示 r_m(y) = gt_m(y) * f_m'(y)^{-1} mod f_m，c_m = r_m(rho_m)
(4) m=4、m=18 的整数 rho：过滤 Q = P_m/(1 - rho x)，[x^k](Q G_m)/rho^k 在 k>=3m 为常数 W_m(1/rho)
"""
import os, sys, time
from fractions import Fraction
from math import factorial
from decimal import Decimal, getcontext

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_fast_column
from polylib import P_poly, pmul, peval, pdiv, trim

getcontext().prec = 90


def red_mul_y(v, j):
    a0, a1, a2 = v
    return (j * a2, a0, a1 + a2)          # y^3 = y^2 + j


def y_pow_table(j, N):
    tab = [(1, 0, 0)]
    for _ in range(N):
        tab.append(red_mul_y(tab[-1], j))
    return tab


def gt_coeffs(j):
    """gt_j(y) 作为 {指数: 系数}。"""
    d = {3 * j + 2: Fraction(1, factorial(j))}
    for i in range(j):
        d[3 * i] = d.get(3 * i, 0) + Fraction(j - i, factorial(i))
    return d


def L(j, poly_dict, tab):
    """[y^2](P mod f_j)"""
    s = Fraction(0)
    for e, c in poly_dict.items():
        s += c * tab[e][2]
    return s


def binet_U(k, m, tabs):
    tot = Fraction((-1) ** m, factorial(m))
    for j in range(1, m + 1):
        g = gt_coeffs(j)
        sh = k + 3 * (m - j)
        tot += Fraction((-1) ** (m - j), factorial(m - j)) * L(j, {e + sh: c for e, c in g.items()}, tabs[j])
    return tot


def solve3(A, b):
    A = [list(map(Fraction, row)) + [Fraction(bb)] for row, bb in zip(A, b)]
    n = 3
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [A[i][n] / A[i][i] for i in range(n)]


def reduce_mod_f(poly_dict, j):
    tab = y_pow_table(j, max(poly_dict) + 1)
    v = [Fraction(0)] * 3
    for e, c in poly_dict.items():
        for t in range(3):
            v[t] += c * tab[e][t]
    return v


def cm_exact_repr(m):
    """r(y) = r0 + r1 y + r2 y^2 with r * f'(y) == gt_m(y) mod f_m."""
    g = reduce_mod_f(gt_coeffs(m), m)
    # f'(y) = 3y^2 - 2y; matrix of multiplication by f' on basis 1,y,y^2
    cols = []
    for basis in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
        # basis * (3y^2 - 2y)
        b = list(basis)
        by = red_mul_y(b, m)
        by2 = red_mul_y(by, m)
        cols.append([3 * by2[t] - 2 * by[t] for t in range(3)])
    A = [[cols[c][r] for c in range(3)] for r in range(3)]
    return solve3(A, g)


def rho(m):
    if m == 0:
        return Decimal(1)
    y = Decimal(m) ** (Decimal(1) / Decimal(3)) + Decimal('0.5')
    for _ in range(300):
        y2 = y - (y ** 3 - y ** 2 - m) / (3 * y * y - 2 * y)
        if abs(y2 - y) < Decimal(10) ** (-85):
            return y2
        y = y2
    return y


def main():
    t0 = time.time()
    out = []
    K = 60
    MM = 20
    cols = {m: U_fast_column(m, K + 3 * MM + 70) for m in range(0, MM + 1)}
    tabs = {j: y_pow_table(j, K + 3 * MM + 3 * MM + 10) for j in range(1, MM + 1)}
    # (1) Binet
    bad = 0
    for m in range(0, MM + 1):
        for k in range(0, K + 1):
            if binet_U(k, m, tabs) != cols[m][k]:
                bad += 1
                if bad < 5:
                    out.append('Binet FAIL m=%d k=%d' % (m, k))
    out.append('(1) Binet spectral formula exact, m<=%d, k<=%d: bad=%d' % (MM, K, bad))
    # (2) filter
    bad = 0
    for m in range(1, MM + 1):
        Pm1 = P_poly(m - 1)
        tabm = y_pow_table(m, 3 * m + 2 + K + 5)
        g = gt_coeffs(m)
        for k in range(3 * m, 3 * m + K + 1):
            v = sum(Pm1[i] * cols[m][k - i] for i in range(len(Pm1)) if k - i >= 0)
            rhs = factorial(m) * L(m, {e + k - 3 * m: c for e, c in g.items()}, tabm)
            if v != rhs:
                bad += 1
    out.append('(2) filtered sequence v_k = m! L_m(gt_m y^{k-3m}), 1<=m<=%d, 3m<=k<=3m+%d: bad=%d' % (MM, K, bad))
    # (3) exact representation of c_m
    for m in range(1, 13):
        r = cm_exact_repr(m)
        rh = rho(m)
        val = Decimal(r[0].numerator) / Decimal(r[0].denominator) + \
            Decimal(r[1].numerator) / Decimal(r[1].denominator) * rh + \
            Decimal(r[2].numerator) / Decimal(r[2].denominator) * rh * rh
        out.append('c_%d = (%s) + (%s) rho + (%s) rho^2  = %s' % (m, r[0], r[1], r[2], str(val)[:30]))
    for m in (4, 18):
        r = cm_exact_repr(m)
        p = 2 if m == 4 else 3
        out.append('c_%d via repr at rho=%d: %s' % (m, p, r[0] + r[1] * p + r[2] * p * p))
    # (4) integer rho filter
    for m, p in ((4, 2), (18, 3)):
        Pm = P_poly(m)
        Q, rem = pdiv(Pm, [1, -p])
        assert rem == [] or all(c == 0 for c in rem)
        vals = set()
        for k in range(3 * m, 3 * m + K + 1):
            v = sum(Q[i] * cols[m][k - i] for i in range(len(Q)) if k - i >= 0)
            vals.add(Fraction(v) / p ** k)
        W = vals.pop() if len(vals) == 1 else None
        cm = W / peval(Q, Fraction(1, p)) if W is not None else None
        out.append('m=%d: [x^k](Q G_m)/%d^k constant for k=%d..%d: %s ; W_m(1/rho)=%s ; c_m=W/Q(1/rho)=%s' % (
            m, p, 3 * m, 3 * m + K, W is not None, W, cm))
    out.append('elapsed %.1fs' % (time.time() - t0))
    print('\n'.join(out))


if __name__ == '__main__':
    main()
