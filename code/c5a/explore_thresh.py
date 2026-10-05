# -*- coding: utf-8 -*-
"""c5a 探索 6：
(1) 一般 d：D(k,d)=N(k,k-d) 与 B_d(k)=(k-d)! [m^{k-d}]U_k(m) 在 k>=2d+2 是否为 2d 次多项式、k=2d+1 是否失效（d<=11）
(2) c_m 新闭式 c_m = rho (rho^{3m+1}/m! - e_{m-1}(rho^3))/(3 rho - 2) 的精确代数核对：
    在 Q[y]/(f_j) 中 gt_j(y) == y^2 (y^{3j+1}/j! - e_{j-1}(y^3))，j<=20
(3) m=18 的数值衰减（k 到 2000）
"""
import os, sys, time
from fractions import Fraction
from math import factorial
from decimal import Decimal, getcontext

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_fast_table, N_from_U, U_fast_column
from polylib import interpolate, peval
from explore_binet import reduce_mod_f, gt_coeffs, rho

getcontext().prec = 90


def main():
    t0 = time.time()
    out = []
    K = 60
    T = U_fast_table(K, K)
    N = {(k, q): N_from_U(T, k, q) for k in range(0, K + 1) for q in range(0, k + 1)}
    # coefficient [m^j] U_k via N
    def coeffs(k):
        c = [Fraction(0)] * (k + 1)
        for q in range(k + 1):
            p = [Fraction(1)]
            for i in range(-1, q - 1):
                new = [Fraction(0)] * (len(p) + 1)
                for a, x in enumerate(p):
                    new[a] += x * (-i)
                    new[a + 1] += x
                p = new
            for j, a in enumerate(p):
                c[j] += Fraction(N[(k, q)]) * a / factorial(q)
        return c
    CO = {k: coeffs(k) for k in range(K + 1)}
    for d in range(1, 12):
        Dk = {k: N[(k, k - d)] for k in range(d, K + 1)}
        Bk = {k: CO[k][k - d] * factorial(k - d) for k in range(d, K + 1)}
        res = []
        for name, seq in (('D', Dk), ('B', Bk)):
            xs = list(range(2 * d + 2, 4 * d + 3))
            p = interpolate(xs, [seq[x] for x in xs])
            okall = all(peval(p, k) == seq[k] for k in range(2 * d + 2, K + 1))
            fail_at = peval(p, 2 * d + 1) != seq[2 * d + 1]
            res.append('%s: deg=%d lc=%s poly on [2d+2,60]=%s fails at 2d+1=%s' % (
                name, len(p) - 1, p[-1], okall, fail_at))
        out.append('d=%2d  %s ; %s   (lc theory 1/(2^(d-1) d!) = %s)' % (d, res[0], res[1], Fraction(1, 2 ** (d - 1) * factorial(d))))
    # (2)
    ok = True
    for j in range(1, 21):
        lhs = reduce_mod_f(gt_coeffs(j), j)
        rhs_d = {3 * j + 3: Fraction(1, factorial(j))}
        for i in range(j):
            rhs_d[3 * i + 2] = rhs_d.get(3 * i + 2, 0) - Fraction(1, factorial(i))
        rhs = reduce_mod_f(rhs_d, j)
        if lhs != rhs:
            ok = False
    out.append('(2) gt_j(y) == y^2(y^{3j+1}/j! - e_{j-1}(y^3)) mod f_j for j<=20: %s' % ok)
    for m in (1, 2, 3, 4, 8, 18):
        r = rho(m)
        e = sum(r ** (3 * i) / factorial(i) for i in range(m))
        cm = r * (r ** (3 * m + 1) / factorial(m) - e) / (3 * r - 2)
        out.append('   c_%d (new form) = %s' % (m, str(cm)[:35]))
    # (3) m=18
    r18, r17 = rho(18), rho(17)
    c18 = Fraction(37105325714711350249401, 6830759936000)
    c18d = Decimal(c18.numerator) / Decimal(c18.denominator)
    r = r17
    e17 = sum(r ** (3 * i) / factorial(i) for i in range(17))
    c17 = r * (r ** (3 * 17 + 1) / factorial(17) - e17) / (3 * r - 2)
    theta = r17 / 3
    kappa = c17 * r17 ** 3 / c18d
    t1 = time.time()
    U = U_fast_column(18, 2000)
    out.append('(3) m=18: rho_17=%s theta=%s kappa=%s  (DP to k=2000 took %.1fs)' % (str(r17)[:20], str(theta)[:20], str(kappa)[:12], time.time() - t1))
    for k in (60, 200, 500, 1000, 1500, 1999):
        ek = Decimal(U[k]) / (c18d * Decimal(3) ** k) - 1
        ek1 = Decimal(U[k + 1]) / (c18d * Decimal(3) ** (k + 1)) - 1
        two = ek / (-kappa * theta ** k)
        out.append('   k=%4d e_k=% .6e rate=%.10f two-term ratio=%.10f' % (k, ek, ek1 / ek, two))
    out.append('elapsed %.1fs' % (time.time() - t0))
    print('\n'.join(out))


if __name__ == '__main__':
    main()
