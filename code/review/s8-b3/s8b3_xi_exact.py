# -*- coding: utf-8 -*-
"""s8-b3 独立核对 1：Q(xi)=Q[X]/(X^3+X-1) 中的精确运算（只用标准库 + code/core.py 的 U 真值）。

不导入 code/tableB 下的任何脚本。核对 notes/06-主Agent-表B-B3单族形状分类.md 用到的代数事实：
  x1  X^3+X-1 无有理根、判别式 -31、只有一个实根且在 (0.68,0.69)
  x2  N(xi)=1、N(1+xi)=3（定理 S 用）、N(1-xi)=1
  x3  xi^N 不是有理数（1<=|N|<=NMAX）
  x4  按定义自建 b_i、P_m、W_m：P_m 与 core 的 U 一致（G_m=W_m/P_m 的级数对照）；b_1|P_m；W_m(xi)=xi+xi^2
  x5  定理 S 的留数闭式  Res_xi(G_m)*u'(xi) = (-1)^m (1+xi) xi^(-3m-2)/(m-1)!
  x6  情形 (IV)：a_beta=(1-xi)^beta-(-xi)^beta 只在 beta=1 时是有理数；beta 为奇数>=3 时 a^2 也不是有理数；
      a_beta = xi^beta (xi^(2beta)-(-1)^beta) 恒等
  x7  情形 (I) 的指数 -3*beta*e（e=alpha-2beta）对 alpha>=1,beta>=1,e!=0 都非零，且 xi^(-3 beta e) 不是有理数
"""
import os
import sys
from fractions import Fraction as Fr
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_table  # noqa: E402  只取 U 的真值

FAILS = []


def check(name, ok, info=''):
    print(('PASS ' if ok else 'FAIL ') + name + ((' | ' + info) if info else ''))
    if not ok:
        FAILS.append(name)


# ---------------- Q(xi) 的元素 (a0,a1,a2) = a0 + a1 xi + a2 xi^2，xi^3 = 1 - xi ----------------
ZERO = (Fr(0), Fr(0), Fr(0))
ONE = (Fr(1), Fr(0), Fr(0))
XI = (Fr(0), Fr(1), Fr(0))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def scal(q, a):
    return tuple(Fr(q) * x for x in a)


def mul(a, b):
    c = [Fr(0)] * 5
    for i in range(3):
        if a[i] == 0:
            continue
        for j in range(3):
            c[i + j] += a[i] * b[j]
    c0, c1, c2, c3, c4 = c
    # xi^3 = 1 - xi ; xi^4 = xi - xi^2
    return (c0 + c3, c1 - c3 + c4, c2 - c4)


def mat(a):
    """乘 a 的矩阵（列 = a*1, a*xi, a*xi^2 的坐标）。"""
    cols = [mul(a, ONE), mul(a, XI), mul(a, mul(XI, XI))]
    return [[cols[j][i] for j in range(3)] for i in range(3)]


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def norm(a):
    return det3(mat(a))


def trace(a):
    M = mat(a)
    return M[0][0] + M[1][1] + M[2][2]


def inv(a):
    """解 mat(a) * y = e_0（Cramer）。"""
    M = mat(a)
    D = det3(M)
    assert D != 0
    y = []
    for j in range(3):
        Mj = [row[:] for row in M]
        for i in range(3):
            Mj[i][j] = ONE[i]
        y.append(det3(Mj) / D)
    return tuple(y)


def power(a, n):
    if n < 0:
        return power(inv(a), -n)
    r = ONE
    b = a
    while n:
        if n & 1:
            r = mul(r, b)
        b = mul(b, b)
        n >>= 1
    return r


def is_rational(a):
    return a[1] == 0 and a[2] == 0


# ---------------- 多项式（低次在前，整数/分数系数） ----------------
def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        if x == 0:
            continue
        for j, y in enumerate(q):
            r[i + j] += x * y
    return r


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pscal(c, p):
    return [c * x for x in p]


def pderiv(p):
    return [i * p[i] for i in range(1, len(p))]


def peval_xi(p):
    r = ZERO
    for coef in reversed(p):
        r = add(mul(r, XI), (Fr(coef), Fr(0), Fr(0)))
    return r


def b_poly(i):
    return [1, -1, 0, -i]          # b_i = 1 - x - i x^3


def P_poly(m):
    P = [1]
    for i in range(m + 1):
        P = pmul(P, b_poly(i))
    return P


def W_poly(m):
    # W_m = 1 + x^2 * sum_{j=1}^m j P_{j-1}
    S = [0]
    for j in range(1, m + 1):
        S = padd(S, pscal(j, P_poly(j - 1)))
    return padd([1], pmul([0, 0, 1], S))


def series_div(num, den, K):
    """num/den 的幂级数前 K+1 项（den(0)=1，整数运算）。"""
    assert den[0] == 1
    out = []
    for k in range(K + 1):
        v = num[k] if k < len(num) else 0
        for j in range(1, min(k, len(den) - 1) + 1):
            v -= den[j] * out[k - j]
        out.append(v)
    return out


def main():
    NMAX = 400
    # x1
    f = lambda t: t ** 3 + t - 1
    check('x1-no-rational-root', f(Fr(1)) != 0 and f(Fr(-1)) != 0, 'f(1)=%s f(-1)=%s' % (f(1), f(-1)))
    p_, q_ = 1, -1
    disc = -4 * p_ ** 3 - 27 * q_ ** 2
    check('x1-disc', disc == -31, 'disc=%d' % disc)
    # 实根区间：f(0.68)<0<f(0.69)，f 严格增（f'=3t^2+1>0）所以只有一个实根
    check('x1-real-root-interval', f(Fr(68, 100)) < 0 < f(Fr(69, 100)), 'f(0.68)=%s f(0.69)=%s' % (float(f(Fr(68, 100))), float(f(Fr(69, 100)))))
    # x2
    check('x2-N(xi)=1', norm(XI) == 1, str(norm(XI)))
    check('x2-N(1+xi)=3', norm(add(ONE, XI)) == 3, str(norm(add(ONE, XI))))
    check('x2-N(1-xi)=1', norm(sub(ONE, XI)) == 1, str(norm(sub(ONE, XI))))
    check('x2-xi^3=1-xi', power(XI, 3) == sub(ONE, XI))
    # x3
    bad = [N for N in range(-NMAX, NMAX + 1) if N != 0 and is_rational(power(XI, N))]
    check('x3-xi^N-irrational', not bad, '1<=|N|<=%d, rational ones: %s' % (NMAX, bad[:5]))
    # x4
    M = 12
    K = 70
    T = U_fast_table(K, M)
    ok_series = True
    for m in range(0, M + 1):
        g = series_div(W_poly(m), P_poly(m), K)
        if g != [T[k][m] for k in range(K + 1)]:
            ok_series = False
            print('   series mismatch at m=%d' % m)
    check('x4-G_m=W_m/P_m-vs-core', ok_series, 'm<=%d, k<=%d' % (M, K))
    ok_div = all(peval_xi(P_poly(m)) == ZERO for m in range(1, 26))
    check('x4-b1-divides-P_m', ok_div, '1<=m<=25')
    target = add(XI, mul(XI, XI))
    ok_w = all(peval_xi(W_poly(m)) == target for m in range(1, 26))
    check('x4-W_m(xi)=xi+xi^2', ok_w, '1<=m<=25')
    # x5 定理 S 的留数闭式
    ok_res = True
    one_minus = sub(ONE, XI)
    # u'(xi) = (3xi^2 - 2xi^3)/(1-xi)^2
    up = mul(sub(scal(3, power(XI, 2)), scal(2, power(XI, 3))), inv(mul(one_minus, one_minus)))
    for m in range(1, 16):
        rho = mul(peval_xi(W_poly(m)), inv(peval_xi(pderiv(P_poly(m)))))
        lhs = mul(rho, up)
        rhs = scal(Fr((-1) ** m, factorial(m - 1)), mul(add(ONE, XI), power(XI, -3 * m - 2)))
        if lhs != rhs:
            ok_res = False
            print('   residue formula fails at m=%d' % m)
    check('x5-thmS-residue-closed-form', ok_res, '1<=m<=15')
    # theta^3 = 3 for theta=(1+xi) xi^{-M}
    ok_th = all(norm(mul(add(ONE, XI), power(XI, -Mx))) == 3 for Mx in range(-30, 31))
    check('x5-thmS-N(theta)=3', ok_th, '|M|<=30')
    # x6 情形 (IV)
    rat_beta = []
    sq_rat_odd = []
    ident_ok = True
    for beta in range(1, 61):
        a = sub(power(one_minus, beta), power(scal(-1, XI), beta))
        if is_rational(a):
            rat_beta.append(beta)
        if beta % 2 == 1 and beta >= 3 and is_rational(mul(a, a)):
            sq_rat_odd.append(beta)
        alt = mul(power(XI, beta), sub(power(XI, 2 * beta), scal((-1) ** beta, ONE)))
        if alt != a:
            ident_ok = False
    check('x6-a_beta-rational-only-beta1', rat_beta == [1], 'beta<=60, rational at %s' % rat_beta)
    check('x6-a_beta^2-not-rational-odd>=3', not sq_rat_odd, 'odd 3<=beta<=59, bad=%s' % sq_rat_odd)
    check('x6-a_beta-identity', ident_ok, 'a=(1-xi)^b-(-xi)^b = xi^b(xi^2b-(-1)^b), beta<=60')
    # x7 情形 (I) 的指数
    ok7 = True
    cnt = 0
    for n in range(2, 41):
        for beta in range(1, n):
            alpha = n - beta
            e = alpha - 2 * beta
            if e == 0:
                continue
            Nexp = -3 * beta * e
            cnt += 1
            if Nexp == 0 or is_rational(power(XI, Nexp)):
                ok7 = False
                print('   case (I) exponent problem at', (alpha, beta))
    check('x7-caseI-exponent-irrational', ok7, '%d shapes with alpha,beta>=1, e!=0, alpha+beta<=40' % cnt)
    # 反向检查：故意改错，核对程序应当能发现
    check('neg-xi^0-is-rational', is_rational(power(XI, 0)))
    m = 3
    rho = mul(peval_xi(W_poly(m)), inv(peval_xi(pderiv(P_poly(m)))))
    wrong = scal(Fr((-1) ** m, factorial(m)), mul(add(ONE, XI), power(XI, -3 * m - 2)))
    check('neg-thmS-residue-with-m!-differs', mul(rho, up) != wrong)
    check('neg-W_m(xi)!=xi', peval_xi(W_poly(5)) != XI)
    check('neg-b2-does-not-vanish-at-xi', peval_xi(b_poly(2)) != ZERO)
    print('SUMMARY: %d FAIL' % len(FAILS), FAILS)
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
