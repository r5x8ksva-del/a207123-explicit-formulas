# -*- coding: utf-8 -*-
"""复核者 s14-b9：真值、c5a 定理 2.2 / notes/16 引理 1、引理 2(b) 的独立核对（不 import 项目代码）。

  r1-dp      逐个枚举 = 朴素对 DP（k<=7, m<=4）；朴素对 DP = 压缩 DP（k<=60, m<=12）
  r1-thm22   c5a 定理 2.2 的精确核对（整数运算）：m!·U_k(m) = sum_j (-1)^{m-j} C(m,j) S_j(k+3(m-j))，
             S_j(N) := [y^2]( j!·g_j(y)·y^N mod f_j )，g_j(y)=y^{3j+2}/j!+sum_{i<j}(j-i)y^{3i}/i!（γ_j=g_j/f_j'），
             用 Lagrange 恒等式 sum_σ P(σ)/f'(σ) = [y^2](P mod f)。对 m<=40、0<=k<=3m+12 核对；因为两边都满足以
             (y-1)∏_{j<=m} f_j 为特征多项式的 3m+1 阶常系数递推（G_m=W_m/P_m 为真分式），k<=3m 相等即对一切 k 相等。
  r1-lem1    引理 1 的精确核对：i!·h_{k,i} = sum_j (-1)^{i-j} C(i,j) sum_r C(k+1,r) n!/(n-r)! S_j(k+3(n-r))（n=i-j），
             i<=15、k<=70
  r1-lag     Lagrange 恒等式本身的数值核对（复数根用 Decimal 复数 Newton 求出，60 位）
  r1-lem1num 引理 1 的高精度数值核对（Decimal 复数，60 位；0<=i<=10，0<=k<=40），并看虚部
  r1-lem2b   引理 2(b) 的三个等式：|σ|^2=ρ(ρ-1)、2Re σ=1-ρ、|σ^2+3j|=|σ|^2 sqrt(9ρ^2-3ρ-2)（1<=j<=60，σ 由 Newton 独立求出）；
             |γ_j(σ)| <= g16_j(|σ|)/(|σ|^2 sqrt(9ρ^2-3ρ-2))；引理 2.1(c) |σ_j|<ρ_{j-1}；c_j 三种形式一致
"""
import sys
import time
from decimal import Decimal as D, getcontext
from fractions import Fraction as Fr
from math import comb, factorial

import numpy as np

sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from s14_common import brute_U, pair_dp_U, rt_dp_U, U_table, h_coef  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


# ---------------------------------------------------------------- Lagrange 形式（整数）
def c2_table(j, Nmax):
    """c2[n] = [y^2](y^n mod (y^3-y^2-j))，n=0..Nmax（整数）。"""
    a0, a1, a2 = 1, 0, 0
    out = []
    for _ in range(Nmax + 1):
        out.append(a2)
        a0, a1, a2 = j * a2, a0, a1 + a2
    return out


def S_table(j, Nmax):
    """S_j(N) = [y^2](j! g_j(y) y^N mod f_j)，N=0..Nmax；j=0 时 S_0 ≡ 1。"""
    if j == 0:
        return [1] * (Nmax + 1)
    c2 = c2_table(j, Nmax + 3 * j + 2)
    fj = factorial(j)
    terms = [(3 * j + 2, 1)] + [(3 * i, (j - i) * (fj // factorial(i))) for i in range(j)]
    return [sum(cf * c2[e + N] for e, cf in terms) for N in range(Nmax + 1)]


def check_thm22(M, U):
    ok = True
    bad = None
    Nmax = (3 * M + 12) + 3 * M + 2
    S = [S_table(j, Nmax) for j in range(M + 1)]
    for m in range(M + 1):
        Kc = 3 * m + 12
        for k in range(Kc + 1):
            rhs = sum((-1) ** (m - j) * comb(m, j) * S[j][k + 3 * (m - j)] for j in range(m + 1))
            if rhs != factorial(m) * U[m][k]:
                ok = False
                bad = (m, k)
                break
        if not ok:
            break
    return ok, bad


def check_lem1(I, K, U):
    ok = True
    bad = None
    Nmax = K + 3 * I + 2
    S = [S_table(j, Nmax) for j in range(I + 1)]
    for i in range(I + 1):
        for k in range(K + 1):
            tot = 0
            for j in range(i + 1):
                n = i - j
                inner = sum(comb(k + 1, r) * (factorial(n) // factorial(n - r)) * S[j][k + 3 * (n - r)]
                            for r in range(n + 1))
                tot += (-1) ** (i - j) * comb(i, j) * inner
            if tot != factorial(i) * h_coef(U, k, i):
                ok = False
                bad = (i, k)
                break
        if not ok:
            break
    return ok, bad


# ---------------------------------------------------------------- Decimal 复数
def cadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def csub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def cdiv(a, b):
    d = b[0] * b[0] + b[1] * b[1]
    return ((a[0] * b[0] + a[1] * b[1]) / d, (a[1] * b[0] - a[0] * b[1]) / d)


def cpow(a, n):
    r = (D(1), D(0))
    b = a
    while n:
        if n & 1:
            r = cmul(r, b)
        b = cmul(b, b)
        n >>= 1
    return r


def cabs2(a):
    return a[0] * a[0] + a[1] * a[1]


def cscale(a, s):
    return (a[0] * s, a[1] * s)


def roots_dec(j):
    """f_j 的三个根（Decimal 复数，Newton 从 numpy 初值出发）；返回 (实根, [三个根])。"""
    if j == 0:
        return D(1), [(D(1), D(0))]
    out = []
    for z in np.roots([1, -1, 0, -j]):
        s = (D(repr(float(z.real))), D(repr(float(z.imag))))
        for _ in range(12):
            f = csub(csub(cmul(cmul(s, s), s), cmul(s, s)), (D(j), D(0)))
            fp = csub(cscale(cmul(s, s), D(3)), cscale(s, D(2)))
            s = csub(s, cdiv(f, fp))
        out.append(s)
    real = [s for s in out if abs(s[1]) < D(10) ** -40]
    assert len(real) == 1, (j, out)
    return real[0][0], out


def gamma_dec(j, s):
    """γ_j(σ) 的第三种形式 g_j(σ)/f_j'(σ)。"""
    if j == 0:
        return (D(1), D(0))
    s3 = cmul(cmul(s, s), s)
    num = cscale(cpow(s, 3 * j + 2), D(1) / D(factorial(j)))
    p = (D(1), D(0))
    for i in range(j):
        num = cadd(num, cscale(p, D(j - i) / D(factorial(i))))
        p = cmul(p, s3)
    fp = csub(cscale(cmul(s, s), D(3)), cscale(s, D(2)))
    return cdiv(num, fp)


def main():
    t0 = time.time()
    getcontext().prec = 60
    # ---- r1-dp
    ok_b = all(brute_U(k, m) == pair_dp_U(7, m)[k] for m in range(0, 5) for k in range(0, 8))
    ok_p = all(pair_dp_U(60, m) == rt_dp_U(60, m) for m in range(0, 13))
    report('r1-dp', ok_b and ok_p, '枚举 = 朴素对 DP（k<=7,m<=4）%s；朴素对 DP = 压缩 DP（k<=60,m<=12）%s（%.1fs）'
           % (ok_b, ok_p, time.time() - t0))

    # ---- r1-thm22
    t1 = time.time()
    M = 40
    U = U_table(M, 3 * M + 12)
    ok, bad = check_thm22(M, U)
    report('r1-thm22', ok, 'c5a 定理 2.2 精确成立（m<=%d，0<=k<=3m+12；按递推阶 3m+1 即对一切 k 成立）%s（%.1fs）'
           % (M, '' if ok else 'first bad (m,k)=%s' % (bad,), time.time() - t1))

    # ---- r1-lem1
    t1 = time.time()
    I1, K1 = 15, 70
    U1 = U_table(I1, K1)
    ok, bad = check_lem1(I1, K1, U1)
    report('r1-lem1', ok, '引理 1 精确成立（0<=i<=%d，0<=k<=%d，整数运算）%s（%.1fs）'
           % (I1, K1, '' if ok else 'first bad (i,k)=%s' % (bad,), time.time() - t1))

    # ---- 根（Decimal）
    roots = {j: roots_dec(j) for j in range(0, 61)}

    # ---- r1-lag：sum_σ σ^n/f'(σ) = [y^2](y^n mod f)
    worst = D(0)
    for j in (1, 2, 4, 7, 18, 30):
        c2 = c2_table(j, 60)
        for n in range(0, 61, 3):
            v = (D(0), D(0))
            for s in roots[j][1]:
                fp = csub(cscale(cmul(s, s), D(3)), cscale(s, D(2)))
                v = cadd(v, cdiv(cpow(s, n), fp))
            err = abs(v[0] - c2[n]) / max(D(1), abs(D(c2[n]))) + abs(v[1])
            worst = max(worst, err)
    report('r1-lag', worst < D(10) ** -40, 'Lagrange 恒等式 sum σ^n/f\'(σ)=[y^2](y^n mod f)（j∈{1,2,4,7,18,30}，n<=60）：最大相对误差 %.1e'
           % float(worst))

    # ---- r1-lem1num
    t1 = time.time()
    worst, worst_im = D(0), D(0)
    U40 = U_table(10, 40)
    gcache = {(j, idx): gamma_dec(j, s) for j in range(0, 11) for idx, s in enumerate(roots[j][1])}
    for i in range(0, 11):
        for k in range(0, 41):
            v = (D(0), D(0))
            big = D(0)
            for j in range(0, i + 1):
                n = i - j
                for idx, s in enumerate(roots[j][1]):
                    s3 = cmul(cmul(s, s), s)
                    L = (D(0), D(0))
                    for r in range(n + 1):
                        L = cadd(L, cscale(cpow(s3, n - r), D(comb(k + 1, r)) / D(factorial(n - r))))
                    term = cmul(cmul(gcache[(j, idx)], cpow(s, k)), L)
                    if (i - j) % 2:
                        term = (-term[0], -term[1])
                    v = cadd(v, term)
                    big = max(big, cabs2(term).sqrt())
            ex = h_coef(U40, k, i)
            worst = max(worst, abs(v[0] - ex) / big)
            worst_im = max(worst_im, abs(v[1]) / big)
    report('r1-lem1num', worst < D(10) ** -45 and worst_im < D(10) ** -45,
           '引理 1 高精度数值（60 位，0<=i<=10，0<=k<=40）：|实部-精确值|/最大项 <= %.1e，|虚部|/最大项 <= %.1e（%.1fs）'
           % (float(worst), float(worst_im), time.time() - t1))

    # ---- r1-lem2b
    ok_id, ok_bd, ok_c, ok_forms = True, True, True, True
    wid = D(0)
    rhos = {j: roots[j][0] for j in roots}
    for j in range(1, 61):
        rho, rs = roots[j]
        cpx = [s for s in rs if abs(s[1]) > D(10) ** -40]
        assert len(cpx) == 2
        for s in cpx:
            a2 = cabs2(s)
            e1 = abs(a2 - rho * (rho - 1))
            e2 = abs(2 * s[0] - (1 - rho))
            s2p = cadd(cmul(s, s), (D(3 * j), D(0)))
            e3 = abs(cabs2(s2p).sqrt() - a2 * (9 * rho * rho - 3 * rho - 2).sqrt())
            wid = max(wid, e1 / a2, e2, e3 / a2)
            # 界：|γ| <= g16(|σ|)/(|σ|^2 sqrt(9ρ^2-3ρ-2))，g16(y)=y^{3j+3}/j!+sum (j-l) y^{3l+1}/l!
            y = a2.sqrt()
            g16 = y ** (3 * j + 3) / factorial(j) + sum(D(j - l) * y ** (3 * l + 1) / factorial(l) for l in range(j))
            bound = g16 / (a2 * (9 * rho * rho - 3 * rho - 2).sqrt())
            gam = cabs2(gamma_dec(j, s)).sqrt()
            if not gam <= bound:
                ok_bd = False
            # 引理 2.1(c)
            if not y < rhos[j - 1]:
                ok_c = False
        # c_j 三种形式：第一种 ρ(ρ^{3j+1}/j! - e_{j-1}(ρ^3))/(3ρ-2)；第二种 g16(ρ)/(ρ^2+3j)；第三种 gamma_dec
        u = rho ** 3
        e = sum(u ** i / factorial(i) for i in range(j))
        c1 = rho * (rho ** (3 * j + 1) / factorial(j) - e) / (3 * rho - 2)
        g16r = rho ** (3 * j + 3) / factorial(j) + sum(D(j - l) * rho ** (3 * l + 1) / factorial(l) for l in range(j))
        c2v = g16r / (rho * rho + 3 * j)
        c3v = gamma_dec(j, (rho, D(0)))[0]
        if not (abs(c1 - c2v) / c2v < D(10) ** -45 and abs(c3v - c2v) / c2v < D(10) ** -45 and c2v > 0):
            ok_forms = False
    ok_id = wid < D(10) ** -45
    # c5a §2.4 表的抽查
    tab = {1: '2.20960813177848081994505234781', 4: '107.5', 8: '19179.3074772177997083232848565'}
    ok_tab = True
    for j, sv in tab.items():
        rho = roots[j][0]
        c2v = (rho ** (3 * j + 3) / factorial(j) + sum(D(j - l) * rho ** (3 * l + 1) / factorial(l) for l in range(j))) / (rho * rho + 3 * j)
        ok_tab &= abs(c2v - D(sv)) < D(10) ** -25
    report('r1-lem2b', ok_id and ok_bd and ok_c and ok_forms and ok_tab,
           '引理 2(b) 三个等式（1<=j<=60，最大偏差 %.1e）%s；|γ_j(σ)| 的界成立 %s；|σ_j|<ρ_{j-1} %s；c_j 三种形式一致且 >0 %s；与 c5a §2.4 表一致 %s'
           % (float(wid), ok_id, ok_bd, ok_c, ok_forms, ok_tab))
    print('total %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
    n_pass = sum(RES)
    print('SUMMARY s14-b9 r1 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
    sys.exit(0 if all(RES) else 1)
