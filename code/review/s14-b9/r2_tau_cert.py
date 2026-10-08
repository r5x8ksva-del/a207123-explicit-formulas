# -*- coding: utf-8 -*-
"""复核者 s14-b9：门槛 τ_i 的独立认证（不 import 项目代码）。

与作者（check_b9.py）的不同之处：
  * 区间运算用 decimal 的定向舍入（ROUND_CEILING / ROUND_FLOOR，60 位），不用 Fraction；
  * ρ_j 的包围区间由 Newton 近似加「f_j(lo)<=0<=f_j(hi)」的精确有理核对得到；
  * c_j 的上下界用 c5a 定理 2.2 的**第一种形式** ρ(ρ^{3j+1}/j! - e_{j-1}(ρ^3))/(3ρ-2)（带减法的区间运算），
    |σ_j|^2 用 j/ρ_j，|3σ-2|^2 用 9j/ρ+6ρ-2，|γ_j(σ)| 取第一种与第三种形式两个上界的较小者；
  * L_n(k,a) 用更粗的上界 (k+1+a)^n/n!（因 C(k+1,r)<=(k+1)^r/r!），单调性用
    q·((K+2+a)/(K+1+a))^n < 1（B(k):=A q^k (k+1+a)^n/n! 的相邻比关于 k 递减），所以 K* 由我自己重新找；
  * h_{k,i} 的精确值来自我自推的压缩 DP（s14_common.rt_dp_U，已与朴素 DP、枚举对照）。
另外（作者证书的复算）：用 decimal 定向舍入按作者的界（第二种形式、精确 L_n、引理 3 的单调条件）在作者给的 K* 处复算。
并做「界 >= 实际余项」的健全性检查：i<=12、0<=k<=2K*，实际 |h_{k,i}-c_iρ_i^k|/(c_iρ_i^k)（80 位）不超过作者形式的界。

用法：py -3.14 r2_tau_cert.py [I]（默认 I=40）
"""
import sys
import time
from decimal import Decimal as D, Context, ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN, localcontext
from fractions import Fraction as Fr
from math import comb, factorial, log, exp, lgamma

sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from s14_common import U_table, h_coef  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

PREC = 60
UP = Context(prec=PREC, rounding=ROUND_CEILING)
DN = Context(prec=PREC, rounding=ROUND_FLOOR)
NE = Context(prec=PREC, rounding=ROUND_HALF_EVEN)

TAU_CLAIM = [2, 8, 16, 24, 33, 41, 50, 59, 68, 77, 86, 95, 105, 114, 123, 132, 141, 151, 160, 169,
             178, 188, 197, 206, 216, 225, 234, 244, 253, 263, 272, 281, 291, 300, 310, 319, 328, 338, 347, 357]
KSTAR_CLAIM = [5, 18, 33, 50, 68, 86, 105, 125, 145, 166, 186, 207, 229, 250, 272, 294, 316, 338, 361, 384,
               407, 430, 453, 476, 500, 523, 547, 571, 595, 619, 643, 667, 691, 716, 740, 765, 789, 814, 839, 864]

RES = []


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


# ------------------------------------------------------------ 定向舍入的小工具（只用于非负数）
def upow(ctx, a, n):
    r = D(1)
    b = a
    while n:
        if n & 1:
            r = ctx.multiply(r, b)
        b = ctx.multiply(b, b)
        n >>= 1
    return r


def usum(ctx, xs):
    s = D(0)
    for x in xs:
        s = ctx.add(s, x)
    return s


def sqrt_up(x):
    s = x.sqrt(UP)
    while Fr(s) * Fr(s) < Fr(x):
        s = s.next_plus(UP)
    return s


def sqrt_dn(x):
    s = x.sqrt(DN)
    while Fr(s) * Fr(s) > Fr(x):
        s = s.next_minus(DN)
    return s


def frac_up(p, q):
    return UP.divide(D(p), D(q))


def frac_dn(p, q):
    return DN.divide(D(p), D(q))


def e_trunc(ctx, u, n):
    """e_n(u)=sum_{i<=n} u^i/i!（u>=0；n<0 时为 0），按 ctx 的方向舍入。"""
    s = D(0)
    p = D(1)
    for i in range(n + 1):
        s = ctx.add(s, ctx.divide(p, D(factorial(i))))
        p = ctx.multiply(p, u)
    return s


# ------------------------------------------------------------ 根与系数的区间
def rho_bracket(j):
    if j == 0:
        return D(1), D(1)
    with localcontext(Context(prec=PREC + 20, rounding=ROUND_HALF_EVEN)):
        x = D(repr(float(j) ** (1.0 / 3.0) + 0.4))
        for _ in range(60):
            x = x - (x * x * x - x * x - j) / (3 * x * x - 2 * x)
    eps = D(10) ** -(PREC - 12)
    lo, hi = DN.subtract(x, eps), UP.add(x, eps)
    f = lambda y: Fr(y) ** 3 - Fr(y) ** 2 - j  # noqa: E731
    assert f(lo) <= 0 <= f(hi) and lo > 1, (j, lo, hi)
    return lo, hi


class Params:
    """我自己的界（见模块说明）。"""

    def __init__(self, J):
        self.lo, self.hi, self.s_up, self.s_dn, self.c_up, self.c_dn, self.G = [], [], [], [], [], [], []
        for j in range(J + 1):
            lo, hi = rho_bracket(j)
            self.lo.append(lo)
            self.hi.append(hi)
            if j == 0:
                self.s_up.append(D(0)); self.s_dn.append(D(0))
                self.c_up.append(D(1)); self.c_dn.append(D(1)); self.G.append(D(0))
                continue
            s2_up, s2_dn = UP.divide(D(j), lo), DN.divide(D(j), hi)       # |σ|^2 = j/ρ
            s_up, s_dn = sqrt_up(s2_up), sqrt_dn(s2_dn)
            self.s_up.append(s_up)
            self.s_dn.append(s_dn)
            # c_j：第一种形式
            fj = D(factorial(j))
            Bup = UP.subtract(UP.divide(upow(UP, hi, 3 * j + 1), fj), e_trunc(DN, upow(DN, lo, 3), j - 1))
            Bdn = DN.subtract(DN.divide(upow(DN, lo, 3 * j + 1), fj), e_trunc(UP, upow(UP, hi, 3), j - 1))
            assert Bdn > 0, j
            c_up = UP.multiply(Bup, UP.divide(lo, DN.subtract(DN.multiply(3, lo), 2)))
            c_dn = DN.multiply(Bdn, DN.divide(hi, UP.subtract(UP.multiply(3, hi), 2)))
            self.c_up.append(c_up)
            self.c_dn.append(c_dn)
            # |3σ-2|^2 = 9j/ρ + 6ρ - 2 的下界
            d2 = DN.subtract(DN.add(DN.divide(D(9 * j), hi), DN.multiply(6, lo)), 2)
            d_dn = sqrt_dn(d2)
            s3 = upow(UP, s_up, 3)
            # 第一种形式：|σ|(|σ|^{3j+1}/j! + e_{j-1}(|σ|^3))/|3σ-2|
            F1 = UP.divide(UP.add(UP.divide(upow(UP, s_up, 3 * j + 2), fj),
                                  UP.multiply(s_up, e_trunc(UP, s3, j - 1))), d_dn)
            # 第三种形式：(|σ|^{3j+2}/j! + sum_{i<j}(j-i)|σ|^{3i}/i!)/(|σ||3σ-2|)
            num = UP.divide(upow(UP, s_up, 3 * j + 2), fj)
            p = D(1)
            for i in range(j):
                num = UP.add(num, UP.divide(UP.multiply(D(j - i), p), D(factorial(i))))
                p = UP.multiply(p, s3)
            F3 = UP.divide(num, DN.multiply(s_dn, d_dn))
            self.G.append(min(F1, F3))


class ParamsAuthor:
    """按作者 check_b9.py 的公式（第二种形式、|σ|^2=ρ(ρ-1)、|3σ-2|^2>=9lo^2-3hi-2），但用 decimal 定向舍入复算。"""

    def __init__(self, J, base):
        self.lo, self.hi = base.lo, base.hi
        self.s_up, self.c_up, self.c_dn, self.G = [], [], [], []
        for j in range(J + 1):
            lo, hi = self.lo[j], self.hi[j]
            if j == 0:
                self.s_up.append(D(0)); self.c_up.append(D(1)); self.c_dn.append(D(1)); self.G.append(D(0))
                continue

            def g16(ctx, y):
                s = ctx.divide(upow(ctx, y, 3 * j + 3), D(factorial(j)))
                for l in range(j):
                    s = ctx.add(s, ctx.divide(ctx.multiply(D(j - l), upow(ctx, y, 3 * l + 1)), D(factorial(l))))
                return s
            self.c_dn.append(DN.divide(g16(DN, lo), UP.add(UP.multiply(hi, hi), 3 * j)))
            self.c_up.append(UP.divide(g16(UP, hi), DN.add(DN.multiply(lo, lo), 3 * j)))
            s2lo = DN.multiply(lo, DN.subtract(lo, 1))
            s2hi = UP.multiply(hi, UP.subtract(hi, 1))
            s_up = sqrt_up(s2hi)
            self.s_up.append(s_up)
            d_lo = sqrt_dn(DN.subtract(DN.subtract(DN.multiply(9, DN.multiply(lo, lo)), UP.multiply(3, hi)), 2))
            self.G.append(UP.divide(g16(UP, s_up), DN.multiply(s2lo, d_lo)))


_SPEC_CACHE = {}


def term_specs(P, i):
    """余项各项：(A, base, n, a)，含义 |项| <= A·base^k·L_n(k,a)。j=i 的两个复根、0<=j<i 的实根（j=0 即 σ=1）、1<=j<i 的复根。"""
    key = (id(P), i)
    if key in _SPEC_CACHE:
        return _SPEC_CACHE[key]
    specs = [(UP.multiply(2, P.G[i]), P.s_up[i], 0, D(0))]
    for j in range(0, i):
        n = i - j
        specs.append((P.c_up[j], P.hi[j], n, upow(UP, P.hi[j], 3)))
        if j >= 1:
            specs.append((UP.multiply(2, P.G[j]), P.s_up[j], n, upow(UP, P.s_up[j], 3)))
    _SPEC_CACHE[key] = specs
    return specs


def L_exact_up(n, k, a):
    return usum(UP, (UP.divide(UP.multiply(D(comb(k + 1, r)), upow(UP, a, n - r)), D(factorial(n - r)))
                     for r in range(n + 1)))


def L_mine_up(n, k, a):
    return UP.divide(upow(UP, UP.add(D(k + 1), a), n), D(factorial(n)))


def cert_value(P, i, K, mine=True):
    """返回 (余项界之和（上界）, 单调条件是否全部成立)。"""
    rlo, clo = P.lo[i], P.c_dn[i]
    tot = D(0)
    mono = True
    for (A, base, n, a) in term_specs(P, i):
        q = UP.divide(base, rlo)
        L = L_mine_up(n, K, a) if mine else L_exact_up(n, K, a)
        tot = UP.add(tot, UP.divide(UP.multiply(UP.multiply(A, upow(UP, q, K)), L), clo))
        if mine:
            ratio = UP.multiply(q, upow(UP, UP.divide(UP.add(D(K + 2), a), DN.add(D(K + 1), a)), n))
            mono &= ratio < 1
        else:
            mono &= (K + 2 - n) > 0 and UP.multiply(q, D(K + 2)) < D(K + 2 - n)
    return tot, mono


def float_total(P, i, K):
    lr, lc = log(float(P.lo[i])), log(float(P.c_dn[i]))
    tot, mono = 0.0, True
    for (A, base, n, a) in term_specs(P, i):
        if A == 0:
            continue
        lq = log(float(base)) - lr
        af = float(a)
        tot += exp(log(float(A)) + K * lq + n * log(K + 1 + af) - lgamma(n + 1) - lc)
        mono &= (lq + n * log((K + 2 + af) / (K + 1 + af))) < 0
    return tot, mono


def find_my_K(P, i):
    K = i
    while True:
        tot, mono = float_total(P, i, K)
        if tot < 0.9 and mono:
            break
        K += 1
    while True:
        tot, mono = cert_value(P, i, K, mine=True)
        if tot < 1 and mono:
            return K, tot
        K += 1


def main(I):
    t0 = time.time()
    P = Params(I + 1)
    PA = ParamsAuthor(I + 1, P)
    print('参数（区间）准备 %.1fs；c_1..c_4 下界 %s' % (time.time() - t0, [str(NE.plus(P.c_dn[j]))[:14] for j in range(1, 5)]), flush=True)
    # 两套参数的一致性（都应包含真值，所以区间必须相交）
    ok_par = all(P.c_dn[j] <= PA.c_up[j] and PA.c_dn[j] <= P.c_up[j] for j in range(I + 2))
    widths = max(float((P.c_up[j] - P.c_dn[j]) / P.c_dn[j]) for j in range(1, I + 2))

    # ---- 我自己的证书
    t1 = time.time()
    myK, mytot = {}, {}
    for i in range(1, I + 1):
        myK[i], mytot[i] = find_my_K(P, i)
    Kmax = max(myK.values())
    print('我的 K*：%s（%.1fs）' % ([myK[i] for i in range(1, I + 1)], time.time() - t1), flush=True)
    t1 = time.time()
    U = U_table(I, Kmax)
    taus, ok_pos = [], True
    for i in range(1, I + 1):
        last_bad = None
        for k in range(0, myK[i] + 1):
            if h_coef(U, k, i) <= 0:
                last_bad = k
        taus.append(last_bad + 1 if last_bad is not None else 0)
    ok_tau = taus == TAU_CLAIM[:I]
    report('r2-tau-mine', ok_tau and ok_par,
           '我的证书（定向舍入、L 的粗上界、自己的单调条件）对 1<=i<=%d 全部通过（最大余项界和 %.3f）；精确部分 k<=K*_mine（K*_40=%s，DP 用时 %.1fs）；'
           'τ = 作者所列 %s；两套 c_j 区间相交 %s（我的 c_j 区间相对宽度 <= %.1e）'
           % (I, max(float(v) for v in mytot.values()), myK.get(40, '-'), time.time() - t1, ok_tau, ok_par, widths))
    if not ok_tau:
        print('  我的 τ：', taus)
    print('  K*_mine/K*_author：', ' '.join('%d:%d/%d' % (i, myK[i], KSTAR_CLAIM[i - 1]) for i in range(1, I + 1)), flush=True)

    # ---- 作者证书的复算（作者的 K*）
    t1 = time.time()
    ok_a, worst = True, D(0)
    per = []
    for i in range(1, I + 1):
        K = KSTAR_CLAIM[i - 1]
        tot, mono = cert_value(PA, i, K, mine=False)
        ok_a &= (tot < 1 and mono)
        worst = max(worst, tot)
        per.append(float(tot))
    # 作者所说的反向检查：K=τ_i 处同一界 >=1（2<=i<=12）
    rv = all(cert_value(PA, i, TAU_CLAIM[i - 1], mine=False)[0] >= 1 for i in range(2, min(I, 12) + 1))
    # 在 K*-1 处作者的界是否仍 <1（看 K* 是不是由 float 目标 0.5 定的，不影响证明）
    below = [i for i in range(1, I + 1) if cert_value(PA, i, KSTAR_CLAIM[i - 1] - 1, mine=False)[0] < 1]
    report('r2-tau-author', ok_a and rv,
           '作者的界在作者的 K* 处复算（decimal 定向舍入）：余项界和 <1 且引理 3 的单调条件成立（1<=i<=%d，最大 %.3f）%s；'
           'K=τ_i 处界 >=1（2<=i<=12）%s；在 K*-1 处界也 <1 的 i 有 %d 个（K* 不是最小可认证值，无碍）（%.1fs）'
           % (I, float(worst), ok_a, rv, len(below), time.time() - t1))

    # ---- 健全性：界 >= 实际余项（i<=12）
    t1 = time.time()
    HP = Context(prec=90, rounding=ROUND_HALF_EVEN)
    ok_s, min_ratio, nchk = True, None, 0
    Imax = min(I, 12)
    Kchk = 2 * KSTAR_CLAIM[Imax - 1]
    U2 = U_table(Imax, Kchk)
    for i in range(1, Imax + 1):
        # 高精度 ρ_i、c_i（中点）
        rho = HP.divide(HP.add(P.lo[i], P.hi[i]), 2)
        ci = HP.divide(HP.add(PA.c_dn[i], PA.c_up[i]), 2)
        for k in range(0, 2 * KSTAR_CLAIM[i - 1] + 1):
            main_ = HP.multiply(ci, HP.power(rho, k))
            act = abs(HP.subtract(D(h_coef(U2, k, i)), main_)) / main_
            bnd, _ = cert_value(PA, i, k, mine=False)
            nchk += 1
            if act > 0:
                r = bnd / act
                min_ratio = r if min_ratio is None or r < min_ratio else min_ratio
            if bnd < act * (1 - D(10) ** -20):
                ok_s = False
    report('r2-bound-sane', ok_s, '作者形式的余项界 >= 实际余项 |h_{k,i}-c_iρ_i^k|/(c_iρ_i^k)（1<=i<=%d，0<=k<=2K*_i，共 %d 点）；界/实际 的最小值 %.3f（%.1fs）'
           % (Imax, nchk, float(min_ratio), time.time() - t1))
    print('total %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    I = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    main(I)
    n_pass = sum(RES)
    print('SUMMARY s14-b9 r2 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
    sys.exit(0 if all(RES) else 1)
