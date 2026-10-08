# -*- coding: utf-8 -*-
"""s11-b6b 复核脚本 3：命题 8（lam = -n 时的 Ei 闭式）的高精度数值核对（decimal，工作精度 70 位，要求 >= 45 位一致）。

左边一律是级数 f_x(t) = sum_m G_m(x) t^m，G_m 由 T1.3(1) 的递推 b_m G_m = G_{m-1} + m x^2 算（x=-1 时为精确有理数）；
右边是笔记的闭式。Ei 的差按「沿像道路同一分支」取：
  Ei(-z(1-t)) - Ei(-z) = Log(1-t) + sum_{k>=1} (-z)^k((1-t)^k - 1)/(k k!)，
因为 |t|<1 时像道路 w = -z(1-s)（s 从 0 到 t）满足 w/(-z) = 1-s 落在右半平面，log 的增量就是主值 Log(1-t)。
  E8-ei      Ei 级数 sum w^k/(k k!) 与 Ramanujan 级数 e^{w/2} sum (-1)^{n-1} w^n/(n! 2^{n-1}) sum_{k<=(n-1)/2} 1/(2k+1)
             在若干实的、复的 w 上一致（两者都去掉 gamma + log w），作为 Ei 实现的独立核对
  E8-xm1     x=-1：F(-1,t) = [e^t - 1 + t^2/(1-t) + e^{t-1}(Ei(1-t) - Ei(1))]/t^2，t in (-1,0) 与 (0,1) 两侧各 5 个点，另 3 个复 t
  E8-x0      x=-1：t->0 时括号 = t^2/2 + O(t^3)，F(-1,0) = 1/2 = G_0(-1)
  E8-gen     一般 n 的闭式：n=1、3 的实根（x<0，-z>0），n=1、2、3 的一个复根（-z 为复数），实 t 两侧与复 t
  E8-M       lam=-n 时 M = 1F1(1;n+1;-zt)/(1-x) = n!(-zt)^{-n}(e^{-zt} - sum_{k<n}(-zt)^k/k!)/(1-x)
  E8-rev     反向检查：去掉 t^2/(1-t)、Ei(1-t) 换成 Ei(1+t)、e^{t-1} 换成 e^{1-t}、n=3 时 sum_{k<n} 换成 sum_{k<=n}、
             复 x 时 log 加 2 pi i（换分支），都应明显不符
"""
import os
import sys
import time
from decimal import Decimal as D
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cdec import CD, set_prec, cexp, clog, pi, newton_real, newton_complex  # noqa: E402

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')

PREC = 70
TOL_DIGITS = 45
set_prec(PREC)
RES = []


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


def fmt(v):
    return '%.3e' % float(v)


def nterms(t_abs):
    import math
    if t_abs == 0:
        return 5
    return int((PREC + 5) * math.log(10) / (-math.log(float(t_abs)))) + 20


def ein_series(w):
    """sum_{k>=1} w^k/(k k!)（Ei 去掉 gamma + log w 的整函数部分）。"""
    w = CD.of(w)
    eps = D(10) ** (-(PREC + 8))
    s, term, k = CD(0), CD(1), 0
    while True:
        k += 1
        term = term * w / k
        add = term / k
        s = s + add
        if add.abs() < eps and k > 5:
            break
    return s


def ein_ramanujan(w):
    w = CD.of(w)
    eps = D(10) ** (-(PREC + 8))
    s, term, n = CD(0), CD(1), 0
    inner = D(0)
    while True:
        n += 1
        term = term * w / n                    # w^n/n!
        if (n - 1) % 2 == 0:
            inner += D(1) / (n)               # 加上 1/(2k+1)，2k+1 = n（n 奇）
        add = term * inner / (D(2) ** (n - 1))
        s = s + (add if n % 2 == 1 else -add)
        if add.abs() < eps and n > 10:
            break
    return cexp(w / 2) * s


def ei_diff_path(zneg, t, branch_shift=0):
    """Ei(-z(1-t)) - Ei(-z)，沿像道路取同一分支（|t|<1）：Log(1-t) + sum (-z)^k((1-t)^k-1)/(k k!)。"""
    w1 = CD.of(zneg)
    w2 = w1 * (1 - CD.of(t))
    lg = clog(1 - CD.of(t))
    if branch_shift:
        lg = lg + CD(0, 2 * pi() * branch_shift)
    return lg + ein_series(w2) - ein_series(w1)


def series_f(Gfun, t, N):
    t = CD.of(t)
    s, p = CD(0), CD(1)
    for m in range(N + 1):
        s = s + Gfun(m) * p
        p = p * t
    return s


def rel(a, b):
    a, b = CD.of(a), CD.of(b)
    den = max(a.abs(), D(1))
    return (a - b).abs() / den


def main():
    t0 = time.time()
    # ---------------- E8-ei ----------------
    ws = [D('0.05'), D(1), D('2.5'), D('-1.7'), CD(D('0.3'), D('1.1')), CD(D('-2'), D('0.5'))]
    worst = max(rel(ein_series(w), ein_ramanujan(w)) for w in ws)
    report('E8-ei', worst < D(10) ** (-(TOL_DIGITS + 10)),
           'Ei 的两种级数在 6 个 w（含负实数与复数）上一致，最大相对差 %s' % fmt(worst))

    # ---------------- x = -1 ----------------
    # x=-1：b_m = 2 + m，x^2 = 1。G_m 用 decimal 递推；m<=300 另用 Fraction 精确递推对照（递推是收缩的，误差不放大）
    Gx = [D(1) / 2]
    for m in range(1, 4000):
        Gx.append((Gx[-1] + m) / (m + 2))
    gf = Fr(1, 2)
    exact_ok = True
    for m in range(1, 301):
        gf = (gf + m) / (m + 2)
        q = (gf.numerator * 10 ** 75) // gf.denominator
        if abs(D(q) / D(10) ** 75 - Gx[m]) > D(10) ** (-(PREC - 3)):
            exact_ok = False
    if not exact_ok:
        print('  warning: decimal G_m(-1) deviates from exact')

    def Gm1(m):
        return CD(Gx[m])

    def F_closed_m1(t, variant=None):
        t = CD.of(t)
        one = CD(1)
        et = cexp(t)
        if variant == 'ei_plus':
            # Ei(1+t) - Ei(1) 代替 Ei(1-t) - Ei(1)
            d1 = clog(1 + t) + ein_series(1 + t) - ein_series(CD(1))
        else:
            d1 = clog(one - t) + ein_series(one - t) - ein_series(CD(1))
        pref = cexp(t - 1) if variant != 'exp_flip' else cexp(1 - t)
        mid = t * t / (one - t) if variant != 'drop' else CD(0)
        return (et - 1 + mid + pref * d1) / (t * t)

    real_ts = [D('-0.95'), D('-0.9'), D('-0.5'), D('-0.1'), D('-0.01'), D('0.01'), D('0.1'), D('0.5'), D('0.9'), D('0.95')]
    cplx_ts = [CD(0, D('0.5')), CD(D('-0.3'), D('0.6')), CD(D('0.7'), D('-0.5'))]
    worst = D(0)
    for t in real_ts + cplx_ts:
        tc = CD.of(t)
        N = nterms(tc.abs())
        a = series_f(Gm1, tc, N)
        b = F_closed_m1(tc)
        worst = max(worst, rel(a, b))
    report('E8-xm1', worst < D(10) ** (-TOL_DIGITS) and exact_ok,
           'x=-1 闭式 = 级数：t 取 (-1,0) 5 点、(0,1) 5 点、3 个复点，最大相对差 %s（工作精度 %d 位）；'
           'decimal 递推的 G_m(-1) 与 Fraction 精确值一致（m<=300）：%s' % (fmt(worst), PREC, exact_ok))

    # t -> 0
    ts = [D('1e-6'), D('1e-9')]
    ok0 = True
    vals = []
    for t in ts:
        tc = CD(t)
        br = cexp(tc) - 1 + tc * tc / (1 - tc) + cexp(tc - 1) * (clog(1 - tc) + ein_series(1 - tc) - ein_series(CD(1)))
        q = br / (tc * tc)
        vals.append(q.r)
        ok0 &= abs(q.r - D('0.5')) < 10 * t
    report('E8-x0', ok0, 'x=-1：括号/t^2 在 t=1e-6、1e-9 处为 %s、%s（-> 1/2 = G_0(-1)）' % (str(vals[0])[:14], str(vals[1])[:14]))

    # ---------------- 一般 n ----------------
    cases = []
    for n in (1, 3):
        xr = newton_real(lambda u: n * u ** 3 - u + 1, lambda u: 3 * n * u * u - 1, D('-1.3') if n == 1 else D('-0.85'))
        cases.append((n, CD(xr), 'real'))
    for n, guess in ((1, complex(0.662, 0.562)), (2, complex(0.5, 0.5)), (3, complex(0.4257, 0.4586))):
        xc = newton_complex(lambda u: n * u ** 3 - u + 1, lambda u: 3 * n * u * u - 1, CD.of(guess))
        cases.append((n, xc, 'complex'))

    def make_G(x, Nmax):
        x2 = x * x
        x3 = x2 * x
        G = []
        prev = CD(0)
        for m in range(Nmax + 1):
            bm = 1 - x - m * x3
            g = ((CD(1) if m == 0 else prev) + m * x2) / bm if m > 0 else CD(1) / bm
            G.append(g)
            prev = g
        return G

    def M_series(x, t, N):
        x3 = x * x * x
        s, p, P = CD(0), CD(1), CD(1)
        for m in range(N + 1):
            P = P * (1 - x - m * x3)
            s = s + p / P
            p = p * t
        return s

    def f_closed_gen(n, x, t, variant=None):
        z = CD(1) / (x * x * x)
        t = CD.of(t)
        # I_k(t) = int_0^t s^k e^{zs} ds = sum_j z^j t^{j+k+1}/(j!(j+k+1))
        kmax = n if variant == 'sum_n' else n - 1
        Isum = CD(0)
        eps = D(10) ** (-(PREC + 8))
        for k in range(kmax + 1):
            j, zt_j, fact = 0, CD(1), 1
            tk1 = t ** (k + 1)
            while True:
                term = zt_j * tk1 / (fact * (j + k + 1))
                Isum = Isum + term
                j += 1
                fact *= j
                zt_j = zt_j * z * t
                if term.abs() < eps and j > 10:
                    break
        dei = ei_diff_path(-z, t, branch_shift=1 if variant == 'branch' else 0)
        J = -Isum - cexp(z) * dei
        Mv = M_series(x, t, 400)
        return (Mv - 1 / (1 - t)) / x + z * (t ** (-n)) * cexp(-z * t) * J

    worst_gen = D(0)
    worst_M = D(0)
    lines = []
    for n, x, kind in cases:
        lam = (1 - x) / (x * x * x)
        lam_err = (lam + n).abs()
        G = make_G(x, 3500)
        w_case = D(0)
        tlist = [D('-0.9'), D('-0.5'), D('-0.05'), D('0.05'), D('0.5'), D('0.9'), CD(D('0.2'), D('0.6'))]
        for t in tlist:
            tc = CD.of(t)
            N = nterms(tc.abs())
            a = series_f(lambda m: G[m], tc, N)
            b = f_closed_gen(n, x, tc)
            w_case = max(w_case, rel(a, b))
            # M 的初等闭式
            wv = -tc / (x * x * x)
            fact_n = 1
            for i in range(1, n + 1):
                fact_n *= i
            partial = CD(0)
            pk, fk = CD(1), 1
            for k in range(n):
                if k > 0:
                    pk = pk * wv
                    fk *= k
                partial = partial + pk / fk
            M_el = fact_n * (wv ** (-n)) * (cexp(wv) - partial) / (1 - x)
            worst_M = max(worst_M, rel(M_series(x, tc, 400), M_el))
        worst_gen = max(worst_gen, w_case)
        lines.append('n=%d %s x=%s%+.12fi |lam+n|=%s rel=%s' % (n, kind, str(x.r)[:15], float(x.i), fmt(lam_err), fmt(w_case)))
    report('E8-gen', worst_gen < D(10) ** (-TOL_DIGITS),
           '一般 n 的闭式 = 级数（每个 x 取 t=-0.9,-0.5,-0.05,0.05,0.5,0.9,0.2+0.6i）：' + '; '.join(lines))
    report('E8-M', worst_M < D(10) ** (-TOL_DIGITS), 'M = n!(-zt)^{-n}(e^{-zt}-sum_{k<n}(-zt)^k/k!)/(1-x)，上述全部 (x,t)，最大相对差 %s' % fmt(worst_M))

    # ---------------- 反向检查 ----------------
    rev = []
    t = D('0.5')
    a = series_f(Gm1, CD(t), nterms(t))
    for var in ('drop', 'ei_plus', 'exp_flip'):
        rev.append(rel(a, F_closed_m1(CD(t), var)) > D('1e-3'))
    n, x, _ = cases[1]          # n=3 实根
    G = make_G(x, 3500)
    a = series_f(lambda m: G[m], CD(t), nterms(t))
    rev.append(rel(a, f_closed_gen(n, x, CD(t), 'sum_n')) > D('1e-3'))
    n, x, _ = cases[2]          # n=1 复根
    G = make_G(x, 3500)
    a = series_f(lambda m: G[m], CD(t), nterms(t))
    rev.append(rel(a, f_closed_gen(n, x, CD(t), 'branch')) > D('1e-3'))
    report('E8-rev', all(rev), '反向检查（t=0.5）：去掉 t^2/(1-t)、Ei(1-t)->Ei(1+t)、e^{t-1}->e^{1-t}、n=3 时多加一项、'
           '复 x 时 log 换分支，都明显不符：%s' % rev)
    print('time %.1fs' % (time.time() - t0))
    print('SUMMARY s11-b6b prop8_decimal pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
    return 0 if all(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
