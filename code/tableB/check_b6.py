# -*- coding: utf-8 -*-
"""表 B 的 B6（整表能否只用一元 1F1 / 不完全 Gamma 写成有限闭式）的核对脚本（2026-10-08）。
证明见 notes/11-主Agent-表B-B6-一元合流函数闭式不存在.md。

记号：b_i = 1 - x - i x^3，P_m = b_0 b_1 ... b_m，lam = (1-x)/x^3，z = x^-3，e_n(z) = sum_{j<=n} z^j/j!，
  M(t)  = sum_m t^m/P_m（= 1F1(1;1-lam;-zt)/(1-x)，T3.1），
  Xi(t) = t e^{-zt} sum_n e_n(z) t^n/(n+1-lam)（= t e^{-zt} Phi_1(1-lam,1;2-lam;t,zt)/(1-lam)），
  L[Y]  = (1-x-t)Y - x^3 t Y'（T3.2 的 L_A，A=1-x），gamma(t) = 1 + x^2 t/(1-t)^2，L[F] = gamma。
  命题 1（结构）：F = (M - 1/(1-t))/x + z Xi，在 Q(x)[[t]] 中。
  命题 2（单值）：固定 x（lam 不是非负整数），f_x(t) = sum_m G_m(x) t^m（|t|<1）。gamma_0 = 圆周 |t|=t0（逆时针），
  gamma_1 = 圆周 |t-1|=1-t0（逆时针），基点 t0 in (0,1)。f_x^{gamma_0} = f_x，f_x^{gamma_1} = f_x - nu*omega，
  omega(t) = t^lam e^{-zt}（主支），nu = 2 pi i z e^z；先 gamma_0 后 gamma_1 与先 gamma_1 后 gamma_0 之差为 -nu(1-e^{2 pi i lam})omega。
逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b6 pass=<n> fail=<n>」。
  b6-struct   命题 1 在 13 个有理 x 上逐系数精确成立（m<=40）；左边的 G_m 用 T1.3(1) 的闭式 1/P_m + x^2 sum_j j/prod_{i=j}^m b_i，
              另与递推 b_m G_m = G_{m-1} + m x^2 对照
  b6-ode      证明里用到的算子恒等式（13 个有理 x，t^40 以内精确）：L[M]=1；L[(M-1/(1-t))/x] = gamma + t/(1-t)；
              L[Xi] = -x^3 t/(1-t)；(n+1-lam)K_n = e_n 且 sum e_n t^n = e^{zt}/(1-t)；z - lam = x^-2（留数常数）
  b6-phi1     Xi = t e^{-zt} Phi_1(1-lam,1;2-lam;t,zt)/(1-lam)：Phi_1 按 Pochhammer 定义的二重和逐系数相同（N<=30）
  b6-dp       对照原始定义：把命题 1 右边按 x 展成 Laurent 级数（1/b_i 展成整系数幂级数），负幂全部相消，x^k t^m 系数
              等于 core.U_fast_table 的 U_k(m)（k<=40, m<=12）；z Xi 的系数全是整数
  b6-mono     （数值，RK4 积分 ODE，双精度；佐证命题 2，不是证明的一部分）5 个 x（含复数 x）：绕 0 不变、绕 1 的跳跃等于
              -nu*omega(t0)、两圈交换次序之差等于 -nu(1-e^{2 pi i lam})omega(t0)，相对误差 < 1e-8
  b6-sharp    lam = -n（n=1,2,3；x 为 n x^3 - x + 1 = 0 的实根，n=2 时 x=-1）：Ei 闭式
              f_x = (M - 1/(1-t))/x + z t^{-n} e^{-zt}[ -sum_{k<n} int_0^t s^k e^{zs}ds - e^z(Ei(-z(1-t)) - Ei(-z)) ]
              与级数 sum G_m t^m 在 5 个 t 上一致（相对误差 < 1e-11）；x=-1 时两圈的交换子数值为 0（交换型），而绕 1 的跳跃仍非零
  b6-qrat     lam = 1/2（x 为 x^3 + 2x - 2 = 0 的实根）：gamma_0 与 gamma_1 不交换，但 gamma_0^2 与 gamma_1 交换（数值），
              与「lam 为有理数时 f_x 是虚交换型」一致
  b6-reverse  反向检查：(a) Xi 里把 e_n 换成 e_{n+1}，命题 1 失败；(b) 右端换成无极点的 1 + x^2 t，绕 1 的跳跃数值为 0；
              (c) 把 nu 换成「二阶极点主部系数」的朴素猜测 2 pi i z x^2 e^z，与数值跳跃不符；(d) 右端换成二阶极点但留数为零的
              gamma + t/(1-t)，绕 1 的跳跃数值为 0（障碍是留数，不是二阶极点本身）
"""
import cmath
import math
import os
import sys
from fractions import Fraction as Fr
from math import factorial

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_table  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []
EULER_GAMMA = 0.57721566490153286060651209008240243


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


# ---------------------------------------------------------------------------
# 精确部分：固定有理 x，t 的截断幂级数（列表，下标 = t 的幂次）
# ---------------------------------------------------------------------------
XS = [Fr(3, 5), Fr(2, 5), Fr(2, 7), Fr(7, 10), Fr(9, 10), Fr(3, 4), Fr(5, 6), Fr(11, 13),
      Fr(2), Fr(5, 4), Fr(-1), Fr(-3, 2), Fr(-2, 3)]


def lam_of(x):
    return (1 - x) / x ** 3


def check_x_ok(x, N):
    lam = lam_of(x)
    return x != 0 and not (lam.denominator == 1 and 0 <= lam.numerator <= N + 2)


def smul(a, b, N):
    r = [Fr(0)] * (N + 1)
    for i, u in enumerate(a[:N + 1]):
        if u:
            for j in range(0, N + 1 - i):
                if j < len(b) and b[j]:
                    r[i + j] += u * b[j]
    return r


def Lop(x, Y, N):
    """L[Y]_m = b_m Y_m - Y_{m-1}（Y 的 t^m 系数 Y_m）。"""
    out = []
    for m in range(N + 1):
        bm = 1 - x - m * x ** 3
        out.append(bm * Y[m] - (Y[m - 1] if m >= 1 else 0))
    return out


def pieces(x, N):
    """返回 dict：G（T1.3(1) 闭式）、Grec（递推）、M、geo=1/(1-t)、e、K、Xi、z。"""
    lam = lam_of(x)
    z = 1 / x ** 3
    b = [1 - x - i * x ** 3 for i in range(N + 2)]
    G = []
    for m in range(N + 1):
        P = Fr(1)
        for i in range(m + 1):
            P *= b[i]
        s = 1 / P
        for j in range(1, m + 1):
            q = Fr(1)
            for i in range(j, m + 1):
                q *= b[i]
            s += x ** 2 * j / q
        G.append(s)
    Grec = [1 / b[0]]
    for m in range(1, N + 1):
        Grec.append((Grec[-1] + m * x ** 2) / b[m])
    Mc, P = [], Fr(1)
    for m in range(N + 1):
        P *= b[m]
        Mc.append(1 / P)
    e, acc = [], Fr(0)
    for n in range(N + 1):
        acc += z ** n / factorial(n)
        e.append(acc)
    K = [e[n] / (n + 1 - lam) for n in range(N + 1)]
    expm = [(-z) ** j / factorial(j) for j in range(N + 1)]       # e^{-zt}
    tK = [Fr(0)] + K[:N]                                           # t K(t)
    Xi = smul(expm, tK, N)
    return dict(G=G, Grec=Grec, M=Mc, geo=[Fr(1)] * (N + 1), e=e, K=K, Xi=Xi, z=z, lam=lam,
                expp=[z ** j / factorial(j) for j in range(N + 1)])


def check_struct_ode_phi1():
    N = 40
    ok_s, ok_rec, ok_ode, ok_phi = True, True, True, True
    detail = []
    for x in XS:
        assert check_x_ok(x, N), x
        d = pieces(x, N)
        z, lam = d['z'], d['lam']
        rhs = [(d['M'][m] - d['geo'][m]) / x + z * d['Xi'][m] for m in range(N + 1)]
        if rhs != d['G']:
            ok_s = False
            detail.append('struct x=%s' % x)
        if d['Grec'] != d['G']:
            ok_rec = False
        gam = [Fr(1)] + [x ** 2 * m for m in range(1, N + 1)]
        tgeo = [Fr(0)] + [Fr(1)] * N                                 # t/(1-t)
        LM = Lop(x, d['M'], N)
        A = [(d['M'][m] - d['geo'][m]) / x for m in range(N + 1)]
        LA = Lop(x, A, N)
        LXi = Lop(x, d['Xi'], N)
        conds = [
            LM == [Fr(1)] + [Fr(0)] * N,
            LA == [gam[m] + tgeo[m] for m in range(N + 1)],
            LXi == [-x ** 3 * tgeo[m] for m in range(N + 1)],
            all((n + 1 - lam) * d['K'][n] == d['e'][n] for n in range(N + 1)),
            smul(d['expp'], d['geo'], N) == d['e'],                   # e^{zt}/(1-t) = sum e_n t^n
            z - lam == 1 / x ** 2,
            [LA[m] + z * LXi[m] for m in range(N + 1)] == gam,
        ]
        if not all(conds):
            ok_ode = False
            detail.append('ode x=%s %s' % (x, conds))
        # Phi_1(1-lam,1;2-lam;t,zt) 的 t^N 系数 = sum_{m+n=N} (1-lam)_{m+n}(1)_m/((2-lam)_{m+n} m! n!) z^n
        Nphi = 30
        for NN in range(Nphi + 1):
            poch_a, poch_c = Fr(1), Fr(1)
            for i in range(NN):
                poch_a *= (1 - lam + i)
                poch_c *= (2 - lam + i)
            s = Fr(0)
            for n in range(NN + 1):
                mm = NN - n
                poch1 = Fr(factorial(mm))                              # (1)_m = m!
                s += poch_a * poch1 / (poch_c * factorial(mm) * factorial(n)) * z ** n
            if s != (1 - lam) * d['K'][NN]:
                ok_phi = False
                detail.append('phi1 x=%s N=%d' % (x, NN))
                break
    report('b6-struct', ok_s and ok_rec, '命题 1：F = (M-1/(1-t))/x + z Xi 在 %d 个有理 x 上逐系数精确成立（m<=%d）；'
           'T1.3(1) 闭式与递推的 G_m 相同 %s' % (len(XS), N, '; '.join(detail[:3])))
    report('b6-ode', ok_ode, '算子恒等式 L[M]=1、L[(M-1/(1-t))/x]=gamma+t/(1-t)、L[Xi]=-x^3 t/(1-t)、(n+1-lam)K_n=e_n、'
           'sum e_n t^n = e^{zt}/(1-t)、z-lam=x^-2，%d 个 x，t^%d 以内精确' % (len(XS), N))
    report('b6-phi1', ok_phi, 'Xi = t e^{-zt} Phi_1(1-lam,1;2-lam;t,zt)/(1-lam)：Phi_1 的 Pochhammer 二重和逐系数相同（N<=30，%d 个 x）'
           % len(XS))


def check_reverse_struct():
    """反向检查 (a)：Xi 里把 e_n 换成 e_{n+1}，命题 1 应当失败。"""
    N = 12
    fails = 0
    for x in XS[:5]:
        d = pieces(x, N + 1)
        z, lam = d['z'], d['lam']
        K2 = [d['e'][n + 1] / (n + 1 - lam) for n in range(N + 1)]
        expm = [(-z) ** j / factorial(j) for j in range(N + 1)]
        Xi2 = smul(expm, [Fr(0)] + K2[:N], N)
        rhs = [(d['M'][m] - 1) / x + z * Xi2[m] for m in range(N + 1)]
        if rhs != d['G'][:N + 1]:
            fails += 1
    return fails == 5


# ---------------------------------------------------------------------------
# 对照原始定义：按 x 的 Laurent 展开
# ---------------------------------------------------------------------------
def inv_b_series(i, n):
    a = [Fr(0)] * (n + 1)
    a[0] = Fr(1)
    for k in range(1, n + 1):
        s = a[k - 1]
        if k >= 3:
            s += i * a[k - 3]
        a[k] = s
    return a


def laurent_t_coeff(m, Kmax):
    """[t^m] 右边 的 Laurent 展开（字典：x 的幂次 -> 系数），两部分分开返回。"""
    n = Kmax + 3 * m + 10
    partA = {}
    P = [Fr(1)] + [Fr(0)] * n
    for i in range(m + 1):
        ib = inv_b_series(i, n)
        newP = [Fr(0)] * (n + 1)
        for a_ in range(n + 1):
            if P[a_]:
                for b_ in range(n + 1 - a_):
                    newP[a_ + b_] += P[a_] * ib[b_]
        P = newP
    P[0] -= 1
    for e_ in range(1, n + 1):
        if P[e_]:
            partA[e_ - 1] = partA.get(e_ - 1, 0) + P[e_]
    # z Xi 的 t^m 系数：sum_{j=0}^{m-1} (-1)^{j+1} x^{-3j}/j! * e_{m-1-j} / b_{m-j}，e_n = sum_{k<=n} x^{-3k}/k!
    partB = {}
    for j in range(0, m):
        nn = m - 1 - j
        ib = inv_b_series(m - j, n)
        for k in range(nn + 1):
            coef = Fr((-1) ** (j + 1), factorial(j) * factorial(k))
            shift = -3 * j - 3 * k
            for r in range(n + 1):
                if ib[r]:
                    e_ = shift + r
                    partB[e_] = partB.get(e_, 0) + coef * ib[r]
    return partA, partB


def check_dp():
    Kmax, Mmax = 40, 12
    T = U_fast_table(Kmax, Mmax)
    ok, integral = True, True
    bad = []
    for m in range(Mmax + 1):
        A, B = laurent_t_coeff(m, Kmax)
        tot = dict(A)
        for e_, v in B.items():
            tot[e_] = tot.get(e_, 0) + v
        if any(v != 0 for e_, v in tot.items() if e_ < 0):
            ok = False
            bad.append('neg m=%d' % m)
        if not all(tot.get(k, 0) == T[k][m] for k in range(Kmax + 1)):
            ok = False
            bad.append('dp m=%d' % m)
        if any(v != 0 for e_, v in B.items() if e_ < 0):
            ok = False
            bad.append('negB m=%d' % m)
        if not all(Fr(B.get(k, 0)).denominator == 1 for k in range(Kmax + 1)):
            integral = False
    report('b6-dp', ok and integral, '命题 1 右边按 x 展开：负幂全部相消，x^k t^m 系数 = 原始定义的 U_k(m)（k<=%d, m<=%d）；'
           'z Xi 的系数都是整数 %s' % (Kmax, Mmax, ' '.join(bad[:4])))


# ---------------------------------------------------------------------------
# 数值部分：RK4 沿圆周积分 ODE  F' = (lam/t - z)F - z*rhs(t)/t
# ---------------------------------------------------------------------------
def G_float(x, N, rhs_kind='gamma'):
    """f_x 的 t-系数（浮点/复数）：b_m G_m = G_{m-1} + r_m，r 为右端的 t^m 系数。"""
    def r(m):
        if rhs_kind == 'gamma':
            return (1 if m == 0 else 0) + (x * x * m if m >= 1 else 0)
        if rhs_kind == 'nopole':          # 1 + x^2 t
            return (1 if m == 0 else 0) + (x * x if m == 1 else 0)
        if rhs_kind == 'zerores':         # gamma + t/(1-t)
            return (1 if m == 0 else 0) + (x * x * m + 1 if m >= 1 else 0)
        raise ValueError(rhs_kind)
    G = []
    prev = 0
    for m in range(N + 1):
        bm = 1 - x - m * x ** 3
        g = (prev + r(m)) / bm
        G.append(g)
        prev = g
    return G


def f_series(x, t, N=400, rhs_kind='gamma'):
    s, p = 0, 1
    for g in G_float(x, N, rhs_kind):
        s += g * p
        p *= t
    return s


def rhs_fun(rhs_kind, x, t):
    if rhs_kind == 'gamma':
        return 1 + x * x * t / (1 - t) ** 2
    if rhs_kind == 'nopole':
        return 1 + x * x * t
    if rhs_kind == 'zerores':
        return 1 + x * x * t / (1 - t) ** 2 + t / (1 - t)
    raise ValueError(rhs_kind)


def ode(x, t, F, rhs_kind):
    lam = (1 - x) / x ** 3
    z = 1 / x ** 3
    return (lam / t - z) * F - z * rhs_fun(rhs_kind, x, t) / t


def loop(kind, t0):
    if kind == 0:     # 绕 0：t = t0 e^{2 pi i s}
        def p(s):
            w = cmath.exp(2j * math.pi * s)
            return t0 * w, t0 * 2j * math.pi * w
    else:             # 绕 1：t = 1 + (1-t0) e^{i(pi + 2 pi s)}
        r = 1 - t0

        def p(s):
            w = cmath.exp(1j * (math.pi + 2 * math.pi * s))
            return 1 + r * w, r * 2j * math.pi * w
    return p


def integrate(x, kinds, F0, t0, rhs_kind='gamma', steps=20000):
    F = F0
    h = 1.0 / steps
    for kind in kinds:
        path = loop(kind, t0)

        def g(s, Fv):
            t, dt = path(s)
            return ode(x, t, Fv, rhs_kind) * dt
        for k in range(steps):
            s = k * h
            k1 = g(s, F)
            k2 = g(s + h / 2, F + h / 2 * k1)
            k3 = g(s + h / 2, F + h / 2 * k2)
            k4 = g(s + h, F + h * k3)
            F = F + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    return F


def predicted(x, t0):
    lam = (1 - x) / x ** 3
    z = 1 / x ** 3
    omega = cmath.exp(lam * math.log(t0) - z * t0)
    nu = 2j * math.pi * z * cmath.exp(z)
    e = cmath.exp(2j * math.pi * lam)
    return omega, nu, e


def check_mono():
    t0 = 0.5
    xs = [0.6, 0.7, 2.0, -1.5, 0.6 + 0.2j]
    ok = True
    lines = []
    for x in xs:
        F0 = f_series(x, t0)
        omega, nu, e = predicted(x, t0)
        a = integrate(x, [0], F0, t0)
        b = integrate(x, [1], F0, t0)
        ab = integrate(x, [0, 1], F0, t0)
        ba = integrate(x, [1, 0], F0, t0)
        scale = abs(nu * omega)
        e0 = abs(a - F0) / scale
        e1 = abs((b - F0) - (-nu * omega)) / scale
        comm_pred = -nu * (1 - e) * omega
        e2 = abs((ab - ba) - comm_pred) / scale
        nonzero = abs(comm_pred) / scale > 1e-3
        good = e0 < 1e-8 and e1 < 1e-8 and e2 < 1e-8 and nonzero
        ok &= good
        lines.append('x=%s: |jump1|=%.4g, |comm|=%.4g, rel.err %.1e/%.1e/%.1e' %
                     (x, abs(b - F0), abs(ab - ba), e0, e1, e2))
    report('b6-mono', ok, '（数值）绕 0 不变、绕 1 跳 -nu*omega、交换子 = -nu(1-e^{2pi i lam})omega ≠ 0：' + '; '.join(lines))
    return ok


def Ei_pos(w):
    """Ei(w)，w>0（主值）：gamma + ln w + sum_{k>=1} w^k/(k k!)。"""
    s, term, k = 0.0, 1.0, 0
    while True:
        k += 1
        term *= w / k
        add = term / k
        s += add
        if abs(add) < 1e-18 * max(1.0, abs(s)) and k > w:
            break
    return EULER_GAMMA + math.log(w) + s


def newton_root(f, df, x0):
    x = x0
    for _ in range(100):
        dx = f(x) / df(x)
        x -= dx
        if abs(dx) < 1e-16:
            break
    return x


def closed_form_negint(n, x, t):
    """lam = -n 时的 Ei 闭式。"""
    z = 1 / x ** 3
    # M(t) = sum t^m/P_m
    Msum, P, p, m = 0.0, 1.0, 1.0, 0
    while True:
        P *= (1 - x - m * x ** 3)
        term = p / P
        Msum += term
        m += 1
        p *= t
        if m > 30 and abs(term) < 1e-19:
            break
    # I_k(t) = int_0^t s^k e^{zs} ds = sum_j z^j t^{j+k+1}/(j!(j+k+1))
    Isum = 0.0
    for k in range(n):
        s, j, zt = 0.0, 0, 1.0
        while True:
            term = zt * t ** (k + 1) / (factorial(j) * (j + k + 1))
            s += term
            j += 1
            zt *= z * t
            if j > 10 and abs(term) < 1e-20:
                break
        Isum += s
    J = -Isum - math.exp(z) * (Ei_pos(-z * (1 - t)) - Ei_pos(-z))
    return (Msum - 1 / (1 - t)) / x + z * t ** (-n) * math.exp(-z * t) * J


def check_sharp():
    ok = True
    lines = []
    for n in (1, 2, 3):
        if n == 2:
            x = -1.0
        else:
            x = newton_root(lambda u: n * u ** 3 - u + 1, lambda u: 3 * n * u ** 2 - 1, -1.2 if n == 1 else -0.85)
        lam = (1 - x) / x ** 3
        worst = 0.0
        for t in (-0.9, -0.5, 0.3, 0.7, 0.9):
            a = f_series(x, t, N=2000)
            b = closed_form_negint(n, x, t)
            worst = max(worst, abs(a - b) / max(1.0, abs(a)))
        good = abs(lam + n) < 1e-12 and worst < 1e-11
        ok &= good
        lines.append('n=%d x=%.12f lam+n=%.3e rel.err=%.1e' % (n, x, lam + n, worst))
    # x=-1：交换子数值为 0，但绕 1 的跳跃非零
    t0 = 0.5
    x = -1.0
    F0 = f_series(x, t0)
    omega, nu, e = predicted(x, t0)
    b = integrate(x, [1], F0, t0)
    ab = integrate(x, [0, 1], F0, t0)
    ba = integrate(x, [1, 0], F0, t0)
    scale = abs(nu * omega)
    c_ok = abs(ab - ba) / scale < 1e-9 and abs((b - F0) + nu * omega) / scale < 1e-8 and abs(b - F0) > 1
    ok &= c_ok
    lines.append('x=-1: |comm|/|nu omega|=%.1e, jump1=%s' % (abs(ab - ba) / scale, b - F0))
    report('b6-sharp', ok, 'lam=-n 的 Ei 闭式与级数一致；x=-1 时交换子为 0、绕 1 跳跃非零：' + '; '.join(lines))


def check_qrat():
    x = newton_root(lambda u: u ** 3 + 2 * u - 2, lambda u: 3 * u ** 2 + 2, 0.77)
    lam = (1 - x) / x ** 3
    t0 = 0.5
    F0 = f_series(x, t0)
    omega, nu, e = predicted(x, t0)
    scale = abs(nu * omega)
    c1 = integrate(x, [0, 1], F0, t0) - integrate(x, [1, 0], F0, t0)
    c2 = integrate(x, [0, 0, 1], F0, t0) - integrate(x, [1, 0, 0], F0, t0)
    ok = abs(lam - 0.5) < 1e-14 and abs(c1) / scale > 0.5 and abs(c2) / scale < 1e-8 \
        and abs(c1 - (-nu * 2 * omega)) / scale < 1e-8          # 1 - e^{i pi} = 2
    report('b6-qrat', ok, 'lam=1/2（x=%.12f）：|[gamma_0,gamma_1] 的差|/|nu omega|=%.3f（预测 2），'
           '|[gamma_0^2,gamma_1] 的差|/|nu omega|=%.1e' % (x, abs(c1) / scale, abs(c2) / scale))


def check_reverse():
    ok_a = check_reverse_struct()
    t0 = 0.5
    x = 0.6
    omega, nu, e = predicted(x, t0)
    scale = abs(nu * omega)
    # (b) 无极点右端
    F0 = f_series(x, t0, rhs_kind='nopole')
    jb = integrate(x, [1], F0, t0, rhs_kind='nopole') - F0
    ok_b = abs(jb) / scale < 1e-9
    # (c) 朴素常数
    F0 = f_series(x, t0)
    j = integrate(x, [1], F0, t0) - F0
    z = 1 / x ** 3
    naive = -(2j * math.pi * z * x * x * cmath.exp(z)) * omega
    ok_c = abs(j - naive) / scale > 0.1 and abs(j + nu * omega) / scale < 1e-8
    # (d) 二阶极点、零留数
    F0 = f_series(x, t0, rhs_kind='zerores')
    jd = integrate(x, [1], F0, t0, rhs_kind='zerores') - F0
    ok_d = abs(jd) / scale < 1e-9
    report('b6-reverse', ok_a and ok_b and ok_c and ok_d,
           '(a) e_n->e_{n+1} 后命题 1 在 5 个 x 上都失败：%s；(b) 无极点右端的绕 1 跳跃 %.1e；(c) 朴素常数与数值跳跃不符：%s；'
           '(d) 零留数右端 gamma+t/(1-t) 的绕 1 跳跃 %.1e（与 L[(M-1/(1-t))/x]=gamma+t/(1-t) 一致：解是单值的）'
           % (ok_a, abs(jb) / scale, ok_c, abs(jd) / scale))


def main():
    check_struct_ode_phi1()
    check_dp()
    check_mono()
    check_sharp()
    check_qrat()
    check_reverse()
    n_pass = sum(RESULTS)
    n_fail = len(RESULTS) - n_pass
    print('SUMMARY b6 pass=%d fail=%d' % (n_pass, n_fail))
    return 0 if n_fail == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
