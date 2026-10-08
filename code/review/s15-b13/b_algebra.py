# -*- coding: utf-8 -*-
"""s15-b13 / B：notes/17 引理 1.1、1.2、1.4、1.5 与引理 1.3(b) 用到的小不等式的独立核对（不导入项目代码）。

  b-l11      引理 1.1：H=g/(1-x+u)（g=1-x²u/(1+u)²）与部分分式 (2-x)/((1-x)p)-(1-x)/q-x/q² 在 Q(x,u) 中恒等
             （符号：通分后分子是 Z[x,u] 中的零多项式；作者只在随机有理点上核对）
  b-l15sym   引理 1.5 作者的式子（a_1=0，-a_2 w'(p_*)/x³=1）作为 Q(x) 中的恒等式（符号）
  b-l15sig   引理 1.5 的另一种证明：H dw=g dσ 是同一个 1-形式，留数与坐标无关。在 σ 平面极点 σ_p=c_l 处，
             g=1+x²e^s/(1-e^s)²（s=σ-σ_p），e^s/(1-e^s)²=1/s²+0/s+…（精确级数），ψ'(σ_p)=-x，
             所以 Res g=0、Res e^{-ψ/x³}g=e^{-p_l/x³}（与作者在 p 平面的计算互相独立）
  b-l12      引理 1.2：G(p)=(1-p)e^p=e^{(w-w_l(x))/(1-x)}（模 2πi 比较对数）、临界值 ψ(σ_c)=w_l(x)、极点值 ψ(σ_p)=p_l(x)、
             (1-x)L(p_*)=-ε(x)（精确级数 + 随机复数点）；以及引理 1.3(a) 用到的 We^W=Z、Z=-1/e ⇔ p=0
  b-l14      引理 1.4：ε 的级数、|ε(x)|<=0.62|x|²（|x|<=1/2，最大模原理：系数全正，最大在 x=1/2，值 2-2ln2）、
             |w_l°|²=(1+τ+lnτ)²+π²(2l+1)²、动点界（随机）
  b-l13b     引理 1.3(b) 的三个小不等式：|E(p)|<=|p|²（|p|<=1；E(p)/p² 系数全正，|p|=1 上最大值在 p=1，为 1）；
             |G(p)/G(p_*)-1|<=2|p-p_*|（|p_*|<=1/3，|p-p_*|<=1/4，取样）；m(ρ)>0（取样）
  b-rev      反向检查：部分分式系数 2-x 改成 2、ψ'(σ_p) 的符号取反、ε 的符号取反，都应被抓到
用法：py -3.14 code/review/s15-b13/b_algebra.py
"""
import cmath
import math
import random
import sys
from fractions import Fraction as Fr

from s15_common import Reporter, setup_stdout

setup_stdout()


# ------------------------------------------------------------------ 多元多项式（dict: 指数元组 -> Fraction）
def P(d):
    return {k: Fr(v) for k, v in d.items() if v != 0}


def padd(a, b, cb=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + cb * v
    return {k: v for k, v in out.items() if v != 0}


def pmul(a, b):
    out = {}
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            k = tuple(i + j for i, j in zip(k1, k2))
            out[k] = out.get(k, 0) + v1 * v2
    return {k: v for k, v in out.items() if v != 0}


def ppow(a, n, one):
    out = one
    for _ in range(n):
        out = pmul(out, a)
    return out


class RF:
    """有理函数 num/den（多项式 dict），只做加减乘除，不约分；判零看分子。"""

    def __init__(self, num, den):
        self.n, self.d = num, den

    def __add__(self, o):
        return RF(padd(pmul(self.n, o.d), pmul(o.n, self.d)), pmul(self.d, o.d))

    def __sub__(self, o):
        return RF(padd(pmul(self.n, o.d), pmul(o.n, self.d), -1), pmul(self.d, o.d))

    def __mul__(self, o):
        return RF(pmul(self.n, o.n), pmul(self.d, o.d))

    def __truediv__(self, o):
        return RF(pmul(self.n, o.d), pmul(self.d, o.n))

    def is_zero(self):
        return not self.n


# 变量 (x,u)
ONE2 = P({(0, 0): 1})
X2 = P({(1, 0): 1})
U2 = P({(0, 1): 1})


def rf2(poly):
    return RF(poly, ONE2)


def lemma11(coef_pf=None):
    x, u, one = rf2(X2), rf2(U2), rf2(ONE2)
    two = rf2(P({(0, 0): 2}))
    q = one + u
    omx = one - x
    p = one + u / omx
    g = one - x * x * u / (q * q)
    H_def = g / (one - x + u)
    c = (two - x) if coef_pf is None else coef_pf
    H_pf = c / (omx * p) - omx / q - x / (q * q)
    return (H_def - H_pf).is_zero()


# 单变量 x
ONE1 = P({(0,): 1})
X1 = P({(1,): 1})


def rf1(poly):
    return RF(poly, ONE1)


def lemma15_author():
    x, one = rf1(X1), rf1(ONE1)
    omx = one - x
    ps = (rf1(P({(0,): 0})) - x) / omx                 # p_* = -x/(1-x)
    one_m_ps = one - ps
    a1 = omx * ps / one_m_ps + (x / omx) / (one_m_ps * one_m_ps)
    a2 = (x / omx) * ps / one_m_ps
    wprime = (rf1(P({(0,): 0})) - omx) * ps / one_m_ps   # w'(p_*) = -(1-x)p_*/(1-p_*)
    x3 = x * x * x
    lhs = (rf1(P({(0,): 0})) - a2) * wprime / x3       # -a_2 w'(p_*)/x³
    return a1.is_zero(), (lhs - one).is_zero(), (wprime - x * omx).is_zero()


# ------------------------------------------------------------------ 一元精确幂级数（Fraction 列表）
def smul(a, b, N):
    out = [Fr(0)] * (N + 1)
    for i, x in enumerate(a[:N + 1]):
        if x:
            for j, y in enumerate(b[:N + 1 - i]):
                out[i + j] += x * y
    return out


def sinv(a, N):
    out = [Fr(0)] * (N + 1)
    out[0] = 1 / a[0]
    for n in range(1, N + 1):
        out[n] = -sum(a[k] * out[n - k] for k in range(1, n + 1)) / a[0]
    return out


def exp_series(N):
    out, f = [], Fr(1)
    for n in range(N + 1):
        out.append(f)
        f /= (n + 1)
    return out


def main():
    rep = Reporter('s15_b_algebra')
    random.seed(15013)

    # ---- b-l11
    ok11 = lemma11()
    rep.check('b-l11', ok11, '引理 1.1 在 Q(x,u) 中恒等（通分后分子为零多项式）%s' % ok11)

    # ---- b-l15sym
    z1, z2, z3 = lemma15_author()
    rep.check('b-l15sym', z1 and z2 and z3, '引理 1.5 作者的式子在 Q(x) 中恒等：a_1≡0 %s；-a_2w\'(p_*)/x³≡1 %s；w\'(p_*)≡x(1-x) %s' % (z1, z2, z3))

    # ---- b-l15sig：σ 平面的独立推导
    N = 8
    e = exp_series(N + 3)
    A = [e[n + 1] for n in range(N + 1)]            # A(s)=(e^s-1)/s
    A2 = smul(A, A, N)
    F = smul(e, sinv(A2, N), N)                     # e^s/A(s)^2；e^s/(1-e^s)^2 = F(s)/s^2
    no_simple = F[1] == 0
    laurent_ok = F[0] == 1 and F[2] == Fr(-1, 12)
    # 数值：τe^{σ_p}=-1，ψ'(σ_p)=-x，Res_σ[e^{-ψ/x³}g] = x²·(-ψ'(σ_p)/x³)·e^{-p_l/x³} = e^{-p_l/x³}
    worst = 0.0
    for _ in range(500):
        tau = math.exp(random.uniform(-4, 4))
        l = random.randint(-6, 6)
        x = complex(random.uniform(-.3, .3), random.uniform(-.3, .3))
        sp = math.log(1 / tau) + 1j * math.pi * (2 * l + 1)
        u = tau * cmath.exp(sp)
        dpsi = 1 - x + u
        res_ratio = x * x * (-dpsi / x ** 3)
        worst = max(worst, abs(u + 1), abs(dpsi + x), abs(res_ratio - 1))
    # 数值：在 σ 平面绕 σ_p 的小圆上直接积分（与 p 平面的作者计算独立）
    worst_c = 0.0
    for (x, tau, l) in [(0.07 + 0.02j, 1.0, 0), (0.05 * cmath.exp(2.5j), 3.0, 1), (-0.04 + 0.06j, 0.2, -1), (0.1j, 10.0, 2)]:
        sp = math.log(1 / tau) + 1j * math.pi * (2 * l + 1)
        pl = (1 - x) * sp + tau * (cmath.exp(sp) - 1)
        M, r = 2000, 0.3 * abs(x) ** 1.5
        s1 = s2 = 0
        for k in range(M):
            th = 2 * math.pi * (k + .5) / M
            sg = sp + r * cmath.exp(1j * th)
            ds = 1j * r * cmath.exp(1j * th) * 2 * math.pi / M
            uu = tau * cmath.exp(sg)
            g = 1 - x * x * uu / (1 + uu) ** 2
            psi = (1 - x) * sg + tau * (cmath.exp(sg) - 1)
            s1 += g * ds
            s2 += cmath.exp(-(psi - pl) / x ** 3) * g * ds
        worst_c = max(worst_c, abs(s1 / (2j * math.pi)) / abs(x) ** 2, abs(s2 / (2j * math.pi) - 1))
    ok15s = no_simple and laurent_ok and worst < 1e-12 and worst_c < 1e-9
    rep.check('b-l15sig', ok15s, 'σ 平面：e^s/(1-e^s)² 的 Laurent 展开 1/s²+0·s^{-1}-1/12+… %s；τe^{σ_p}=-1、ψ\'(σ_p)=-x、留数比=1 的最大误差 %.1e；'
              '小圆数值积分（4 组）Res g/|x|² 与 Res(e^{-(ψ-p_l)/x³}g)-1 最大 %.1e' % (no_simple and laurent_ok, worst, worst_c))

    # ---- b-l12
    NN = 12
    Lps = [Fr(0)] + [Fr(1, n) - 1 for n in range(1, NN + 1)]          # L(p_*)=Σ(1/n-1)x^n
    eps_over = [Fr(0)] + [1 - Fr(1, n) for n in range(1, NN + 1)]     # ε/(1-x)=Σ(1-1/n)x^n
    # 独立地由 ε=(1-x)ln(1-x)+x 的级数验证 eps_over：
    ln1mx = [Fr(0)] + [Fr(-1, n) for n in range(1, NN + 2)]
    eps = [Fr(0)] * (NN + 1)
    for n in range(NN + 1):
        eps[n] = ln1mx[n] - (ln1mx[n - 1] if n >= 1 else 0) + (1 if n == 1 else 0)
    geo = [Fr(1)] * (NN + 1)
    ok_ser = all(a + b == 0 for a, b in zip(Lps, eps_over)) and smul(eps, geo, NN) == eps_over
    worst = 0.0
    for _ in range(3000):
        tau = math.exp(random.uniform(-4, 4))
        l = random.randint(-5, 5)
        x = complex(random.uniform(-.3, .3), random.uniform(-.3, .3))
        cl = math.log(1 / tau) + 1j * math.pi * (2 * l + 1)
        w0c = cl - 1 - tau
        epsx = (1 - x) * cmath.log(1 - x) + x
        wl = w0c - x * cl + epsx
        pl = w0c - x * cl
        sc = cmath.log((1 - x) / tau) + 1j * math.pi * (2 * l + 1)
        e1 = abs((1 - x) * sc + tau * (cmath.exp(sc) - 1) - wl)
        e2 = abs((1 - x) * cl + tau * (cmath.exp(cl) - 1) - pl)
        sig = complex(random.uniform(-3, 3), random.uniform(-6, 6))
        u = tau * cmath.exp(sig)
        w = (1 - x) * sig + u - tau
        p = 1 + u / (1 - x)
        d = (cmath.log(1 - p) + p - (w - wl) / (1 - x)) / (2j * math.pi)
        e3 = abs(d - round(d.real))
        ps = -x / (1 - x)
        e4 = abs((1 - x) * (ps + cmath.log(1 - ps)) + epsx)
        # 引理 1.3(a)：W=p-1，We^W=Z=(τ/(1-x))e^{(w+τ)/(1-x)}
        W = p - 1
        logZ = cmath.log(tau / (1 - x)) + (w + tau) / (1 - x)
        d5 = (cmath.log(W) + W - logZ) / (2j * math.pi)          # We^W=Z（对数形式，模 2πi，避免溢出）
        e5 = abs(d5 - round(d5.real))
        e6 = 0.0
        if abs(p) < 4:                                           # Z+1/e=E(p)/e，E(p)=1-G(p)
            Z = cmath.exp(logZ)
            e6 = abs((Z + 1 / math.e) - (1 - (1 - p) * cmath.exp(p)) / math.e) / max(1.0, abs(Z))
        worst = max(worst, e1 / max(1, abs(wl)), e2 / max(1, abs(pl)), e3, e4, e5, e6)
    rep.check('b-l12', ok_ser and worst < 1e-11, '(1-x)L(p_*)=-ε(x) 作为精确幂级数（到 x^12）%s；临界值、极点值、G(p) 关系（模 2πi）、We^W=Z、Z+1/e=E(p)/e：'
              '3000 组随机 (x,τ,l,σ) 最大误差 %.1e' % (ok_ser, worst))

    # ---- b-l14
    eps_coef_ok = all(eps[n] == Fr(1, n * (n - 1)) for n in range(2, NN + 1)) and eps[0] == 0 and eps[1] == 0
    bound = 2 - 2 * math.log(2)                      # 4ε(1/2)
    ok_bound = bound < 0.62
    # 取样核对 |ε(x)|<=0.62|x|²（|x|<=1/2）
    smp = max(abs((1 - x) * cmath.log(1 - x) + x) / abs(x) ** 2
              for x in (0.5 * r * cmath.exp(2j * math.pi * k / 360) for r in (0.05, 0.2, 0.5, 0.8, 1.0) for k in range(360)))
    ok_wl = True
    for tau in (0.01, 0.2784645427610738, 1.0, 3.0, 100.0):
        R = abs(math.log(1 / tau) - 1 - tau + 1j * math.pi)
        for l in range(-3000, 3001):
            m = abs(math.log(1 / tau) - 1 - tau + 1j * math.pi * (2 * l + 1))
            ok_wl &= abs(m * m - ((1 + tau + math.log(tau)) ** 2 + math.pi ** 2 * (2 * l + 1) ** 2)) < 1e-6 * m * m
            ok_wl &= m >= max(R, math.pi * abs(2 * l + 1)) - 1e-9
            ok_wl &= (abs(m - R) < 1e-12) == (l in (0, -1))
    ok_mv = True
    for _ in range(5000):
        x = 0.5 * random.random() * cmath.exp(2j * math.pi * random.random())
        tau = math.exp(random.uniform(-6, 6))
        l = random.randint(-200, 200)
        cl = math.log(1 / tau) + 1j * math.pi * (2 * l + 1)
        epsx = (1 - x) * cmath.log(1 - x) + x
        b = abs(x) * (abs(math.log(tau)) + math.pi * abs(2 * l + 1) + 1)
        ok_mv &= abs(-x * cl + epsx) <= b and abs(-x * cl) <= b
    rep.check('b-l14', eps_coef_ok and ok_bound and smp <= 0.62 and ok_wl and ok_mv,
              'ε=Σ_{n>=2}x^n/(n(n-1)) %s；max_{|x|<=1/2}|ε|/|x|²=2-2ln2=%.4f（取样 %.4f）<0.62；|w_l°|² 公式、|w_l°|>=max(R,π|2l+1|)、等号恰在 l=0,-1（5 个 τ 含 W(1/e)，|l|<=3000）%s；动点界（5000 组）%s'
              % (eps_coef_ok, bound, smp, ok_wl, ok_mv))

    # ---- b-l13b
    worstE = 0.0
    for k in range(3600):
        pp = cmath.exp(2j * math.pi * k / 3600)
        Ep = 1 - (1 - pp) * cmath.exp(pp)
        worstE = max(worstE, abs(Ep) / abs(pp) ** 2)
    worstG = 0.0
    for _ in range(20000):
        ps = (1 / 3) * math.sqrt(random.random()) * cmath.exp(2j * math.pi * random.random())
        pp = ps + 0.25 * math.sqrt(random.random()) * cmath.exp(2j * math.pi * random.random())
        if pp == ps:
            continue
        G = (1 - pp) * cmath.exp(pp)
        Gs = (1 - ps) * cmath.exp(ps)
        worstG = max(worstG, abs(G / Gs - 1) / abs(pp - ps))
    # m(ρ)=min{|1-e^ξ|: dist(ξ,2πiZ)>=ρ}：在 |Re ξ|<=1、0<=Im ξ<=2π 上取样
    ms = []
    for rho in (0.05, 0.2, 0.8):
        best = 1e9
        for i in range(201):
            for j in range(401):
                xi = complex(-1 + 2 * i / 200, 2 * math.pi * j / 400)
                dist = min(abs(xi - 2j * math.pi * n) for n in (-1, 0, 1, 2))
                if dist >= rho:
                    best = min(best, abs(1 - cmath.exp(xi)))
        ms.append(best)
    ok13 = worstE <= 1 + 1e-12 and worstG <= 2 and all(v > 0.5 * r for v, r in zip(ms, (0.05, 0.2, 0.8)))
    rep.check('b-l13b', ok13, 'max_{|p|=1}|E(p)|/|p|²=%.6f（应 <=1）；|G(p)/G(p_*)-1|/|p-p_*| 取样最大 %.4f（应 <=2）；m(0.05),m(0.2),m(0.8) 取样 %.3f,%.3f,%.3f（>0）'
              % (worstE, worstG, ms[0], ms[1], ms[2]))

    # ---- b-rev
    r1 = not lemma11(coef_pf=rf2(P({(0, 0): 2})))
    # ψ'(σ_p) 的符号取反 → 留数比变成 -1
    x = 0.07 + 0.02j
    r2 = abs(x * x * (-(+x) / x ** 3) - 1) > 1
    # ε 的符号取反 → (1-x)L(p_*)=+ε 不成立
    r3 = not all(a - b == 0 for a, b in zip(Lps, eps_over) if a != 0)
    # 引理 1.1 的另一处改坏：x/q² 改成 x²/q²
    x2, u2, one2 = rf2(X2), rf2(U2), rf2(ONE2)
    q2 = one2 + u2
    bad = (one2 - x2 * x2 * u2 / (q2 * q2)) / (one2 - x2 + u2) - ((rf2(P({(0, 0): 2})) - x2) / (one2 - x2 + u2) - (one2 - x2) / q2 - x2 * x2 / (q2 * q2))
    r4 = not bad.is_zero()
    rep.check('b-rev', r1 and r2 and r3 and r4, '反向检查：2-x 改成 2 时恒等式失败 %s；ψ\'(σ_p) 取 +x 时留数比 ≠1 %s；ε 取反时级数恒等式失败 %s；x/q² 改成 x²/q² 时失败 %s'
              % (r1, r2, r3, r4))
    return rep.summary()


if __name__ == '__main__':
    sys.exit(main())
