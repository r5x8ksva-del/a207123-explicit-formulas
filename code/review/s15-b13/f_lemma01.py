# -*- coding: utf-8 -*-
"""s15-b13 / F（后续复核）：notes/17 新加的引理 0.1、改写的引理 1.6 与 §4 常数顺序的数值演示（不导入项目代码）。

a_k 一律用我自己的 Lagrange 闭式（a_lagrange_exact.LagrangeSym，λ=1/(1-t) 的多项式，精确），不用 (0.1) 本身。
  f-02       (0.2) 作为 Q[λ] 中的恒等式：a_k-λa_{k-1}-λ²(λ-1)a'_{k-3}=λγ_k（d/dt=λ²d/dλ），γ_0=1、γ_2=t/(1-t)²=λ(λ-1)，
             其余 γ_k=0，负下标的 a 为 0；k<=200，含 k<=2 的初值
  f-int      引理 0.1(iii) 的积分形式：t_1a_{k-3}(t_1)-t_0a_{k-3}(t_0)=∫_{t_0}^{t_1}[(1-s)a_k-a_{k-1}+a_{k-3}-γ_k]ds，
             3 个区间、0<=k<=40；a_j(s) 用 90 位 Decimal 求值（避免相消），复合 Gauss–Legendre 积分
  f-asym     引理 0.1(i) 的解析输入：直接数值积分 I(x,t)（σ=x³v 换元，复合 Gauss–Legendre）。
             (a) 渐近展开的定义：K<=6 时 (I-S_K)/x^K → a_K，|(I-S_K)/x^K-a_K|<=2(|a_{K+1}|x+|a_{K+2}|x²)+噪声（x=0.1,0.05,0.025）；
             (b) 120 项部分和与 I 相差 <1e-13|I|（x=0.05,0.1,0.15）；t=-1/3,-1,-3
  f-ode      c3a 命题 5.2 的方程 x³tI_t=(1-x-t)I-g_x(t)（I_t 在积分号下求导），残差 <1e-11
  f-l16      引理 1.6 的常数：r_*=1/4 时 v=√(-2L(p)) 在 |p|<=r_* 上 Re v'>0（凸域上单叶）；m_*=min_{|p|=r_*}|L|；
             |p|<=r_* 上 |L(p)|<=|p|²；|c|<m_*/3 时 L(p)=c 在 |p|<r_* 内恰有 2 个根（辐角原理，200 个 c）；|L-c|<π，
             所以 G(p)=e^c ⇔ L(p)=c
  f-c4       §4 常数顺序：δ_1→η=√(δ_1/(4(R+δ_1)))→(C3)→r_D∈((4/3)δ_1, min((R/2)sinη, m_*/4))，6 个 τ 上逐条核对
             (C1)(C2)(C3)、区间非空、D(w_0°,2r_D) 中 Λ 只有 w_0°
  f-d0       引理 2.1 证明新加的 d_0>0 所用的下界在 τ∈[1e-8,1e8] 上恒正
  f-rev      反向：γ_2 改成 t/(1-t)；a_5 乘 1.01；δ_1 取成 m_*/4（r_D 的区间变空）；η 加倍（(C3) 失败）——都应失败
用法：py -3.14 code/review/s15-b13/f_lemma01.py
"""
import cmath
import math
import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction as Fr

import numpy as np

from s15_common import Reporter, setup_stdout, padd, pscale, pmul, pshift, ptrim, pderiv, peval
from a_lagrange_exact import LagrangeSym

setup_stdout()
GLX, GLW = np.polynomial.legendre.leggauss(24)
W_E = 0.2784645427610738
getcontext().prec = 90


def I_num(x, t):
    """I(x,t)=∫_0^∞ exp(-[(1-x)v+τ·expm1(x³v)/x³])·g_x(t e^{x³v}) dv（σ=x³v），以及 I_t（积分号下求导）。"""
    tau = -t
    x3 = x ** 3
    Vmax = 64.0 / (1 - x + tau)
    edges = np.linspace(0.0, Vmax, 97)
    I = It = 0.0
    for lo, hi in zip(edges[:-1], edges[1:]):
        v = (hi - lo) / 2 * GLX + (hi + lo) / 2
        wts = (hi - lo) / 2 * GLW
        em1 = np.expm1(x3 * v)
        expo = -((1 - x) * v + tau * em1 / x3)
        z = t * (1 + em1)
        g = 1 + x * x * z / (1 - z) ** 2
        dg = x * x * (1 + z) * (1 + em1) / (1 - z) ** 3          # ∂_t g(t e^σ)=g'(z)e^σ
        base = np.exp(expo)
        I += np.sum(wts * base * g)
        It += np.sum(wts * base * (em1 / x3 * g + dg))           # ∂_t(-ψ/x³)=(e^σ-1)/x³
    return float(I), float(It)


def L_of(p):
    return p + np.log(1 - p)


def main():
    rep = Reporter('s15_f_lemma01')
    t0 = time.time()
    KS = 200
    LS = LagrangeSym(KS)
    A = {k: LS.kfact_a(k) for k in range(KS + 1)}      # A_k = k!·a_k(λ)，整系数
    AD = {k: [Decimal(c) for c in A[k]] for k in range(41)}

    def a_dec(j, s):
        """a_j(t=s)，s 为 float；90 位 Decimal Horner。"""
        if j < 0:
            return 0.0
        lam = Decimal(1) / (Decimal(1) - Decimal(s))
        v = Decimal(0)
        for c in reversed(AD[j]):
            v = v * lam + c
        return float(v / Decimal(math.factorial(j)))

    # ---- f-02
    def check02(lam_gamma2):
        bad = []
        for k in range(0, KS + 1):
            lhs = list(A[k])
            if k >= 1:
                lhs = padd(lhs, pscale(pshift(A[k - 1], 1), -k))
            if k >= 3:
                lhs = padd(lhs, pscale(pmul([0, 0, -1, 1], pderiv(A[k - 3])), -k * (k - 1) * (k - 2)))
            if k == 0:
                rhs = [0, 1]                       # 0!·λγ_0=λ
            elif k == 2:
                rhs = pscale(lam_gamma2, 2)        # 2!·λγ_2
            else:
                rhs = []
            if ptrim(lhs) != ptrim(rhs):
                bad.append(k)
        return bad
    bad02 = check02([0, 0, -1, 1])                 # λγ_2=λ·λ(λ-1)=λ³-λ²
    rep.check('f-02', not bad02, '(0.2) 在 Q[λ] 中逐个 k 精确成立（0<=k<=%d，含 γ_0=1、γ_2=t/(1-t)²、负下标为 0 的初值）；不符的 k：%s'
              % (KS, bad02[:5]))

    # ---- f-int
    t1 = time.time()
    worst = 0.0
    for (ta, tb) in [(-3.0, -1.0), (-1.0, -1.0 / 3), (-5.0, -0.2)]:
        segs = np.linspace(ta, tb, 9)
        nodes = []
        for lo, hi in zip(segs[:-1], segs[1:]):
            for xg, wg in zip(GLX, GLW):
                nodes.append(((hi - lo) / 2 * xg + (hi + lo) / 2, (hi - lo) / 2 * wg))
        vals = {s: [a_dec(j, s) for j in range(41)] for s, _ in nodes}
        for k in range(0, 41):
            get = lambda j, s: 0.0 if j < 0 else vals[s][j]
            gam = lambda s: 1.0 if k == 0 else (s / (1 - s) ** 2 if k == 2 else 0.0)
            lhs = tb * a_dec(k - 3, tb) - ta * a_dec(k - 3, ta)
            rhs = sum(w * ((1 - s) * get(k, s) - get(k - 1, s) + get(k - 3, s) - gam(s)) for s, w in nodes)
            worst = max(worst, abs(lhs - rhs) / max(1.0, abs(lhs), abs(rhs)))
    rep.check('f-int', worst < 1e-11, '引理 0.1(iii) 的积分恒等式（[t_0,t_1]=[-3,-1]、[-1,-1/3]、[-5,-0.2]，0<=k<=40）最大相对差 %.1e（%.1f s）'
              % (worst, time.time() - t1))

    # ---- f-asym
    t1 = time.time()
    ok_a, ok_b, lines = True, True, []
    for tt in (Fr(-1, 3), Fr(-1), Fr(-3)):
        lam = 1 / (1 - tt)
        a = [float(Fr(peval(A[k], lam)) / math.factorial(k)) for k in range(KS + 1)]
        # (a) 渐近展开的定义
        worst_ratio = 0.0
        for K in range(0, 7):
            errs = []
            for x in (0.1, 0.05, 0.025):
                I, _ = I_num(x, float(tt))
                S = sum(a[k] * x ** k for k in range(K))
                qK = (I - S) / x ** K
                bound = 2 * (abs(a[K + 1]) * x + abs(a[K + 2]) * x * x) + 1e-14 * abs(I) / x ** K
                errs.append(abs(qK - a[K]))
                ok_a &= abs(qK - a[K]) <= bound
                worst_ratio = max(worst_ratio, abs(qK - a[K]) / bound)
            ok_a &= errs[2] < errs[0]
        # (b) 高阶部分和
        floors = []
        for x in (0.05, 0.1, 0.15):
            I, _ = I_num(x, float(tt))
            S = sum(a[k] * x ** k for k in range(120))
            floors.append(abs(I - S) / abs(I))
            ok_b &= abs(I - S) < 1e-13 * abs(I)
        lines.append('t=%s：(a) 最大 误差/界=%.2f，(b) |I-S_120|/|I|=%s' % (tt, worst_ratio, '/'.join('%.0e' % f for f in floors)))
    rep.check('f-asym', ok_a and ok_b, 'I(x,t) 的数值积分以 Σa_kx^k 为渐近展开（a_k 来自 H 的 Taylor 系数，不经 (0.1)）：'
              + '；'.join(lines) + '（%.1f s）' % (time.time() - t1))

    # ---- f-ode
    worst = 0.0
    for tt in (-1.0 / 3, -1.0, -3.0):
        for x in (0.05, 0.1, 0.3, 0.6):
            I, It = I_num(x, tt)
            g = 1 + x * x * tt / (1 - tt) ** 2
            res = x ** 3 * tt * It - ((1 - x - tt) * I - g)
            worst = max(worst, abs(res) / max(1.0, abs(I)))
    rep.check('f-ode', worst < 1e-11, 'c3a 命题 5.2：x³tI_t-(1-x-t)I+g_x(t) 的最大残差 %.1e（3 个 t×4 个 x）' % worst)

    # ---- f-l16
    rstar = 0.25

    def v_of(p):
        return p * np.sqrt(-2 * L_of(p) / (p * p))
    rr = np.linspace(0.0, rstar, 60)[1:]
    th = np.linspace(0, 2 * np.pi, 361)[:-1]
    P = (rr[:, None] * np.exp(1j * th[None, :])).ravel()
    h = 1e-6
    dv = (v_of(P + h) - v_of(P - h)) / (2 * h)
    min_re_dv = float(np.min(dv.real))
    pc = rstar * np.exp(1j * np.linspace(0, 2 * np.pi, 7201)[:-1])
    mstar = float(np.min(np.abs(L_of(pc))))
    ratio_L = float(np.max(np.abs(L_of(P)) / np.abs(P) ** 2))
    rng = np.random.default_rng(15013)
    roots_ok = True
    for _ in range(200):
        c = (mstar / 3) * math.sqrt(rng.random()) * cmath.exp(2j * math.pi * rng.random())
        vals = L_of(pc) - c
        wind = np.sum(np.diff(np.unwrap(np.angle(np.append(vals, vals[0]))))) / (2 * np.pi)
        roots_ok &= abs(wind - 2) < 1e-6
    sep_ok = rstar ** 2 + mstar / 3 < math.pi
    ok16 = min_re_dv > 0 and ratio_L <= 1 and roots_ok and sep_ok and mstar / 3 < math.pi / 2
    rep.check('f-l16', ok16, 'r_*=1/4：min Re v\'=%.3f>0（凸域上单叶）；m_*=%.5f，m_*/3<π/2；max|L(p)|/|p|²=%.3f（<=1）；'
              '|c|<m_*/3 时辐角原理数出 2 个根（200 个 c）%s；|L-c|<r_*²+m_*/3<π %s'
              % (min_re_dv, mstar, ratio_L, roots_ok, sep_ok))

    # ---- f-c4
    def chain(tau, delta1=None, eta_mult=1.0):
        wl = lambda l: math.log(1 / tau) - 1 - tau + 1j * math.pi * (2 * l + 1)
        R = abs(wl(0))
        th0 = cmath.phase(wl(0))
        R2 = abs(wl(1))
        if delta1 is None:
            delta1 = min(3 * mstar / 32, (R2 - R) / 4, 9 * R / 512)
        R1 = R + delta1
        eta = eta_mult * math.sqrt(delta1 / (4 * (R + delta1)))
        c3 = R1 * math.cos(2 * eta) >= R + delta1 / 2 - 1e-15
        thp, thm = th0 + eta, th0 - eta
        args = [cmath.phase(wl(l)) for l in range(-2000, 2001)]
        c1 = 0 < thm and thp < math.pi and all(abs(a - thp) > 1e-12 and abs(a - thm) > 1e-12 for a in args) \
            and abs(thp - math.pi / 2) > 1e-12 and abs(thm - math.pi / 2) > 1e-12
        inside = sorted(l for l in range(-2000, 2001) if abs(wl(l)) <= R1)
        c2 = inside == [-1, 0] and not (thm <= cmath.phase(wl(-1)) <= thp)
        lo = 4 * delta1 / 3
        gapL = min(abs(wl(l) - wl(0)) for l in range(-50, 51) if l != 0)
        hi = min(R / 2 * math.sin(eta), mstar / 4, gapL / 2)
        nonempty = lo < hi
        rD = (lo + hi) / 2
        disc_ok = all(abs(wl(l) - wl(0)) >= 2 * rD for l in range(-50, 51) if l != 0)
        return dict(delta1=delta1, eta=eta, c3=c3, lo=lo, hi=hi, nonempty=nonempty,
                    ok=c1 and c2 and c3 and nonempty and disc_ok)
    rows, okc4 = [], True
    for tau in (0.01, 0.1, W_E, 1.0, 3.0, 100.0):
        d = chain(tau)
        okc4 &= d['ok']
        rows.append('τ=%.3g:δ1=%.1e,η=%.1e,r_D∈(%.1e,%.1e)%s' % (tau, d['delta1'], d['eta'], d['lo'], d['hi'], '' if d['ok'] else ' BAD'))
    rep.check('f-c4', okc4, '§4 常数顺序：' + '；'.join(rows) + '（(C1)(C2)(C3)、区间非空、D(w_0°,2r_D)∩Λ={w_0°} 都成立）')

    # ---- f-d0：引理 2.1 证明新加的 d_0:=inf_{|x|<=1/4}dist(0,S(x))>0，所用下界 |w_l°|-(|lnτ|+π|2l+1|+1)/4
    worst_d0, arg_d0 = 1e9, None
    for i in range(2001):
        tau = 10 ** (-8 + 16 * i / 2000)
        a0 = 1 + tau + math.log(tau)
        for l in range(-300, 301):
            m = math.hypot(a0, math.pi * (2 * l + 1)) - (abs(math.log(tau)) + math.pi * abs(2 * l + 1) + 1) / 4
            if m < worst_d0:
                worst_d0, arg_d0 = m, (tau, l)
    rep.check('f-d0', worst_d0 > 0, '引理 2.1 证明里的 d_0>0：|w_l°|-(|lnτ|+π|2l+1|+1)/4 在 τ∈[1e-8,1e8]（2001 个）、|l|<=300 上的最小值 %.3f'
              '（在 τ=%.3g、l=%d 取到；l 更大时下界只增不减）' % (worst_d0, arg_d0[0], arg_d0[1]))

    # ---- f-rev
    r1 = bool(check02([0, -1, 1]))             # γ_2 改成 t/(1-t)=λ-1，λγ_2=λ²-λ
    lam = Fr(2, 3)                             # t=-1/2
    a = [float(Fr(peval(A[k], lam)) / math.factorial(k)) for k in range(60)]
    a_bad = list(a)
    a_bad[5] *= 1.01
    x = 0.1
    I, _ = I_num(x, -0.5)
    S = sum(a_bad[k] * x ** k for k in range(60))
    r2 = abs(I - S) > 1e-3 * abs(a[5] * x ** 5)
    r3 = not chain(1.0, delta1=mstar / 4)['nonempty']
    r4 = not chain(1.0, eta_mult=2.0)['c3']
    rep.check('f-rev', r1 and r2 and r3 and r4, '反向：γ_2 改成 t/(1-t) 时 (0.2) 不成立 %s；a_5 乘 1.01 时 |I-S| 远大于噪声 %s；'
              'δ_1=m_*/4 时 r_D 的区间为空 %s；η 加倍时 (C3) 失败 %s' % (r1, r2, r3, r4))
    print('（总用时 %.1f s）' % (time.time() - t0))
    return rep.summary()


if __name__ == '__main__':
    sys.exit(main())
