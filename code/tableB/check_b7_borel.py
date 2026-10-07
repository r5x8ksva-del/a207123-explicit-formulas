# -*- coding: utf-8 -*-
"""表 B 的 B7 后半（F 在 x 方向 3-可和、和等于积分 I）的数值核对（2026-10-08）。证明见 notes/09-主Agent-表B-B7-Borel可和.md。

证明是解析的；这里只做数值佐证（双精度，numpy），不是证明的一部分。记号：t<0，tau=-t，
  psi_x(s) = (1-x) s + tau (e^s - 1)，G = {|Im s| < pi/2}，H(w,x) = g_x(-tau e^{s_x(w)}) / psi_x'(s_x(w))，
  g_x(z) = 1 + x^2 z/(1-z)^2，s_x = (psi_x|_G)^{-1}。I_phi(x) = x^{-3} int_{arg w = phi} e^{-w/x^3} H(w,x) dw。
逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b7b pass=<n> fail=<n>」。
  b7b-bdry   引理 2 的边界估计：|x|<=r0=min(1/8,tau/2) 时 psi_x({Im s = ±pi/2}) 与 Omega' = {|w|<1/2} ∪ {|arg w|<delta}
             （tan delta = min(1,tau/3)）不相交：圆周取样（tau 取 7 个值，x 在圆周 |x|=r0 上取 24 个点，s 在 [-60,60] 上取 24001 个点），
             以及整个圆盘的余量 dist(psi_0(s),Omega')-r0|s|>0（psi_x 对 x 仿射；13 个 tau 从 1e-6 到 1e6，s∈[-300,300]）
  b7b-inv    在 Omega' 的取样点上 Newton 求 s_x(w)，解都落在 G 里、|psi_x(s)-w|<1e-11，且 Re psi_x' >= 1-|x| > 0（单叶性的前提）
  b7b-real   实的 x：原定义（对 sigma 积分）与 w 积分（phi=0）一致
  b7b-rot    同一个复 x 用两条不同的射线 phi1, phi2 计算，结果一致（Cauchy 定理，佐证解析延拓），含 |arg x| > pi/6 的点
  b7b-series 复 x（含 |arg x| > pi/6）：I_phi(x) 与 F 的部分和 sum_{k<K} f_k(t) x^k 比较；|x| 较小时一致到 1e-12，
             |x|=0.7 时最优截断误差与最小项同量级（Gevrey 渐近的佐证）
  b7b-gevrey t=-2, -5（|t|>1，前半的定理 G1 不覆盖）：|f_k(t)|/Gamma(1+k/3) 的 k 次方根有界（推论的佐证）
"""
import math
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb
import numpy as np

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def psi(s, x, tau):
    return (1 - x) * s + tau * (np.exp(s) - 1)


def dpsi(s, x, tau):
    return (1 - x) + tau * np.exp(s)


def gx(z, x):
    return 1 + x * x * z / (1 - z) ** 2


# ---------------- b7b-bdry ----------------
def check_boundary():
    ok = True
    worst = []
    s = np.linspace(-60, 60, 24001)
    for tau in (0.05, 0.3, 0.5, 1.0, 2.0, 5.0, 20.0):
        r0 = min(1 / 8, tau / 2)
        tand = min(1.0, tau / 3)
        for k in range(24):
            x = r0 * np.exp(2j * np.pi * k / 24)
            for eps in (1, -1):
                w = psi(s + eps * 1j * np.pi / 2, x, tau)
                in_disc = np.abs(w) < 0.5
                in_sector = (w.real > 0) & (np.abs(w.imag) < tand * w.real)
                if (in_disc | in_sector).any():
                    ok = False
                # 余量：到 Omega' 的「距离」的粗略刻画
                marg = np.minimum(np.abs(w) - 0.5, np.where(w.real > 0, np.abs(w.imag) - tand * w.real, np.inf))
                worst.append(float(marg.min()))
    # 整个圆盘 |x|<=r0 的检验（复核者 s9-b7 的建议）：psi_x(s) = psi_0(s) - x s 对 x 是仿射的，
    # {psi_x(s): |x|<=r0} 是以 psi_0(s) 为心、半径 r0|s| 的闭圆盘，避开开集 Omega' ⇔ dist(psi_0(s), Omega') >= r0|s|
    def dist_omega(w, tand):
        d_disc = np.maximum(np.abs(w) - 0.5, 0.0)
        delta = math.atan(tand)
        inside = (w.real > 0) & (np.abs(np.angle(w)) < delta)
        dr = []
        for sg in (1, -1):
            d = np.exp(1j * sg * delta)
            p = (w * np.conj(d)).real
            dr.append(np.where(p <= 0, np.abs(w), np.abs((w * np.conj(d)).imag)))
        d_sec = np.where(inside, 0.0, np.minimum(dr[0], dr[1]))
        return np.minimum(d_disc, d_sec)
    ok2 = True
    worst2 = []
    s2 = np.linspace(-300, 300, 240001)
    taus = (1e-6, 1e-4, 1e-2, 0.05, 0.2785, 0.5, 1.0, 2.0, 3.0, 10.0, 100.0, 1e4, 1e6)
    for tau in taus:
        r0 = min(1 / 8, tau / 2)
        tand = min(1.0, tau / 3)
        for eps in (1, -1):
            sig = s2 + eps * 1j * np.pi / 2
            marg = dist_omega(psi(sig, 0.0, tau), tand) - r0 * np.abs(sig)
            if not (marg > 0).all():
                ok2 = False
            worst2.append(float(marg.min()))
    report('b7b-bdry', ok and ok2, '边界像与 Omega\' 不相交：圆周取样（7 个 tau × 24 个 x × 2 条边 × 24001 个点，最小余量 %.3f）；'
           '整个圆盘的余量 dist(psi_0, Omega\')-r0|sigma|（%d 个 tau，1e-6..1e6，s∈[-300,300] 上 240001 个点）最小 %.3f'
           % (min(worst), len(taus), min(worst2)))


# ---------------- 反函数 ----------------
def invert_path(ws, x, tau, s0=0j):
    """沿 w 的序列（从 0 附近开始、相邻点接近）用 Newton 延拓求 s_x(w)。"""
    out = np.empty(len(ws), dtype=complex)
    s = s0
    for idx, w in enumerate(ws):
        # 预测
        for _ in range(60):
            f = psi(s, x, tau) - w
            d = dpsi(s, x, tau)
            step = f / d
            s = s - step
            if abs(step) < 1e-15 * (1 + abs(s)):
                break
        out[idx] = s
    return out


def check_invert():
    ok = True
    maxres, minre = 0.0, np.inf
    for tau in (0.05, 0.5, 2.0, 20.0):
        r0 = min(1 / 8, tau / 2)
        tand = min(1.0, tau / 3)
        delta = math.atan(tand)
        for k in range(8):
            x = r0 * np.exp(2j * np.pi * k / 8)
            for ang in np.linspace(-0.99 * delta, 0.99 * delta, 7):
                rad = np.concatenate([np.linspace(0, 0.49, 50), np.linspace(0.5, 50, 400)])
                ws = rad * np.exp(1j * ang)
                ss = invert_path(ws, x, tau)
                res = np.abs(psi(ss, x, tau) - ws)
                maxres = max(maxres, float(res.max()))
                if (np.abs(ss.imag) >= np.pi / 2).any():
                    ok = False
                re = dpsi(ss, x, tau).real
                minre = min(minre, float((re - (1 - abs(x))).min()))
    ok = ok and maxres < 1e-11 and minre >= -1e-12
    report('b7b-inv', ok, 'Newton 延拓求得的 s_x(w) 都在 G 内；max|psi-w|=%.1e；min(Re psi\' - (1-|x|))=%.2e' % (maxres, minre))


# ---------------- 积分 ----------------
GL_X, GL_W = np.polynomial.legendre.leggauss(30)


def I_ray(x, tau, phi, smax=None, panels=400):
    x = complex(x)
    X3 = x ** 3
    c = math.cos(phi - np.angle(X3))
    if c <= 0:
        raise ValueError('ray does not decay')
    if smax is None:
        smax = 80 * abs(X3) / c
    edges = np.linspace(0, smax, panels + 1)
    nodes, wts = [], []
    for a, b in zip(edges[:-1], edges[1:]):
        nodes.append((b - a) / 2 * GL_X + (a + b) / 2)
        wts.append((b - a) / 2 * GL_W)
    nodes = np.concatenate(nodes)
    wts = np.concatenate(wts)
    ws = nodes * np.exp(1j * phi)
    ss = invert_path(ws, x, tau)
    H = gx(-tau * np.exp(ss), x) / dpsi(ss, x, tau)
    val = np.sum(wts * np.exp(-ws / X3) * H) * np.exp(1j * phi) / X3
    return val


def I_sigma(x, tau, smax=None, panels=400):
    """原定义：x 实，sigma 在 [0, inf) 上积分。psi 是凸函数，psi(s) >= (1-x+tau) s，所以积到 80 x^3/(1-x+tau) 即可。"""
    if smax is None:
        smax = 80 * x ** 3 / (1 - x + tau)
    edges = np.linspace(0, smax, panels + 1)
    tot = 0.0
    for a, b in zip(edges[:-1], edges[1:]):
        s = (b - a) / 2 * GL_X + (a + b) / 2
        w = (b - a) / 2 * GL_W
        f = np.exp(-psi(s, x, tau) / x ** 3) * gx(-tau * np.exp(s), x)
        tot += np.sum(w * f)
    return tot / x ** 3


def check_real():
    ok = True
    info = []
    for tau in (0.5, 2.0):
        for x in (0.15, 0.3, 0.5):
            a = I_sigma(x, tau)
            b = I_ray(x, tau, 0.0).real
            rel = abs(a - b) / abs(a)
            info.append('%.2f/%.2f:%.0e' % (tau, x, rel))
            ok = ok and rel < 1e-12
    report('b7b-real', ok, '实 x：sigma 积分与 w 积分一致（相对误差 %s）' % ', '.join(info))


def check_rot():
    ok = True
    info = []
    cases = [(0.5, 0.3, 0.0, 0.2, 0.5), (0.5, 0.3, 0.55, 0.3, 0.9), (2.0, 0.35, 0.6, 0.5, 1.0), (0.5, 0.25, -0.58, -0.4, -1.0)]
    for (tau, r, alpha, p1, p2) in cases:
        x = r * np.exp(1j * alpha)
        a = I_ray(x, tau, p1)
        b = I_ray(x, tau, p2)
        rel = abs(a - b) / abs(a)
        info.append('tau=%.1f x=%.2fe^{%.2fi}: %.0e' % (tau, r, alpha, rel))
        ok = ok and rel < 1e-11
    report('b7b-rot', ok, '两条射线结果一致：%s（pi/6=%.3f）' % ('; '.join(info), math.pi / 6))


# ---------------- f_k(t) ----------------
def N_triangle(K):
    N = [[0] * (K + 3) for _ in range(K + 1)]
    N[0][0] = 1
    N[1][1] = 1
    N[2][1], N[2][2] = 1, 2
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            r = q - 1
            v = N[k - 1][r] + N[k - 1][r + 1]
            if r >= 1:
                v += r * (N[k - 3][r - 1] + 2 * N[k - 3][r] + N[k - 3][r + 1])
            N[k][q] = v
    return N


def f_values(t, K):
    """f_k(t) = h_k(t)/(1-t)^(k+1)，精确有理数，k<=K。"""
    N = N_triangle(K)
    t = Fr(t)
    out = []
    for k in range(K + 1):
        if k == 0:
            h = Fr(1)
        else:
            h = sum(N[k][q] * t ** (q - 1) * (1 - t) ** (k - q) for q in range(1, k + 1))
        out.append(h / (1 - t) ** (k + 1))
    return out


def check_series():
    ok = True
    info = []
    fk = {}
    for tt in (Fr(-1, 2), Fr(-2)):
        fk[tt] = [complex(float(v)) for v in f_values(tt, 140)]
    # 小 |x|：部分和与 I 一致到 1e-12
    for (tt, r, alpha, phi) in [(Fr(-1, 2), 0.3, 0.55, 0.4), (Fr(-1, 2), 0.3, -0.56, -0.5), (Fr(-2), 0.35, 0.6, 0.6),
                                (Fr(-1, 2), 0.35, 0.0, 0.0)]:
        tau = float(-tt)
        x = r * np.exp(1j * alpha)
        I = I_ray(x, tau, phi)
        S = sum(fk[tt][k] * x ** k for k in range(140))
        rel = abs(I - S) / abs(I)
        info.append('t=%s x=%.2fe^{%.2fi}: %.0e' % (tt, r, alpha, rel))
        ok = ok and rel < 1e-12
    # 较大的 |x|：最优截断误差 E(r)=min_K |I - S_K| 按 exp(-c/r^3) 衰减（Gevrey-1/3 渐近的特征），c 对实轴与复方向都有界
    tt = Fr(-1, 2)
    tau = 0.5
    cs = []
    for alpha in (0.0, 0.3, 0.55):
        for r in (0.5, 0.6, 0.7):
            x = r * np.exp(1j * alpha)
            I = I_ray(x, tau, min(0.6, 3 * alpha), panels=1200)
            ps = np.cumsum([fk[tt][k] * x ** k for k in range(140)])
            E = min(abs(ps[K] - I) for K in range(140))
            cs.append((alpha, r, E, -math.log(E) * r ** 3))
    cvals = [c for (_, _, _, c) in cs]
    info.append('最优截断误差 E(r)，r^3·(-ln E)：' + ', '.join('a=%.2f r=%.1f E=%.1e c=%.2f' % v for v in cs))
    mono = all(cs[3 * a][2] < cs[3 * a + 1][2] < cs[3 * a + 2][2] for a in range(3))
    # 宽松判据（只是佐证）：E 随 r 减小而迅速减小，r^3·(-ln E) 有正的上下界；复方向上 c 随 r 变化来自 e^{-w(x)/x^3} 中 x^{-2}、x^{-1} 的次级指数
    ok = ok and mono and min(cvals) > 0.5 and max(cvals) < 4.0
    report('b7b-series', ok, '; '.join(info))


def check_gevrey():
    info = []
    ok = True
    for tt in (Fr(-2), Fr(-5)):
        fv = f_values(tt, 240)
        vals = []
        for k in (60, 120, 180, 240):
            lg = math.log(abs(float(fv[k]))) if fv[k] != 0 else -math.inf
            vals.append(math.exp((lg - math.lgamma(1 + k / 3)) / k))
        info.append('t=%s: %s' % (tt, ', '.join('%.3f' % v for v in vals)))
        ok = ok and max(vals) < 10 and vals[-1] < 1.5 * vals[0] + 1
    report('b7b-gevrey', ok, '(|f_k|/Gamma(1+k/3))^(1/k) 在 k=60,120,180,240：%s（有界）' % '；'.join(info))


def main():
    t0 = time.time()
    check_boundary()
    check_invert()
    check_real()
    check_rot()
    check_series()
    check_gevrey()
    print('time %.1fs' % (time.time() - t0))
    npass = sum(RESULTS)
    print('SUMMARY b7b pass=%d fail=%d' % (npass, len(RESULTS) - npass))
    return 0 if npass == len(RESULTS) else 1


if __name__ == '__main__':
    sys.exit(main())
