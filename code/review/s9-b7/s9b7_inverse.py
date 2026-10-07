# -*- coding: utf-8 -*-
"""s9-b7 独立核对 P1-P3：命题 4（Omega' ⊆ psi_x(G)，且在 G 中恰有一个原像）与引理 5（|H| 的界、Re z<0）。

不导入项目里的任何模块。numpy 双精度。

P1  辐角原理：对 w ∈ Omega' 的取样点，数 psi_x(s)-w 在矩形 [-L1,L2]×[-pi/2,pi/2] 里的零点个数。
    由引理 3，|Re s| 超出矩形时 |psi_x(s)|>|w|，所以矩形里的个数就是 G 里的个数（引理 2 保证上下两边上没有零点）。
    命题 4 + 引理 1 断言个数恰为 1。沿边界逐点跟踪 arg(psi_x(s)-w)，相邻点辐角差超过 0.3 就加密。
    对照：也数几个 Omega' 外的 w（信息性，不判定）。
P2  沿线段 [0,w]（Omega' 对 0 星形）做延拓（RK4 预测 + Newton 校正）求 s_x(w)：解在 G 内，|psi_x(s)-w| 小；
    由此算 H(w,x)，检查 |H| <= (1+r0^2/2)/(1-r0) 与 Re z<0（z=-tau e^s）。
P3  P2 的解与 P1 的辐角原理一致：在 s_x(w) 周围的小圆上辐角原理也给 1（定位的零点就是那唯一的一个）。
"""
import math
import sys
import time

import numpy as np

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def params(tau):
    r0 = min(1 / 8, tau / 2)
    tand = min(1.0, tau / 3)
    return r0, tand, math.atan(tand)


def psi(s, x, tau):
    return (1 - x) * s + tau * np.expm1(s)


def dpsi(s, x, tau):
    return (1 - x) + tau * np.exp(s)


def winding(fun, path_pts, max_refine=6):
    """fun 在闭折线 path_pts（首尾相接）上的绕数；自适应加密使相邻辐角差 < 0.3。返回 (绕数实数值, min|f|)。"""
    total = 0.0
    fmin = np.inf
    P = list(path_pts) + [path_pts[0]]
    for A, B in zip(P[:-1], P[1:]):
        n = 64
        for _ in range(max_refine):
            u = np.linspace(0, 1, n + 1)
            z = A + (B - A) * u
            f = fun(z)
            ang = np.angle(f)
            d = np.diff(ang)
            d = (d + np.pi) % (2 * np.pi) - np.pi
            if np.abs(d).max() < 0.3:
                break
            n *= 4
        else:
            raise RuntimeError('winding: cannot resolve')
        total += d.sum()
        fmin = min(fmin, float(np.abs(f).min()))
    return total / (2 * np.pi), fmin


def rect_count(x, tau, w):
    W = abs(w)
    L1 = 8 * (W + 1 + 2 * tau) / 7 + 1
    # 右边：tau e^s - (9/8)(s+pi/2) - tau > W+1
    L2 = 0.0
    while tau * math.exp(L2) - (9 / 8) * (L2 + math.pi / 2) - tau <= W + 1:
        L2 += 0.25
    L2 += 0.5
    h = math.pi / 2
    # 每条边再细分成若干段，便于自适应（右段 e^s 变化快，分得更细）
    pts = []
    xs = np.unique(np.concatenate([np.linspace(-L1, -10, 21), np.linspace(-10, L2, 4 * int(L2 + 10) + 2)]))
    for s in xs[:-1]:
        pts.append(complex(s, -h))
    ys = np.linspace(-h, h, 9)
    for y in ys[:-1]:
        pts.append(complex(L2, y))
    for s in xs[::-1][:-1]:
        pts.append(complex(s, h))
    for y in ys[::-1][:-1]:
        pts.append(complex(-L1, y))
    wnd, fmin = winding(lambda z: psi(z, x, tau) - w, pts)
    return wnd, fmin


def sigma_of_w(x, tau, w, nsteps=400):
    """沿 lam*w（lam: 0->1）延拓：d s/d lam = w/psi'(s)，RK4 + Newton 校正。"""
    s = 0j
    # |w| 大时开头 s 变化快，用几何步长
    lams = np.concatenate([[0.0], np.geomspace(1e-4 / max(1.0, abs(w)), 1.0, nsteps)])
    for l0, l1 in zip(lams[:-1], lams[1:]):
        hstep = l1 - l0
        f = lambda ss: w / dpsi(ss, x, tau)
        k1 = f(s)
        k2 = f(s + hstep / 2 * k1)
        k3 = f(s + hstep / 2 * k2)
        k4 = f(s + hstep * k3)
        s = s + hstep / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        target = l1 * w
        for _ in range(6):
            step = (psi(s, x, tau) - target) / dpsi(s, x, tau)
            s -= step
            if abs(step) < 1e-16 * (1 + abs(s)):
                break
    return s


def w_samples(delta):
    ws = [0.0 + 0j]
    for r in (0.05, 0.2, 0.35, 0.49):
        for k in range(16):
            ws.append(r * np.exp(2j * np.pi * k / 16))
    for ang in (0.999 * delta, 0.5 * delta, 0.0, -0.5 * delta, -0.999 * delta):
        for r in (0.5, 1.0, 3.0, 10.0, 30.0, 100.0, 1000.0):
            ws.append(r * np.exp(1j * ang))
    return ws


def main():
    t0 = time.time()
    taus = [1e-4, 1e-2, 0.25, 0.5, 2.0, 3.0, 30.0, 1e4]
    cnt_bad = 0
    ncase = 0
    fmin_all = np.inf
    info_out = []
    p2_ok = True
    maxres = 0.0
    maxH_ratio = 0.0
    max_im = 0.0
    p3_bad = 0
    for tau in taus:
        r0, tand, delta = params(tau)
        xs = [0j] + [r0 * np.exp(2j * np.pi * k / 12) for k in range(12)] + [0.6 * r0 * np.exp(1j * np.pi / 3)]
        Hbound = (1 + r0 ** 2 / 2) / (1 - r0)
        for x in xs:
            for w in w_samples(delta):
                wnd, fmin = rect_count(x, tau, w)
                ncase += 1
                fmin_all = min(fmin_all, fmin)
                if abs(wnd - 1) > 1e-6:
                    cnt_bad += 1
                # P2
                s = sigma_of_w(x, tau, w, nsteps=200 if abs(w) < 1 else 600)
                res = abs(psi(s, x, tau) - w) / max(1.0, abs(w))
                maxres = max(maxres, res)
                max_im = max(max_im, abs(s.imag))
                if abs(s.imag) >= np.pi / 2:
                    p2_ok = False
                z = -tau * np.exp(s)
                if not (z.real < 0):
                    p2_ok = False
                H = (1 + x * x * z / (1 - z) ** 2) / dpsi(s, x, tau)
                maxH_ratio = max(maxH_ratio, abs(H) / Hbound)
                # P3：s 周围小圆上的绕数
                rad = min(0.05, (np.pi / 2 - abs(s.imag)) / 2)
                circ = [s + rad * np.exp(2j * np.pi * k / 16) for k in range(16)]
                wc, _ = winding(lambda zz: psi(zz, x, tau) - w, circ)
                if abs(wc - 1) > 1e-6:
                    p3_bad += 1
        # 信息性：Omega' 外的点
        for wout in (-5 + 0j, 3 * np.exp(1j * (delta + 0.3)), 50 * np.exp(1j * min(delta + 0.5, 2.5)), -50 + 3j):
            wnd, _ = rect_count(r0 * np.exp(1j * np.pi / 4), tau, wout)
            info_out.append('tau=%g,w=%.3g%+.3gi:%d' % (tau, wout.real, wout.imag, round(wnd)))
    report('P1', cnt_bad == 0, '辐角原理：%d 个 (tau,x,w) 组合（8 个 tau，x 取 0、圆周 |x|=r0 上 12 点与一个内点，w 取 Omega\' 中 100 个点（w=0、圆盘内 64 点、扇形内 35 点），含 |arg w|=0.999δ、|w|=1000）'
           '在 G 中的原像个数都等于 1（不等于 1 的组合数 %d）；边界上 min|psi-w|=%.3g' % (ncase, cnt_bad, fmin_all))
    report('P2', p2_ok and maxres < 1e-12 and maxH_ratio <= 1.0,
           '沿 [0,w] 延拓：解都在 G 内（max|Im s|=%.4f<pi/2），max 相对残差 %.1e；Re z<0 处处成立；max|H|/[(1+r0^2/2)/(1-r0)]=%.4f（<=1）'
           % (max_im, maxres, maxH_ratio))
    report('P3', p3_bad == 0, '延拓得到的 s_x(w) 周围小圆上的绕数都是 1（不符的组合 %d 个）；信息性：Omega\' 外几个点的原像个数 %s'
           % (p3_bad, ', '.join(info_out)))
    print('time %.1fs' % (time.time() - t0))
    n = sum(RES)
    print('SUMMARY s9b7_inverse pass=%d fail=%d' % (n, len(RES) - n))
    return 0 if n == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
