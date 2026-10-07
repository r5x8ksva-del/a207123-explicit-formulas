# -*- coding: utf-8 -*-
"""s9-b7 独立核对 L1-L6：notes/09 引理 2（边界像避开 Omega'）与引理 3（真性）的数值检验，含极端 tau。

不导入项目里的任何模块。numpy 双精度。

关键化简（使检验覆盖整个圆盘 |x|<=r0，而不是圆周上的若干取样点）：
  psi_x(s) = psi_0(s) - x*s 对 x 是仿射的，所以 {psi_x(s): |x|<=r0} 恰是以 psi_0(s) 为心、半径 r0|s| 的闭圆盘。
  Omega' 是开集，故「对一切 |x|<=r0，psi_x(s) 不在 Omega' 中」 <=> dist(psi_0(s), Omega') >= r0*|s|。
  于是余量 marg(s) := dist(psi_0(s), Omega') - r0*|s| >= 0 就是引理 2 在该 s 处对整个圆盘成立的充要条件。
  （共轭对称：Im s = -pi/2 的边与 Im s = +pi/2 的边余量相同，所以只算上边；L2 另外直接取样两条边。）

  L1  余量 marg(s) 在 s∈[-1000,600]（|s|<=10 处步长 5e-5）上恒正；tau 取 21 个值 1e-8 … 1e8
  L2  直接取样：x 在圆周 |x|=r0 上 720 个方向、两条边、s 取 12001 个点，psi_x(s) 都不在 Omega' 中
  L3  证明里三个情形的中间不等式（按证明的写法只用 |a|,|b|<=r0，所以在正方形的四个角上检验，比圆盘更强）
  L4  引理 3 的两个下界：min_{|x|<=r0}|psi_x(s)| = max(0,|psi_0(s)|-r0|s|) 不小于证明给出的下界
  L5  说明常数确实需要随 tau 变小（不是证明的缺口，是「r0、delta 依赖 tau」的必要性）：
      tau 很小时若取 r=1/8（不缩小）或 tan(delta)=1（不缩小），引理 2 的结论会失败
  L6  「真实」的最大半径 r*(tau) = inf_s dist(psi_0(s),Omega')/|s|（给定 delta 时引理 2 成立的最大 r）与 r0 的比较（信息性）
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


TAUS = [1e-8, 1e-6, 1e-4, 1e-3, 0.01, 0.05, 0.1, 0.2, 0.25, 0.3, 0.5, 1.0, 2.0, 2.9, 3.0, 3.1, 5.0, 10.0, 100.0, 1e4, 1e8]


def params(tau):
    r0 = min(1 / 8, tau / 2)
    tand = min(1.0, tau / 3)
    return r0, tand, math.atan(tand)


def psi0(s, tau):
    return s + tau * np.expm1(s)


def psix(s, x, tau):
    return (1 - x) * s + tau * np.expm1(s)


def psi_edge(s, x, tau, eps):
    """边 Im sigma = eps*pi/2 上的精确公式（e^sigma = i*eps*e^s）。
    不能用 expm1(s + i pi/2)：浮点的 cos(pi/2)=6e-17 会给实部混进 tau*e^s*6e-17，s 大时淹没真实的实部。"""
    a, b = x.real, x.imag
    re = (1 - a) * s + eps * b * np.pi / 2 - tau
    im = eps * ((1 - a) * np.pi / 2 + tau * np.exp(s) - eps * b * s)
    return re + 1j * im


def dist_omega(p, delta):
    """到 Omega'={|w|<1/2} ∪ {w≠0: |arg w|<delta} 的距离；点在 Omega' 内时返回负数（-1）。"""
    r = np.abs(p)
    ang = np.abs(np.angle(p))
    inside = (r < 0.5) | ((ang < delta) & (r > 0))
    d_disc = r - 0.5
    d_sec = np.where(ang - delta <= np.pi / 2, r * np.sin(ang - delta), r)
    d = np.minimum(d_disc, d_sec)
    return np.where(inside, -1.0, d)


def in_omega(p, delta):
    r = np.abs(p)
    ang = np.abs(np.angle(p))
    return (r < 0.5) | ((ang < delta) & (r > 0))


def s_grid():
    return np.concatenate([np.linspace(-1000, -10, 99001), np.linspace(-10, 10, 400001)[1:-1],
                           np.linspace(10, 600, 118001)])


def main():
    t0 = time.time()
    S = s_grid()
    sig = S + 1j * np.pi / 2

    # L1
    ok = True
    info = []
    rstar = {}
    for tau in TAUS:
        r0, tand, delta = params(tau)
        p = psi_edge(S, 0j, tau, 1)
        d = dist_omega(p, delta)
        marg = d - r0 * np.abs(sig)
        i = int(np.argmin(marg))
        ok = ok and marg.min() > 0 and np.isfinite(marg).all()
        # 余量的两端应当向外增大（排除网格端点处才是最小值的情形）
        ok = ok and marg[0] > marg[100] and marg[-1] > marg[-101]
        info.append('tau=%g:min %.3g@s=%.3f' % (tau, marg.min(), S[i]))
        pos = d > 0
        rstar[tau] = float(np.min(d[pos] / np.abs(sig[pos]))) if pos.all() else float('nan')
    report('L1', ok, '整个圆盘 |x|<=r0 上的余量 dist(psi_0,Omega\')-r0|s| 恒正：' + '; '.join(info))

    # L2 直接取样
    ok = True
    nviol = 0
    Sc = np.concatenate([np.linspace(-200, -10, 1901), np.linspace(-10, 10, 8001)[1:-1], np.linspace(10, 300, 2101)])
    for tau in TAUS:
        r0, tand, delta = params(tau)
        for k in range(720):
            x = r0 * np.exp(2j * np.pi * k / 720)
            for eps in (1, -1):
                w = psi_edge(Sc, x, tau, eps)
                v = int(in_omega(w, delta).sum())
                nviol += v
    ok = nviol == 0
    report('L2', ok, '直接取样（21 个 tau × 720 个 x × 2 条边 × %d 个 s）落入 Omega\' 的点数 = %d' % (len(Sc), nviol))

    # L3 证明中的中间不等式（在 |a|,|b|<=r0 的正方形四角检验）
    ok = True
    worst = {'A': -np.inf, 'B1': np.inf, 'B2': -np.inf, 'C1': np.inf, 'C2': -np.inf, 'C3': np.inf}
    sA = np.linspace(-1000, -2, 99801)[:-1]
    sB = np.linspace(-2, 0, 20001)
    sC = np.concatenate([np.linspace(0, 10, 100001)[1:], np.linspace(10, 600, 59001)[1:]])
    for tau in TAUS:
        r0, tand, delta = params(tau)
        for a in (r0, -r0):
            for b in (r0, -r0):
                x = a + 1j * b
                for eps in (1, -1):
                    pA = psi_edge(sA, x, tau, eps)
                    pB = psi_edge(sB, x, tau, eps)
                    pC = psi_edge(sC, x, tau, eps)
                    worst['A'] = max(worst['A'], float(pA.real.max()))            # 应 < -1.55
                    worst['B1'] = min(worst['B1'], float((eps * pB.imag).min()))  # 应 >= 1.12
                    worst['B2'] = max(worst['B2'], float(pB.real.max()))          # 应 < 0.2
                    lhsC = eps * pC.imag - (1.374 + (tau / 2) * sC)
                    worst['C1'] = min(worst['C1'], float(lhsC.min()))             # 应 >= 0
                    worst['C2'] = max(worst['C2'], float((pC.real - (9 / 8) * sC - 0.2).max()))  # 应 <= 0
                    # 最终结论：Re>0 处 |Im| > tan(delta) Re
                    m = pC.real > 0
                    if m.any():
                        worst['C3'] = min(worst['C3'], float((np.abs(pC.imag[m]) - tand * pC.real[m]).min()))  # 应 > 0
    ok = (worst['A'] < -1.55 and worst['B1'] >= 1.12 and worst['B2'] < 0.2 and worst['C1'] >= -1e-9
          and worst['C2'] <= 1e-9 and worst['C3'] > 0)
    report('L3', ok, '中间不等式（正方形四角、21 个 tau、两条边）：s<-2 时 max Re psi=%.4f(<-1.55)；-2<=s<=0 时 min eps·Im psi=%.4f(>=1.12)、'
           'max Re psi=%.4f(<0.2)；s>0 时 min[eps·Im psi-1.374-(tau/2)s]=%.3g(>=0)、max[Re psi-(9/8)s-0.2]=%.3g(<=0)、'
           'min[|Im psi|-tan(delta)Re psi]=%.4f(>0)' % (worst['A'], worst['B1'], worst['B2'], worst['C1'], worst['C2'], worst['C3']))

    # L4 引理 3
    ok = True
    worst_r = np.inf
    worst_l = np.inf
    Sr = np.concatenate([np.linspace(0, 10, 2001), np.linspace(10, 300, 2901)[1:]])
    Sl = np.linspace(-500, 0, 5001)
    ims = np.linspace(-np.pi / 2, np.pi / 2, 61)
    for tau in TAUS:
        r0, tand, delta = params(tau)
        for im in ims:
            sr = Sr + 1j * im
            mn = np.maximum(0, np.abs(psi0(sr, tau)) - r0 * np.abs(sr))
            lb = tau * np.exp(Sr) - (9 / 8) * (Sr + np.pi / 2) - tau
            # 相对比较（大 s 时两边都极大）
            diff = (mn - lb) / np.maximum(1, np.abs(lb))
            worst_r = min(worst_r, float(diff.min()))
            sl = Sl + 1j * im
            mn2 = np.maximum(0, np.abs(psi0(sl, tau)) - r0 * np.abs(sl))
            lb2 = (7 / 8) * np.abs(Sl) - 2 * tau
            worst_l = min(worst_l, float(((mn2 - lb2) / np.maximum(1, np.abs(lb2))).min()))
    ok = worst_r >= -1e-12 and worst_l >= -1e-12
    report('L4', ok, '引理 3 两个下界（21 个 tau、Im s 取 61 个值、整个圆盘 |x|<=r0）：Re s>=0 的最小相对余量 %.3g，Re s<=0 的 %.3g（都应 >=0）'
           % (worst_r, worst_l))

    # L5 必要性：不缩小的常数会失败
    info = []
    fail_r = []
    for tau in (1e-8, 1e-7, 1e-6, 1e-5):
        r, tand = 1 / 8, min(1.0, tau / 3)
        d = dist_omega(psi_edge(S, 0j, tau, 1), math.atan(tand))
        marg = d - r * np.abs(sig)
        fail_r.append(marg.min() < 0)
        info.append('r=1/8,tau=%g:min余量 %.3g' % (tau, marg.min()))
    fail_d = []
    for tau in (1e-3, 0.01, 0.1, 1.0):
        r0 = min(1 / 8, tau / 2)
        d = dist_omega(psi_edge(S, 0j, tau, 1), math.atan(1.0))
        marg = d - r0 * np.abs(sig)
        fail_d.append(marg.min() < 0)
        info.append('tan(delta)=1,tau=%g:min余量 %.3g' % (tau, marg.min()))
    ok = fail_r[0] and fail_d[0]
    report('L5', ok, '常数随 tau 缩小是必要的（tau 很小时不缩小 r 或 delta 会出现负余量，即边界像进入 Omega\'）：' + '; '.join(info))

    # L6 信息性
    info = ['tau=%g: r0=%.3g, r*=%.3g' % (tau, params(tau)[0], rstar[tau]) for tau in TAUS]
    report('L6', all(rstar[t] >= params(t)[0] for t in TAUS), '给定 delta 时引理 2 成立的最大半径 r*（>= r0 即可）：' + '; '.join(info))

    print('time %.1fs' % (time.time() - t0))
    n = sum(RES)
    print('SUMMARY s9b7_lemma23 pass=%d fail=%d' % (n, len(RES) - n))
    return 0 if n == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
