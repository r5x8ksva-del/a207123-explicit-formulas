# -*- coding: utf-8 -*-
"""s11-b6b 复核脚本 5：定理 2.2–2.3 的单值（跳跃 -nu*omega、交换子）用高精度 Taylor 级数逐圆盘解析延拓核对。
与 check_b6 的 RK4 不同：每一步在圆心 c 处由 ODE 精确递推出 f 的 Taylor 系数（K 项），在半径的约 1/4 处求和，
decimal 60 位，截断误差 < 1e-50；不用命题 1。起点值 f_x(t_0) 用级数 sum G_m t_0^m（t_0 = 1/2）。
ODE：x^3 t f' = (1-x-t) f - gamma(t)，gamma = 1 + x^2 t/(1-t)^2。在 t = c+s 处：
  x^3 [c(k+1) a_{k+1} + k a_k] = (1-x-c) a_k - a_{k-1} - g_k，g_k = [s^k] gamma(c+s)。
  NT-mono   x = 0.6, 0.7, 2, -1.5, 0.6+0.2i：f^{g0} = f；f^{g1} - f = -nu omega(t0)；f^{g0 g1} - f^{g1 g0} = -nu(1-e^{2 pi i lam}) omega(t0)
            （记号 f^{ab}：先 a 后 b）；另在 x=0.6 核对 a=2, b=3 的一般式 -b nu (1-e^{2 pi i lam a}) omega
  NT-qrat   lam = 1/2：[g0, g1] 的差 = -2 nu omega；[g0^2, g1] 的差 = 0
  NT-int    x = -1（lam=-2）：交换子 = 0，跳跃 = -nu omega = 2 pi i e^{t0-1}/t0^2 ≠ 0
  NT-ei     x = -1：沿上、下两条道路（绕过 t=1）延拓到 t = 3/2，与命题 8 的闭式比较：上路对应 log(1-t) = ln|1-t| - i pi，
            下路对应 + i pi；再沿 t=0 上方到 t = -3/2（单位圆外的负实轴），与闭式（实的 Ei）比较
  NT-rev    反向检查：朴素常数 2 pi i z x^2 e^z 与数值跳跃不符；把 e^{2 pi i lam} 换成 e^{-2 pi i lam} 时交换子不符
"""
import os
import sys
import time
from decimal import Decimal as D

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cdec import CD, set_prec, cexp, clog, pi, sincos, newton_real  # noqa: E402

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')

PREC = 60
set_prec(PREC)
RES = []
K = 170
NSTEP = 24
TOL = D(10) ** (-40)


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


def f_series(x, t, N=260):
    x2 = x * x
    x3 = x2 * x
    s, p, g = CD(0), CD(1), CD(0)
    for m in range(N + 1):
        g = (CD(1) if m == 0 else g + m * x2) / (1 - x - m * x3) if m > 0 else CD(1) / (1 - x)
        s = s + g * p
        p = p * t
    return s


def taylor_step(x, c, fc, delta):
    x2 = x * x
    x3 = x2 * x
    d = 1 - c
    # g_k
    inv_d = CD(1) / d
    g = []
    pw = inv_d * inv_d               # 1/d^{k+2} 从 k=0 开始
    pw1 = inv_d                      # 1/d^{k+1}
    for k in range(K + 1):
        if k == 0:
            g.append(1 + x2 * c * pw)
        else:
            g.append(x2 * (c * (k + 1) * pw + k * pw1))
        pw = pw * inv_d
        pw1 = pw1 * inv_d
    a = [fc]
    am1 = CD(0)
    A = 1 - x - c
    den0 = x3 * c
    for k in range(K):
        nxt = (A * a[k] - am1 - g[k] - x3 * k * a[k]) / (den0 * (k + 1))
        am1 = a[k]
        a.append(nxt)
    s, p = CD(0), CD(1)
    for k in range(K + 1):
        s = s + a[k] * p
        p = p * delta
    return s


def unit(theta):
    s, c = sincos(theta)
    return CD(c, s)


def loop_points(kind, t0, n=NSTEP, sign=1):
    pts = []
    for j in range(n + 1):
        th = 2 * pi() * j / n * sign
        if kind == 0:
            pts.append(CD(t0) * unit(th))
        else:
            r = 1 - t0
            pts.append(CD(1) + CD(r) * unit(pi() + th))
    return pts


def continue_along(x, f0, pts):
    f = f0
    for j in range(len(pts) - 1):
        f = taylor_step(x, pts[j], f, pts[j + 1] - pts[j])
    return f


def run_word(x, f0, t0, word):
    """word：0/1 组成的序列，依次绕 gamma_0 / gamma_1（逆时针）。"""
    f = f0
    for w in word:
        f = continue_along(x, f, loop_points(w, t0))
    return f


def predictions(x, t0):
    z = CD(1) / (x * x * x)
    lam = (1 - x) * z
    omega = cexp(lam * D(t0).ln() - z * t0)
    nu = CD(0, 2 * pi()) * z * cexp(z)
    e = cexp(CD(0, 2 * pi()) * lam)
    return z, lam, omega, nu, e


def rel(a, scale):
    return a.abs() / scale


def main():
    t0 = D('0.5')
    tstart = time.time()
    ok = True
    lines = []
    for name, x in (('0.6', CD(D('0.6'))), ('0.7', CD(D('0.7'))), ('2', CD(D(2))), ('-1.5', CD(D('-1.5'))),
                    ('0.6+0.2i', CD(D('0.6'), D('0.2')))):
        f0 = f_series(x, CD(t0))
        z, lam, omega, nu, e = predictions(x, t0)
        scale = (nu * omega).abs()
        a = run_word(x, f0, t0, [0])
        b = run_word(x, f0, t0, [1])
        ab = run_word(x, f0, t0, [0, 1])
        ba = run_word(x, f0, t0, [1, 0])
        e0 = rel(a - f0, scale)
        e1 = rel((b - f0) + nu * omega, scale)
        e2 = rel((ab - ba) + nu * (1 - e) * omega, scale)
        good = e0 < TOL and e1 < TOL and e2 < TOL and rel(nu * (1 - e) * omega, scale) > D('1e-3')
        ok &= good
        lines.append('x=%s: |jump1|=%.4g, err %.1e/%.1e/%.1e' % (name, float((b - f0).abs()), float(e0), float(e1), float(e2)))
        if name == '0.6':
            w1 = run_word(x, f0, t0, [0, 0, 1, 1, 1])
            w2 = run_word(x, f0, t0, [1, 1, 1, 0, 0])
            e2b = cexp(CD(0, 4 * pi()) * lam)
            e3 = rel((w1 - w2) + 3 * nu * (1 - e2b) * omega, scale)
            ok &= e3 < TOL
            lines.append('x=0.6 (a,b)=(2,3): err %.1e' % float(e3))
            store06 = (x, f0, z, lam, omega, nu, b)
    report('NT-mono', ok, '（数值，60 位 Taylor 延拓）绕 0 不变、绕 1 跳 -nu omega、交换子 -nu(1-e^{2pi i lam})omega：' + '; '.join(lines))

    # lam = 1/2
    xh = CD(newton_real(lambda u: u ** 3 + 2 * u - 2, lambda u: 3 * u * u + 2, D('0.77')))
    f0 = f_series(xh, CD(t0))
    z, lam, omega, nu, e = predictions(xh, t0)
    scale = (nu * omega).abs()
    c1 = run_word(xh, f0, t0, [0, 1]) - run_word(xh, f0, t0, [1, 0])
    c2 = run_word(xh, f0, t0, [0, 0, 1]) - run_word(xh, f0, t0, [1, 0, 0])
    okq = rel(c1 + 2 * nu * omega, scale) < TOL and rel(c2, scale) < TOL
    report('NT-qrat', okq, 'lam=1/2（|lam-1/2|=%.1e）：|[g0,g1] 的差 + 2 nu omega|/|nu omega| = %.1e，|[g0^2,g1] 的差|/|nu omega| = %.1e'
           % (float((lam - D('0.5')).abs()), float(rel(c1 + 2 * nu * omega, scale)), float(rel(c2, scale))))

    # x = -1
    xm = CD(D(-1))
    f0 = f_series(xm, CD(t0))
    z, lam, omega, nu, e = predictions(xm, t0)
    scale = (nu * omega).abs()
    b = run_word(xm, f0, t0, [1])
    comm = run_word(xm, f0, t0, [0, 1]) - run_word(xm, f0, t0, [1, 0])
    pred = CD(0, 2 * pi()) * cexp(CD(t0 - 1)) / (t0 * t0)
    oki = rel(comm, scale) < TOL and rel((b - f0) - pred, scale) < TOL and rel((b - f0) + nu * omega, scale) < TOL
    report('NT-int', oki, 'x=-1：|交换子|/|nu omega| = %.1e；跳跃 = %s（预测 2 pi i e^{t0-1}/t0^2 = i*%s）'
           % (float(rel(comm, scale)), str((b - f0).i)[:20], str(pred.i)[:20]))

    # NT-ei：x=-1 延拓到单位圆外
    def F_closed(t, logbranch):
        t = CD.of(t)
        one = CD(1)
        w = one - t
        # Ei(1-t) - Ei(1) = log(1-t) + sum ((1-t)^k - 1)/(k k!)，log 取给定分支
        eps = D(10) ** (-(PREC + 8))
        s, term, k = CD(0), CD(1), 0
        s1, term1 = CD(0), CD(1)
        while True:
            k += 1
            term = term * w / k
            term1 = term1 * one / k
            add = (term - term1) / k
            s = s + add
            if add.abs() < eps and k > 10:
                break
        d1 = logbranch + s
        return (cexp(t) - 1 + t * t / (one - t) + cexp(t - 1) * d1) / (t * t)

    f0 = f_series(xm, CD(t0))
    r = 1 - t0
    up = [CD(1) + CD(r) * unit(pi() - pi() * j / NSTEP) for j in range(NSTEP + 1)]     # 上半圆：从 1/2 到 3/2
    dn = [CD(1) + CD(r) * unit(-pi() + pi() * j / NSTEP) for j in range(NSTEP + 1)]    # 下半圆
    fu = continue_along(xm, f0, up)
    fd = continue_along(xm, f0, dn)
    t15 = CD(D('1.5'))
    ln_half = D('0.5').ln()
    Fu = F_closed(t15, CD(ln_half, -pi()))
    Fd = F_closed(t15, CD(ln_half, pi()))
    # 到 -3/2：沿 |t|=1/2 的上半圆到 -1/2，再沿负实轴走到 -3/2
    path = [CD(t0) * unit(pi() * j / NSTEP) for j in range(NSTEP + 1)]
    path += [CD(D('-0.5') - D(j) / 16) for j in range(1, 17)]
    fneg = continue_along(xm, f0, path)
    Fneg = F_closed(CD(D('-1.5')), clog(CD(D('2.5'))))
    sc = Fu.abs()
    oke = (fu - Fu).abs() / sc < TOL and (fd - Fd).abs() / sc < TOL and (fneg - Fneg).abs() / Fneg.abs() < TOL
    oke &= (fu - Fd).abs() / sc > D('0.1')        # 分支取反就不符
    report('NT-ei', oke, 'x=-1 闭式在单位圆外：t=3/2 上路差 %.1e、下路差 %.1e（对应 log(1-t) 的 -i pi / +i pi；取反则差 %.2f），'
           't=-3/2 差 %.1e' % (float((fu - Fu).abs() / sc), float((fd - Fd).abs() / sc), float((fu - Fd).abs() / sc),
                               float((fneg - Fneg).abs() / Fneg.abs())))

    # 反向检查
    x, f0, z, lam, omega, nu, b = store06
    scale = (nu * omega).abs()
    naive = CD(0, 2 * pi()) * z * x * x * cexp(z)
    rv1 = rel((b - f0) + naive * omega, scale) > D('0.1')
    ab = run_word(x, f0, t0, [0, 1])
    ba = run_word(x, f0, t0, [1, 0])
    ebad = cexp(CD(0, -2 * pi()) * lam)
    rv2 = rel((ab - ba) + nu * (1 - ebad) * omega, scale) > D('0.1')
    report('NT-rev', rv1 and rv2, '反向检查（x=0.6）：朴素常数 2 pi i z x^2 e^z 不符：%s；e^{2 pi i lam} 换成 e^{-2 pi i lam} 时交换子不符：%s' % (rv1, rv2))
    print('time %.1fs' % (time.time() - tstart))
    print('SUMMARY s11-b6b nu_taylor pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
    return 0 if all(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
