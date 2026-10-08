# -*- coding: utf-8 -*-
"""s11-b6b 复核脚本 7：有理数 x 处 lam = (1-x)/x^3 一定是有理数，所以由定理 6.2 的 ⇐，f_x 在 V 里。
例：x = 3/5（check_b6 的 b6-mono 用的点之一），lam = 50/27。用脚本 5 的高精度 Taylor 延拓（这里 45 位）核对：
  RX-27   [g0^a, g1] 的差 = -nu(1-e^{2 pi i lam a}) omega：a=1、13 时不为零，a=27 时为零（e^{2 pi i * 50} = 1）
  RX-list check_b6 的实数测试点 x = 0.6, 0.7, 2, -1.5 的 lam 都是有理数（精确算出），复数点 0.6+0.2i 的 lam = 1/4 - 7i/4 不是实数
"""
import os
import sys
import time
from decimal import Decimal as D
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cdec  # noqa: E402
from cdec import CD, set_prec, cexp, pi, sincos  # noqa: E402

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')

set_prec(45)
K = 120
NSTEP = 24
RES = []


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


def f_series(x, t, N=200):
    x2, x3 = x * x, x * x * x
    s, p, g = CD(0), CD(1), CD(0)
    for m in range(N + 1):
        g = CD(1) / (1 - x) if m == 0 else (g + m * x2) / (1 - x - m * x3)
        s = s + g * p
        p = p * t
    return s


def taylor_step(x, c, fc, delta):
    x2, x3 = x * x, x * x * x
    d = 1 - c
    inv_d = CD(1) / d
    pw, pw1 = inv_d * inv_d, inv_d
    g = []
    for k in range(K + 1):
        g.append(1 + x2 * c * pw if k == 0 else x2 * (c * (k + 1) * pw + k * pw1))
        pw, pw1 = pw * inv_d, pw1 * inv_d
    a, am1 = [fc], CD(0)
    A, den0 = 1 - x - c, x3 * c
    for k in range(K):
        nxt = (A * a[k] - am1 - g[k] - x3 * k * a[k]) / (den0 * (k + 1))
        am1 = a[k]
        a.append(nxt)
    s, p = CD(0), CD(1)
    for k in range(K + 1):
        s = s + a[k] * p
        p = p * delta
    return s


def unit(th):
    s, c = sincos(th)
    return CD(c, s)


def loop(x, f, kind, t0):
    pts = []
    for j in range(NSTEP + 1):
        th = 2 * pi() * j / NSTEP
        pts.append(CD(t0) * unit(th) if kind == 0 else CD(1) + CD(1 - t0) * unit(pi() + th))
    for j in range(NSTEP):
        f = taylor_step(x, pts[j], f, pts[j + 1] - pts[j])
    return f


def main():
    t0w = time.time()
    t0 = D('0.5')
    x = CD(D(3) / 5)
    z = CD(1) / (x * x * x)
    lam = (1 - x) * z
    omega = cexp(lam * t0.ln() - z * t0)
    nu = CD(0, 2 * pi()) * z * cexp(z)
    scale = (nu * omega).abs()
    f0 = f_series(x, CD(t0))
    out = []
    ok = True
    # 先 g0^a 后 g1，与先 g1 后 g0^a
    fa = f0
    fb = loop(x, f0, 1, t0)
    for a in range(1, 28):
        fa = loop(x, fa, 0, t0)
        fb = loop(x, fb, 0, t0)
        if a in (1, 13, 27):
            left = loop(x, fa, 1, t0)          # f^{g0^a g1}
            diff = left - fb                   # 减 f^{g1 g0^a}
            pred = CD(0) - nu * (1 - cexp(CD(0, 2 * pi()) * lam * a)) * omega
            err = (diff - pred).abs() / scale
            mag = diff.abs() / scale
            out.append('a=%d: |差|/|nu omega|=%.3e，与公式偏差 %.1e' % (a, float(mag), float(err)))
            ok &= err < D('1e-30')
            if a == 27:
                ok &= mag < D('1e-30')
            else:
                ok &= mag > D('0.1')
    report('RX-27', ok, 'x=3/5（lam=%s≈%s）：' % ('50/27', str(lam.r)[:12]) + '；'.join(out))
    lams = []
    okl = True
    for xv in (Fr(3, 5), Fr(7, 10), Fr(2), Fr(-3, 2)):
        lv = (1 - xv) / xv ** 3
        lams.append('x=%s: lam=%s' % (xv, lv))
    # 复数点 0.6+0.2i：精确 Gauss 有理数
    xr, xi = Fr(3, 5), Fr(1, 5)
    x2r, x2i = xr * xr - xi * xi, 2 * xr * xi
    x3r, x3i = x2r * xr - x2i * xi, x2r * xi + x2i * xr
    nr, ni = 1 - xr, -xi
    den = x3r * x3r + x3i * x3i
    lr, li = (nr * x3r + ni * x3i) / den, (ni * x3r - nr * x3i) / den
    okl &= (lr, li) == (Fr(1, 4), Fr(-7, 4))
    lams.append('x=3/5+i/5: lam=%s%+si' % (lr, li))
    report('RX-list', okl, 'check_b6 的测试点：' + '；'.join(lams))
    print('time %.1fs' % (time.time() - t0w))
    print('SUMMARY s11-b6b rational_x pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
    return 0 if all(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
