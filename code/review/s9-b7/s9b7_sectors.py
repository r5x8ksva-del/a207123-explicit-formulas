# -*- coding: utf-8 -*-
"""s9-b7 信息性核对 Q1：notes/09 把扇形写成 {|arg x^3| < pi/2+delta}；按字面这是三个扇形
（arg x 在 0、2pi/3、4pi/3 附近）。这里看「另外两个扇形」里同一个积分公式的行为，说明字面读法无害：
在 |arg x - 2pi/3| < pi/6 上，原定义的实轴 sigma 积分 J(x)=x^{-3} int_0^inf exp(-psi_x(s)/x^3) g_x(-tau e^s) ds 收敛
（只依赖 x^3），而且同样以 F=sum f_k x^k 为渐近展开（§3 的推导只用到 x^3 与 |x|）。

不导入项目里的任何模块。

Q1  x = r e^{i(2pi/3 + a)}（|a|<pi/6）：实轴 sigma 积分与部分和 sum_{k<K} f_k x^k 比较（r=0.05、0.15、0.25）
Q2  同一点上 J(x) 与「主扇形的函数在 x 处的值」根本不是一回事：主扇形的 I 在 arg x=2pi/3 附近没有定义；
    这里只报告 J(x) 与 J(conj x) 的共轭关系（实系数级数的对称性），作为数值自洽检查
"""
import math
import sys
import time
from fractions import Fraction as Fr

import numpy as np

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def h_polys(K):
    h = [[1], [1], [1, 1]]
    for k in range(3, K + 1):
        q = h[k - 3]
        der = [i * q[i] for i in range(1, len(q))] or [0]
        d = padd(padd(der, [0] + [-c for c in der]), [(k - 2) * c for c in q])
        h.append(padd(h[k - 1], padd([0] + d, [0, 0] + [-c for c in d])))
    return h


HS = h_polys(300)


def f_float(t, K):
    t = Fr(t)
    p, q = t.numerator, t.denominator
    out = []
    for k in range(K + 1):
        cs = HS[k]
        d = len(cs) - 1
        v = sum(cs[i] * p ** i * q ** (d - i) for i in range(d + 1))
        out.append((v * q ** (k + 1 - d)) / ((q - p) ** (k + 1)))
    return np.array(out, dtype=float)


GLX, GLW = np.polynomial.legendre.leggauss(20)


def panels(edges):
    edges = np.asarray(edges, dtype=float)
    a, b = edges[:-1], edges[1:]
    return (((b - a)[:, None] / 2 * GLX[None, :] + (a + b)[:, None] / 2).ravel(),
            ((b - a)[:, None] / 2 * GLW[None, :]).ravel())


def J_real_axis(x, tau):
    x = complex(x)
    X3 = x ** 3
    c = math.cos(np.angle(X3))
    scale = abs(X3) / abs(1 - x + tau)
    # 实轴积分：被积函数 |exp(-psi/x^3)| 的衰减由 Re((1-x+tau)s/x^3) 与 Re(tau e^s/x^3) 控制
    smax = max(60 * scale / max(c, 1e-3), math.log(max(1.0, 800 * abs(X3) / (tau * max(c, 1e-3)))) + 3)
    edges = np.concatenate([[0.0], np.geomspace(1e-5 * scale, smax, 400)])
    s, ws = panels(edges)
    psi = (1 - x) * s + tau * np.expm1(s)
    f = np.exp(-psi / X3) * (1 + x * x * (-tau * np.exp(s)) / (1 + tau * np.exp(s)) ** 2)
    return complex(np.sum(ws * f) / X3)


def main():
    t0 = time.time()
    rows = []
    ok = True
    for tau, tt in ((3.0, Fr(-3)), (0.5, Fr(-1, 2))):
        F = f_float(tt, 300)
        for r in (0.05, 0.15, 0.25):
            for a in (0.0, 0.3, -0.3):
                x = r * np.exp(1j * (2 * np.pi / 3 + a))
                J = J_real_axis(x, tau)
                terms = F * x ** np.arange(len(F))
                ps = np.cumsum(terms)
                err = np.abs(ps - J) / abs(J)
                kmin = int(np.argmin(np.abs(terms)))
                good = err.min() < 1e-12
                ok = ok and good
                rows.append('t=%s x=%.2fe^{i(2pi/3%+.1f)}: min_K|J-S_K|/|J|=%.0e（K=%d），|J|=%.4f%s'
                            % (tt, r, a, err.min(), int(np.argmin(err)), abs(J), '' if good else ' <-- FAIL'))
    report('Q1', ok, '在 arg x≈2pi/3 的扇形里，原定义的实轴积分同样以 F 为渐近展开：' + '; '.join(rows))
    # Q2 共轭对称
    x = 0.15 * np.exp(1j * (2 * np.pi / 3 + 0.2))
    J1 = J_real_axis(x, 3.0)
    J2 = J_real_axis(np.conj(x), 3.0)
    d = abs(J1 - np.conj(J2)) / abs(J1)
    report('Q2', d < 1e-13, 'J(conj x)=conj J(x)：相对差 %.0e' % d)
    print('time %.1fs' % (time.time() - t0))
    n = sum(RES)
    print('SUMMARY s9b7_sectors pass=%d fail=%d' % (n, len(RES) - n))
    return 0 if n == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
