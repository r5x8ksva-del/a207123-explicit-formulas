# -*- coding: utf-8 -*-
"""B13 / (★) 探索：notes/09 的被积函数 H(w,x) 在分支点附近的局部结构（2026-10-09）。

核对（数值，双精度）：
 (a) 用 p=1+u/(1-x)、q=1+u（u=τe^σ）时 H = (2-x)/((1-x)p) - (1-x)/q - x/q^2；
 (b) w - w_l(x) = (1-x)(p+log(1-p))（适当的 log 分支），w_l(x)=w_l° - x c_l + (1-x)log(1-x) + x；
 (c) 极点 q=0 处 Res_w H = 0，Res_w e^{-w/x^3}H = e^{-p_l(x)/x^3}；
 (d) 跳跃积分 Φ(y) 与渐近式 √(2π)(2-y)/√(1-y)·(−y^3)^{-1/2} 的比较；
 (e) τ=1 时三个立方根方向的主导性（余弦）。
用法：py -3.14 code/tableB/explore/explore_b13_local.py
"""
import cmath
import math
import random


def H_def(sig, x, tau):
    u = tau * cmath.exp(sig)
    g = 1 - x * x * u / (1 + u) ** 2
    return g / (1 - x + u)


def H_pq(sig, x, tau):
    u = tau * cmath.exp(sig)
    p = 1 + u / (1 - x)
    q = 1 + u
    return (2 - x) / ((1 - x) * p) - (1 - x) / q - x / q ** 2


def psi(sig, x, tau):
    return (1 - x) * sig + tau * (cmath.exp(sig) - 1)


def w_l(x, tau, l):
    c = math.log(1 / tau) + 1j * math.pi * (2 * l + 1)
    w0 = c - 1 - tau
    return w0 - x * c + (1 - x) * cmath.log(1 - x) + x


def p_l(x, tau, l):
    c = math.log(1 / tau) + 1j * math.pi * (2 * l + 1)
    return c - 1 - tau - x * c


def main():
    random.seed(1)
    # (a)
    worst = 0.0
    for _ in range(2000):
        x = complex(random.uniform(-.3, .3), random.uniform(-.3, .3))
        tau = math.exp(random.uniform(-3, 3))
        sig = complex(random.uniform(-3, 3), random.uniform(-4, 4))
        a, b = H_def(sig, x, tau), H_pq(sig, x, tau)
        worst = max(worst, abs(a - b) / max(1, abs(a)))
    print('(a) H partial fractions: max rel err %.2e' % worst)
    # (b): critical point sigma_c = log((1-x)/tau) + i pi (2l+1); check w - w_l = (1-x)(p+log(1-p)) up to 2πi(1-x)Z
    worst = 0.0
    for _ in range(2000):
        x = complex(random.uniform(-.3, .3), random.uniform(-.3, .3))
        tau = math.exp(random.uniform(-3, 3))
        l = random.randint(-3, 3)
        sc = cmath.log((1 - x) / tau) + 1j * math.pi * (2 * l + 1)
        e1 = abs(psi(sc, x, tau) - w_l(x, tau, l))
        sig = sc + complex(random.uniform(-.5, .5), random.uniform(-.5, .5))
        u = tau * cmath.exp(sig)
        p = 1 + u / (1 - x)
        lhs = psi(sig, x, tau) - w_l(x, tau, l)
        rhs = (1 - x) * (p + cmath.log(1 - p))
        d = (lhs - rhs) / (2j * math.pi * (1 - x))
        e2 = abs(d - round(d.real))
        sp = math.log(1 / tau) + 1j * math.pi * (2 * l + 1)
        e3 = abs(psi(sp, x, tau) - p_l(x, tau, l))
        worst = max(worst, e1, e2, e3)
    print('(b) critical value / pole value / w(p) relation: max err %.2e' % worst)
    # (c) residues on a small circle in sigma around the pole sigma_p = log(1/tau)+i pi
    for (x, tau) in [(0.05 + 0.03j, 1.0), (0.1 * cmath.exp(0.7j), 1.0), (0.08 - 0.02j, 3.0), (0.06j + 0.02, 0.2)]:
        sp = math.log(1 / tau) + 1j * math.pi
        r = 1e-3
        N = 4000
        s1 = s2 = 0
        for k in range(N):
            th = 2 * math.pi * (k + .5) / N
            sg = sp + r * cmath.exp(1j * th)
            dsg = 1j * r * cmath.exp(1j * th) * 2 * math.pi / N
            u = tau * cmath.exp(sg)
            g = 1 - x * x * u / (1 + u) ** 2
            s1 += g * dsg
            s2 += cmath.exp(-(psi(sg, x, tau) - p_l(x, tau, 0)) / x ** 3) * g * dsg
        res2 = s2 / (2j * math.pi)
        pred = 1.0  # 已在被积函数里除掉 e^{-p0/x^3}
        print('(c) x=%s tau=%g: Res_w H = %.1e ; Res e^{-w/x^3}H / e^{-p0/x^3} = %s'
              % (x, tau, abs(s1 / (2j * math.pi)), res2 / pred))
    # (d) jump integral Phi(y): integrate along steepest-descent rays from the saddle p=0 (small y only)
    th0 = cmath.phase(-2 + 1j * math.pi)
    for rad in [0.02, 0.04, 0.08]:
        for s in range(3):
            y = rad * cmath.exp(1j * (th0 / 3 + 2 * math.pi * s / 3))
            a = cmath.sqrt(y ** 3 / (1 - y))   # p = ± i a t  gives (1-y)p^2/(2y^3) = -t^2/2
            tot = 0
            M, T = 20000, 12.0
            for sgn in (1, -1):
                for k in range(M):
                    t = T * (k + .5) / M
                    p = sgn * 1j * a * t
                    dp = sgn * 1j * a * T / M
                    q = y + (1 - y) * p
                    om = (-(2 - y) / (1 - p) + (1 - y) ** 2 * p / ((1 - p) * q) + y * (1 - y) * p / ((1 - p) * q * q))
                    expo = -(1 - y) * (p + cmath.log(1 - p)) / y ** 3
                    tot += sgn * cmath.exp(expo) * om * dp
            Phi = tot / y ** 3
            pred = math.sqrt(2 * math.pi) * (2 - y) / cmath.sqrt(1 - y) * cmath.sqrt(-y ** 3) ** -1
            print('(d) |y|=%.2f s=%d: |Phi|=%.6e |pred|=%.6e ratio=%s' % (rad, s, abs(Phi), abs(pred), Phi / pred))
    # (e) dominance for tau=1, arg x = th0/3
    for s in range(3):
        c = math.cos(math.pi / 2 + 2 * math.pi * s / 3 - 2 * th0 / 3)
        print('(e) s=%d: cos = %.5f ; Re(1/y) sign: %+.3f' % (s, c, math.cos(th0 / 3 + 2 * math.pi * s / 3)))


if __name__ == '__main__':
    main()
