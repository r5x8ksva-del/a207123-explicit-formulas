# -*- coding: utf-8 -*-
"""s9-b7 独立核对 R0-R3：解析延拓 I(x,t) 的两种互相独立的算法，在 |arg x|>pi/6 的复 x 上彼此比较，并与 F 的部分和比较。

不导入项目里的任何模块（不导入 check_b7_borel.py）。numpy 双精度。f_k(t) 用 h_k 多项式递推精确算出
（与 s9b7_formal.py 里的同一递推；那里已对原始定义核对过）。

算法一（w 射线，notes/09 §2 的公式，自己实现）：I_phi(x)=x^{-3} int_0^{inf e^{i phi}} e^{-w/x^3} H(w,x) dw，
  s_x(w) 沿射线用 RK4 + Newton 延拓（标量 cmath），变量 u = r cos(phi-arg x^3)/|x|^3，复合 Gauss-Legendre；
  面板数按振荡率 tan|phi-arg x^3| 自适应（每个振荡周期至少约 40 个节点）。
算法二（sigma 平面直接变形积分路径，不求反函数）：I = x^{-3} int_P exp(-psi_x(s)/x^3) g_x(-tau e^s) ds，
  P = 0 -> p_a（s=0 处的最速下降方向，走到 Re(psi e^{-i arg x^3})/|x|^3 约 80）-> p1 -> 水平到 +inf；
  Im s 始终在 (-pi+0.3, pi-0.3) 内，不跨过 g 的极点 Im s = ±pi；p1 在候选里挑，使 Re(psi_x(s) e^{-i arg x^3})
  在后两段上尽量大（被积函数不放大）。对 |arg x|<pi/6 这就是原定义的实轴积分（Cauchy）；对更大的 |arg x|，
  只要尾巴留在同一个谷（cos(Im s - arg x^3)>0）且路径留在带形 |Im s|<pi 内，它就是同一个解析延拓。

R0  实 x：原定义的实轴 sigma 积分 = 算法一（phi=0）= 算法二
R1  定理的区域内（|x|=3r0/8；arg x 取 0、略大于 pi/6、S'_eps 的边（eps=delta/4）、接近 S 的边）：
    两种算法一致、两条不同射线一致，且与部分和 sum_{k<K} f_k x^k 一致
    （|x|<=3/64 时级数的最优截断误差远小于双精度，所以这一条检验的是「延拓出来的函数确实以 F 为展开」与分支选择）
R2  定理区域之外（|x|=0.2–0.5，arg x 到 0.7>pi/6；佐证，定理不声称）：
    算法一的 sigma 路径若留在带形 |Im s|<pi 内，两种算法应一致；最小项大于 1e-13 时报告最优截断误差 / 最小项
R3  反向检查：若把 H 里的 g_x 换成 1（丢掉 x^2 项），在 R1 的点上与部分和的差必须远大于舍入误差
"""
import cmath
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


def params(tau):
    r0 = min(1 / 8, tau / 2)
    tand = min(1.0, tau / 3)
    return r0, tand, math.atan(tand)


# ---------------- f_k ----------------
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


HS = h_polys(400)


def f_float(t, K):
    """f_k(t)=h_k(t)/(1-t)^{k+1}，t=p/q：整数运算，最后一次整数除法转成双精度（正确舍入）。"""
    t = Fr(t)
    p, q = t.numerator, t.denominator
    out = []
    for k in range(K + 1):
        cs = HS[k]
        d = len(cs) - 1
        v = sum(cs[i] * p ** i * q ** (d - i) for i in range(d + 1))
        out.append((v * q ** (k + 1 - d)) / ((q - p) ** (k + 1)))
    return np.array(out, dtype=float)


# ---------------- 被积函数 ----------------
def cexpm1(z):
    if abs(z) < 1e-3:
        return z * (1 + z / 2 * (1 + z / 3 * (1 + z / 4 * (1 + z / 5))))
    return cmath.exp(z) - 1


def psi_np(s, x, tau):
    return (1 - x) * s + tau * np.expm1(s)


def gx_np(z, x, drop=False):
    if drop:
        return np.ones_like(z)
    return 1 + x * x * z / (1 - z) ** 2


GLX, GLW = np.polynomial.legendre.leggauss(20)


def panels(edges):
    edges = np.asarray(edges, dtype=float)
    a, b = edges[:-1], edges[1:]
    nodes = ((b - a)[:, None] / 2 * GLX[None, :] + (a + b)[:, None] / 2).ravel()
    wts = ((b - a)[:, None] / 2 * GLW[None, :]).ravel()
    return nodes, wts


# ---------------- 算法一：w 射线 ----------------
def cont_ray(x, tau, e, rs):
    a = 1 - x
    s = 0j
    out = np.empty(len(rs), dtype=complex)
    rp = 0.0
    for i, r in enumerate(rs):
        h = r - rp
        k1 = e / (a + tau * cmath.exp(s))
        k2 = e / (a + tau * cmath.exp(s + h / 2 * k1))
        k3 = e / (a + tau * cmath.exp(s + h / 2 * k2))
        k4 = e / (a + tau * cmath.exp(s + h * k3))
        s += h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        tgt = r * e
        for _ in range(5):
            em = cexpm1(s)
            f = a * s + tau * em - tgt
            st = f / (a + tau * (em + 1))
            s -= st
            if abs(st) < 1e-16 * (1 + abs(s)):
                break
        out[i] = s
        rp = r
    return out


def I_ray(x, tau, phi, drop=False, U=50.0):
    x = complex(x)
    th = cmath.phase(x ** 3)
    c = math.cos(phi - th)
    if c <= 0:
        raise ValueError('ray does not decay')
    T = abs(math.tan(phi - th))
    npan = max(100, int(math.ceil(U * T / (2 * math.pi) * 2)))
    kappa = c / abs(x) ** 3
    u, wu = panels(np.linspace(0, U, npan + 1))
    r = u / kappa
    e = cmath.exp(1j * phi)
    sig = cont_ray(x, tau, e, r)
    w = r * e
    H = gx_np(-tau * np.exp(sig), x, drop) / ((1 - x) + tau * np.exp(sig))
    val = np.sum(wu * np.exp(-w / x ** 3) * H) * e / x ** 3 / kappa
    return complex(val), float(np.abs(sig.imag).max()), npan


# ---------------- 算法二：sigma 平面路径 ----------------
def I_sigma_path(x, tau, drop=False):
    x = complex(x)
    X3 = x ** 3
    ax3 = abs(X3)
    th = cmath.phase(X3)
    rot = cmath.exp(-1j * th)
    c0 = 1 - x + tau
    th_sd = th - cmath.phase(c0)
    Aa = min(0.4, 80 * ax3 / abs(c0))
    pa = Aa * cmath.exp(1j * th_sd)
    Phi = lambda s: (psi_np(s, x, tau) * rot).real
    best = None
    for B in (0.3, 0.6, 1.0, 1.5, 2.0, 3.0, 4.0):
        for t2 in np.linspace(-1.5, 1.5, 61):
            p1 = pa + B * cmath.exp(1j * t2)
            if abs(p1.imag) > math.pi - 0.3 or math.cos(p1.imag - th) < 0.2:
                continue
            seg = pa + (p1 - pa) * np.linspace(0, 1, 300)
            tail = p1 + np.linspace(0, 6, 300)
            sc = min(Phi(seg).min(), Phi(tail).min())
            if best is None or sc > best[0]:
                best = (sc, p1)
    sc, p1 = best
    # 段 1：几何加密
    lmin = 1e-4 * ax3 / abs(c0) / max(Aa, 1e-300)
    l1, w1 = panels(np.concatenate([[0.0], np.geomspace(min(lmin, 0.5), 1.0, 150)]))
    s1 = l1 * pa
    v = np.sum(w1 * np.exp(-psi_np(s1, x, tau) / X3) * gx_np(-tau * np.exp(s1), x, drop)) * pa
    # 段 2：均匀
    l2, w2 = panels(np.linspace(0, 1, 401))
    s2 = pa + l2 * (p1 - pa)
    v += np.sum(w2 * np.exp(-psi_np(s2, x, tau) / X3) * gx_np(-tau * np.exp(s2), x, drop)) * (p1 - pa)
    # 尾巴
    cb = math.cos(p1.imag - th)
    Ut = max(2.0, math.log(max(800 * ax3 / (tau * cb), 1e-300)) - p1.real + 3.0)
    u, wu = panels(np.linspace(0, Ut, 600))
    s3 = p1 + u
    v += np.sum(wu * np.exp(-psi_np(s3, x, tau) / X3) * gx_np(-tau * np.exp(s3), x, drop))
    return complex(v / X3), p1, sc / ax3


def I_real_sigma(x, tau):
    """原定义（实 x）：实轴 sigma 积分，几何加密网格。"""
    X3 = x ** 3
    scale = X3 / (1 - x + tau)
    edges = np.concatenate([[0.0], np.geomspace(1e-4 * scale, 200 * scale, 200)])
    s, ws = panels(edges)
    f = np.exp(-psi_np(s, x, tau) / X3) * gx_np(-tau * np.exp(s), x)
    return float(np.sum(ws * f) / X3)


def partial_sums(fk, x):
    terms = fk * x ** np.arange(len(fk))
    return np.cumsum(terms), np.abs(terms)


def main():
    t0 = time.time()
    fk_cache = {}

    def fk(t):
        if t not in fk_cache:
            fk_cache[t] = f_float(t, 400)
        return fk_cache[t]

    # R0
    info = []
    ok = True
    for tau in (0.5, 3.0):
        for x in (0.04, 0.2, 0.45):
            a = I_real_sigma(x, tau)
            b = I_ray(x, tau, 0.0)[0]
            c = I_sigma_path(x, tau)[0]
            ra, rc = abs(b - a) / abs(a), abs(c - a) / abs(a)
            ok = ok and ra < 1e-13 and rc < 1e-13
            info.append('tau=%g,x=%g:%.0e/%.0e' % (tau, x, ra, rc))
    report('R0', ok, '实 x：实轴 sigma 积分 vs 算法一 / 算法二（相对差）%s' % ', '.join(info))

    # R1 定理区域内
    ok = True
    rows = []
    for tau, tt in ((0.5, Fr(-1, 2)), (3.0, Fr(-3)), (20.0, Fr(-20)), (0.1, Fr(-1, 10))):
        r0, tand, delta = params(tau)
        eps = delta / 4
        a_edge = (np.pi / 2 + delta / 2 - eps) / 3      # S'_eps 的边
        a_S = 0.98 * (np.pi / 2 + delta) / 3             # 0.98 倍 S 的边（tau=0.5、3、20 时在 S'_eps 外；tau=0.1 时 delta 太小，仍在 S'_eps 内）
        F = fk(tt)
        for alpha in (0.0, np.pi / 6 + 0.002, a_edge, -a_edge, a_S, -a_S):
            x = 3 * r0 / 8 * np.exp(1j * alpha)
            th = 3 * alpha
            lo, hi = max(-delta, th - np.pi / 2), min(delta, th + np.pi / 2)
            # 射线 A：允许区间里最接近 th 的方向（条件最好）；射线 B：|arg x|<=a_edge 时用证明 §3 的取法，否则取区间中点
            phiA = min(max(th, lo + 0.02 * (hi - lo)), hi - 0.02 * (hi - lo))
            if abs(alpha) <= a_edge + 1e-12:
                phiB = math.copysign(min(abs(th), delta / 2), th)
                if abs(phiB - phiA) < 1e-3 * delta:
                    phiB = lo + 0.3 * (hi - lo) if phiA > (lo + hi) / 2 else hi - 0.3 * (hi - lo)
            else:
                phiB = (lo + hi) / 2
            vA, imA, nA = I_ray(x, tau, phiA)
            vB, imB, nB = I_ray(x, tau, phiB)
            vP, p1, sc = I_sigma_path(x, tau)
            S = partial_sums(F[:120], x)[0][-1]
            dAB = abs(vA - vB) / abs(vA)
            dAP = abs(vA - vP) / abs(vA)
            dS = abs(vA - S) / abs(vA)
            good = dAB < 1e-12 and dAP < 1e-12 and dS < 1e-12 and max(imA, imB) < np.pi / 2
            ok = ok and good
            rows.append('t=%s |x|=%.4g arg=%.4f phi=%.3f/%.3f(面板 %d/%d): 两射线 %.0e, 射线vs路径 %.0e, vs部分和 %.0e%s'
                        % (tt, abs(x), alpha, phiA, phiB, nA, nB, dAB, dAP, dS, '' if good else ' <-- FAIL'))
    report('R1', ok, '定理区域内（|x|=3r0/8；pi/6=0.5236）：' + '; '.join(rows))

    # R2 区域外
    rows = []
    ok = True
    nsame = 0
    for tau, tt in ((0.5, Fr(-1, 2)), (2.0, Fr(-2)), (3.0, Fr(-3)), (0.1, Fr(-1, 10))):
        F = fk(tt)
        for rad in (0.2, 0.35, 0.5):
            for alpha in (0.3, 0.6, 0.7):
                x = rad * np.exp(1j * alpha)
                th = 3 * alpha
                phi = min(max(th - np.pi / 2 + 0.6, -1.2), 1.2)
                v1, im1, n1 = I_ray(x, tau, phi)
                vP, p1, sc = I_sigma_path(x, tau)
                d = abs(v1 - vP) / abs(vP)
                in_strip = im1 < np.pi
                if in_strip:
                    nsame += 1
                    ok = ok and d < 1e-10
                ps, at = partial_sums(F, x)
                err = np.abs(ps - vP)
                kmin = int(np.argmin(at))
                extra = ''
                if at[kmin] > 1e-13 * abs(vP):
                    kopt = int(np.argmin(err))
                    extra = '; 最优截断 K=%d 误差 %.1e，最小项(k=%d) %.1e，比 %.2g' % (kopt, err[kopt], kmin, at[kmin], err[kopt] / at[kmin])
                else:
                    extra = '; 部分和(K<=400) 与 I 的最小差 %.0e（最小项低于双精度）' % (err.min() / abs(vP))
                rows.append('t=%s x=%.2fe^{%.2fi}: 射线 phi=%.2f 的 max|Im s|=%.2f%s，射线vs路径 %.0e%s'
                            % (tt, rad, alpha, phi, im1, '' if in_strip else '(离开带形)', d, extra))
    report('R2', ok, '定理区域外（佐证，定理不声称；%d 个点中射线的 sigma 路径留在带形内的 %d 个，两种算法都一致到 1e-10）：' % (36, nsame)
           + '; '.join(rows))

    # R3 反向检查
    info = []
    ok = True
    for tau, tt in ((0.5, Fr(-1, 2)), (3.0, Fr(-3))):
        r0, tand, delta = params(tau)
        F = fk(tt)
        alpha = (np.pi / 2 + delta / 4) / 3
        x = 3 * r0 / 8 * np.exp(1j * alpha)
        vb = I_ray(x, tau, min(3 * alpha, 0.98 * delta), drop=True)[0]
        S = partial_sums(F[:120], x)[0][-1]
        d = abs(vb - S) / abs(S)
        ok = ok and d > 1e-6
        info.append('t=%s: %.1e' % (tt, d))
    report('R3', ok, '反向检查：g_x 换成 1 后与部分和的相对差（应远大于舍入）%s' % ', '.join(info))

    print('time %.1fs' % (time.time() - t0))
    n = sum(RES)
    print('SUMMARY s9b7_rays pass=%d fail=%d' % (n, len(RES) - n))
    return 0 if n == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
