# -*- coding: utf-8 -*-
"""s15-b13 / C：notes/17 引理 1.6、引理 4.1（Stokes 跳跃）的独立数值核对（不导入项目代码）。

与作者 b13-jump 的区别：作者沿 p 平面的直线积分 ω(p)（用到引理 1.1、1.5、1.6 的局部参数化）；
这里 H 一律用原始定义 H=g/ψ'(σ)，σ 由沿道路的 Newton 延拓（自适应步长、按到临界点的距离限步）求主分支，
积分在 w 平面（换成 s=(w-w_0(y))/X）的 Hankel 围道上做，不用任何局部参数化。

记号：x=|x|e^{iφ/3}，y=ω^ν x（ν=0,1,2），X=x³=y³，w_0(y)=w_0°-y c_0+ε(y)，p_0(y)=w_0°-y c_0，
切口 Σ={w_0(y)+Xs: s>=0}，s_*=(p_0(y)-w_0(y))/X=-ε(y)/X。
  Φ_+(y):=∫_0^∞ e^{-s}(H_+-H_-)ds，H_± 是主分支在切口两侧（Im s≷0）的边界值；
  由留数定理，J(y)=I_{θ+}(y)-I_{θ-}(y)=e^{-w_0/X}Φ_+(y) - 2πi κ' X^{-1} e^{-p_0/X}，κ'∈{0,1} 表示 p_0(y) 是否是主分支的极点。
检查：
  c-l16      引理 1.6：x=0 时沿 s·w_0° 延拓得到的 W=τe^σ 落在 W_0 的值域 {|Im W|<π, Re W>-Im W·cot(Im W)} 内，
             且 p=W+1≈+√(2(1-s)w_0°)（主值平方根）→0；小 x 时径向延拓到 w_0(y) 附近得到的 p 是小的那一支
  c-phi      Φ_+(y) 与 √(2π)(2-y)(1-y)^{-1/2}(-y³)^{-1/2} 之比 → ±1（4 个 τ，3 个立方根方向，|x|=0.005…0.04），
             偏差 ∝|x|，Richardson 外推到 |x|=0 与 ±1 相差 <2e-3（即主项系数 2√(2π)，含因子 2-y）
  c-kappa    κ'(y)：绕 s_* 的小圆积分 (2πi)^{-1}∮e^{-(s-s_*)}H·X ds ∈{0,1}（引理 1.5 的值 1 也一并核对），
             并与“半平面判据”比较：κ'≠0 ⇔ Im(y·e^{-i(φ+π)/2})>0；预测 κ'(x)=0、κ'(ωx)=κ'(ω²x)=1
  c-full     中等 |x| 上的完整恒等式：两条射线上的 Laplace 积分直接相减（双精度能分辨的范围），
             与 e^{-w_0/X}Φ_+ - 2πiκ'X^{-1}e^{-p_0/X} 比较（τ=1；ν=0 时 κ'=0，另一个 ν 有 κ'=1）
  c-rev      反向检查：g≡1（去掉 x² 项）时 c-phi 的比值 → 1/2；从切口另一侧绕到 s_* 时 κ' 翻转；
             c-full 里漏掉极点项或主项时不再相等
用法：py -3.14 code/review/s15-b13/c_jump.py
"""
import cmath
import math
import sys
import time

import numpy as np

from s15_common import Reporter, setup_stdout

setup_stdout()
GL_X, GL_W = np.polynomial.legendre.leggauss(20)
W_E = 0.2784645427610738          # W(1/e)


# ------------------------------------------------------------------ 基本量
def c_l(tau, l=0):
    return math.log(1 / tau) + 1j * math.pi * (2 * l + 1)


def w_circ(tau, l=0):
    return c_l(tau, l) - 1 - tau


def eps(y):
    return (1 - y) * cmath.log(1 - y) + y


def w_l(y, tau, l=0):
    return w_circ(tau, l) - y * c_l(tau, l) + eps(y)


def p_l(y, tau, l=0):
    return w_circ(tau, l) - y * c_l(tau, l)


class Track:
    """沿直线段把 σ（ψ_y(σ)=w 的解）从当前点延拓到目标点；步长按到临界点的距离控制。"""

    def __init__(self, y, tau, drop_g=False):
        self.y, self.tau, self.drop_g = y, tau, drop_g
        self.w, self.s = 0j, 0j

    def psi(self, s):
        return (1 - self.y) * s + self.tau * (cmath.exp(s) - 1)

    def dpsi(self, s):
        return (1 - self.y) + self.tau * cmath.exp(s)

    def newton(self, w, s):
        # 收敛判据看残差（分支点附近 ψ' 很小，σ 本身到不了 1e-15 的相对精度）
        for _ in range(60):
            e = self.tau * cmath.exp(s)
            f = (1 - self.y) * s + e - self.tau - w
            scale = abs((1 - self.y) * s) + abs(e) + self.tau + abs(w)
            ds = f / ((1 - self.y) + e)
            s -= ds
            if abs(f) <= 32 * 2.2e-16 * scale or abs(ds) <= 1e-15 * (1 + abs(s)):
                e = self.tau * cmath.exp(s)
                s -= ((1 - self.y) * s + e - self.tau - w) / ((1 - self.y) + e)   # 再修正一步
                return s, True
        return s, False

    def move_to(self, wt):
        w0 = self.w
        if wt == w0:
            return self.s
        r, h = 0.0, 1.0
        while r < 1.0:
            h = min(h, 1.0 - r)
            last = r + h >= 1.0 - 1e-15
            wn = wt if last else w0 + (wt - w0) * (r + h)
            d = self.dpsi(self.s)
            sp = self.s + (wn - self.w) / d
            sn, ok = self.newton(wn, sp)
            u = self.tau * cmath.exp(self.s)
            crit = abs(d / u) if u != 0 else 1e300
            if ok and abs(sn - sp) <= 0.05 * crit + 1e-13 and abs(sn - self.s) <= 0.25 * min(crit, 1.0):
                self.w, self.s = wn, sn
                r = 1.0 if last else r + h
                h *= 2
            else:
                h /= 2
                if h < 1e-14:
                    raise RuntimeError('tracking failed near w=%s' % wn)
        return self.s

    def H(self):
        u = self.tau * cmath.exp(self.s)
        g = 1 if self.drop_g else 1 - self.y * self.y * u / (1 + u) ** 2
        return g / (1 - self.y + u)

    def p(self):
        return 1 + self.tau * cmath.exp(self.s) / (1 - self.y)


def seg_hits_ray(a, b, o, dvec):
    """线段 [a,b] 与射线 {o+t·dvec, t>=0} 是否相交（平面几何）。"""
    e = b - a
    den = (e.real * dvec.imag - e.imag * dvec.real)
    if abs(den) < 1e-300:
        return False
    oa = o - a
    lam = (oa.real * dvec.imag - oa.imag * dvec.real) / den
    t = (oa.real * e.imag - oa.imag * e.real) / den
    return 0 <= lam <= 1 and t >= 0


# ------------------------------------------------------------------ Hankel 围道上的 Φ_+
def nodes(a, b, n_panels):
    out = []
    edges = np.linspace(a, b, n_panels + 1)
    for i in range(n_panels):
        lo, hi = edges[i], edges[i + 1]
        for xg, wg in zip(GL_X, GL_W):
            out.append(((hi - lo) / 2 * xg + (hi + lo) / 2, (hi - lo) / 2 * wg))
    return out


def ray_nodes(T):
    out = []
    edges = [e for e in (0, 0.5, 1, 2, 3, 4, 6, 8, 11, 15, 20, 26, 33, 41) if e < T] + [T]
    for lo, hi in zip(edges[:-1], edges[1:]):
        for xg, wg in zip(GL_X, GL_W):
            out.append(((hi - lo) / 2 * xg + (hi + lo) / 2, (hi - lo) / 2 * wg))
    return out


def start_inner(y, tau, X, w0, sB, drop_g=False):
    """从 w=0 径向延拓到 w_0+X·sB（sB 为负实数，切口内侧）。核对线段不穿过切口。"""
    tr = Track(y, tau, drop_g)
    target = w0 + X * sB
    if seg_hits_ray(0j, target, w0, X):
        raise RuntimeError('radial segment crosses the cut')
    tr.move_to(target)
    return tr


def phi_plus(y, tau, phi, d=1.0, T=48.0, drop_g=False):
    X = y ** 3
    w0 = w_l(y, tau, 0)
    base = start_inner(y, tau, X, w0, -d, drop_g)
    s_base = base.s
    total = 0j
    for sgn in (+1, -1):            # +1：上侧（α 从 π 减到 π/2）；-1：下侧（α 从 π 增到 3π/2）
        tr = Track(y, tau, drop_g)
        tr.w, tr.s = base.w, s_base
        # 半圆
        a_lo, a_hi = (math.pi / 2, math.pi) if sgn > 0 else (math.pi, 3 * math.pi / 2)
        nd = nodes(a_lo, a_hi, 4)
        if sgn > 0:
            nd = nd[::-1]           # 从 π 往 π/2 走
        acc = 0j
        for a, wgt in nd:
            s = d * cmath.exp(1j * a)
            tr.move_to(w0 + X * s)
            acc += cmath.exp(-s) * tr.H() * (1j * s) * wgt
        # 半圆部分在 Φ_+ 里的符号：-∫_{π/2}^{3π/2}
        total -= acc
        # 射线
        tr.move_to(w0 + X * (sgn * 1j * d))
        acc = 0j
        for t, wgt in ray_nodes(T):
            s = t + sgn * 1j * d
            tr.move_to(w0 + X * s)
            acc += cmath.exp(-s) * tr.H() * wgt
        total += sgn * acc
    return total


def phi_pred(y, factor=None):
    f = (2 - y) if factor is None else factor
    return math.sqrt(2 * math.pi) * f / cmath.sqrt(1 - y) / cmath.sqrt(-y ** 3)


# ------------------------------------------------------------------ κ'
def kappa(y, tau, wrong_side=False, M=400):
    X = y ** 3
    w0 = w_l(y, tau, 0)
    sst = -eps(y) / X
    rho = min(2.0, 0.3 * abs(sst))
    rb = abs(sst) + 2 * rho
    ang = cmath.phase(sst) % (2 * math.pi)          # ∈[0,2π)
    tr = start_inner(y, tau, X, w0, -rb)
    # 沿 |s|=rb 从 π 走到 ang，不穿过角度 0（正实轴=切口）；wrong_side 时故意从另一边绕
    if not wrong_side:
        path = np.linspace(math.pi, ang, 400)
    else:
        target = ang - 2 * math.pi if ang > math.pi else ang + 2 * math.pi
        path = np.linspace(math.pi, target, 400)
    for a in path[1:]:
        tr.move_to(w0 + X * rb * cmath.exp(1j * a))
    tr.move_to(w0 + X * (sst + rho * cmath.exp(1j * ang)))
    acc = 0j
    for k in range(M):
        b = 2 * math.pi * (k + 0.5) / M
        s = sst + rho * cmath.exp(1j * (ang + b))
        tr.move_to(w0 + X * s)
        ds = 1j * rho * cmath.exp(1j * (ang + b)) * 2 * math.pi / M
        acc += cmath.exp(-(s - sst)) * tr.H() * X * ds
    return acc / (2j * math.pi)


def kappa_halfplane(y, phi):
    D = cmath.exp(1j * (phi + math.pi) / 2)
    return 1 if (y / D).imag > 0 else 0


# ------------------------------------------------------------------ 射线积分（中等 |x|）
def ray_integral(y, tau, theta, phi):
    X = y ** 3
    rate = math.cos(theta - phi) / abs(X)
    L = 52.0 / rate
    tr = Track(y, tau)
    e = cmath.exp(1j * theta)
    acc = 0j
    edges = np.linspace(0, L, 105)
    for lo, hi in zip(edges[:-1], edges[1:]):
        for xg, wg in zip(GL_X, GL_W):
            rr = (hi - lo) / 2 * xg + (hi + lo) / 2
            tr.move_to(rr * e)
            acc += cmath.exp(-rr * e / X) * tr.H() * e * (hi - lo) / 2 * wg
    return acc / X


def sector_ok(y, tau, th_lo, th_hi, Lmax=60, cut_exp=40.0):
    """扇形 [th_lo, th_hi] 内除 w_0(y)、p_0(y) 外没有“看得见”的 S(y) 点（|l|<=Lmax）。
    Re(z/X)>cut_exp 的点贡献 <=|X|^{-1}e^{-40}<2e-17（这里 |J|~1e-7，相对 <1e-9），在双精度比较里不可见，跳过并计数。
    返回 (ok, 最近的外点的角距, 被跳过的扇形内远点个数)。"""
    X = y ** 3
    worst, skipped = 1e9, 0
    for l in range(-Lmax, Lmax + 1):
        for z, is0 in ((w_l(y, tau, l), l == 0), (p_l(y, tau, l), l == 0)):
            a = cmath.phase(z)
            if is0:
                if not (th_lo < a < th_hi):
                    return False, -1, skipped
                continue
            inside = th_lo <= a <= th_hi
            if inside and (z / X).real > cut_exp:
                skipped += 1
                continue
            if inside:
                return False, -1, skipped
            wrap = lambda d: abs((d + math.pi) % (2 * math.pi) - math.pi)
            worst = min(worst, wrap(a - th_lo), wrap(a - th_hi))
    return True, worst, skipped


def main():
    rep = Reporter('s15_c_jump')
    t0 = time.time()

    # ---- c-l16
    ok16, info16 = True, []
    for tau in (0.1, W_E, 1.0, 3.0, 30.0):
        wc = w_circ(tau)
        tr = Track(0.0, tau)
        maxviol = 0.0
        for sp in list(np.linspace(0, 0.99, 100)) + [1 - 10 ** (-k) for k in range(3, 9)]:
            tr.move_to(sp * wc)
            W = tau * cmath.exp(tr.s)
            a, b = W.real, W.imag
            # W_0 的值域：|b|<π 且 a>-b·cot b（b=0 时 a>-1）
            if abs(b) < 1e-12:
                inside = a > -1
            else:
                inside = abs(b) < math.pi and a > -b / math.tan(b)
            Z = tau * cmath.exp(sp * wc + tau)
            maxviol = max(maxviol, abs(W * cmath.exp(W) - Z) / max(1, abs(Z)))
            ok16 &= inside
        sp = 1 - 1e-8
        pp = tau * cmath.exp(tr.s) + 1
        pred = cmath.sqrt(2 * (1 - sp) * wc)
        rel = abs(pp - pred) / abs(pred)
        ok16 &= maxviol < 1e-12 and rel < 1e-3
        info16.append('τ=%.4g:|p/√(2(1-s)w_0°)-1|=%.1e' % (tau, rel))
    # 小 x：径向延拓到 w_0(y)-X·d 得到的 p 与 ±V√(-d)，V=(-2X/(1-y))^{1/2}，是小的那一支
    oks = True
    for tau in (W_E, 1.0, 3.0):
        phi = cmath.phase(w_circ(tau))
        for rad in (0.01, 0.03):
            for nu in range(3):
                y = rad * cmath.exp(1j * (phi / 3 + 2 * math.pi * nu / 3))
                X = y ** 3
                tr = start_inner(y, tau, X, w_l(y, tau), -1.0)
                pp = tr.p()
                small = math.sqrt(2 * abs(X) / abs(1 - y))
                oks &= abs(abs(pp) / small - 1) < 0.05
    rep.check('c-l16', ok16 and oks, 'x=0：沿 s·w_0° 的延拓都在 W_0 值域内、We^W=Z，p≈+√(2(1-s)w_0°)（主值）：%s；'
              '小 x（3 个 τ，|x|=0.01、0.03，三个方向）径向到 w_0(y)-X 时 |p|≈√(2|X|/|1-y|)（小的一支）%s'
              % ('，'.join(info16), oks))

    # ---- c-phi
    t1 = time.time()
    ok_phi = True
    lines = []
    extrap_err = 0.0
    for tau in (0.1, W_E, 1.0, 3.0):
        phi = cmath.phase(w_circ(tau))
        for nu in range(3):
            rs = (0.005, 0.01, 0.02, 0.04)
            ratios = []
            for rad in rs:
                y = rad * cmath.exp(1j * (phi / 3 + 2 * math.pi * nu / 3))
                ratios.append(phi_plus(y, tau, phi) / phi_pred(y))
            sgn = 1 if ratios[0].real > 0 else -1
            devs = [abs(r - sgn) for r in ratios]
            lin = all(0.3 < devs[i] / rs[i] / (devs[-1] / rs[-1]) < 3 for i in range(3))
            r0 = 2 * ratios[0] - ratios[1]            # Richardson（偏差 ∝|x|）
            extrap_err = max(extrap_err, abs(r0 - sgn))
            ok_phi &= all(devs[i] < devs[i + 1] for i in range(3)) and devs[0] < 0.02 and lin and abs(r0 - sgn) < 2e-3
            lines.append('τ=%.3g ν=%d 号%+d 偏差 %s 外推 %.1e' % (tau, nu, sgn, '/'.join('%.4f' % v for v in devs), abs(r0 - sgn)))
    rep.check('c-phi', ok_phi, 'Φ_+(y)/[√(2π)(2-y)(1-y)^{-1/2}(-y³)^{-1/2}] → ±1，偏差在 |x|=0.005,0.01,0.02,0.04 上单调且 ∝|x|，外推最大误差 %.1e（%.1f s）'
              % (extrap_err, time.time() - t1))
    for ln in lines:
        rep.info('c-phi ' + ln)

    # ---- c-kappa
    t1 = time.time()
    ok_k, kl = True, []
    for tau in (0.1, W_E, 1.0, 3.0):
        phi = cmath.phase(w_circ(tau))
        for nu in range(3):
            for rad in (0.01, 0.03):
                y = rad * cmath.exp(1j * (phi / 3 + 2 * math.pi * nu / 3))
                kv = kappa(y, tau)
                kr = round(kv.real)
                good_int = abs(kv - kr) < 1e-6 and kr in (0, 1)
                pred = kappa_halfplane(y, phi)
                ok_k &= good_int and kr == pred
                if rad == 0.01:
                    kl.append('τ=%.3g ν=%d κ\'=%d(|偏差| %.0e)' % (tau, nu, kr, abs(kv - kr)))
    rep.check('c-kappa', ok_k, '小圆积分得到的 κ\' 都是 0 或 1（值为 1 时即引理 1.5 的留数 e^{-p_0/X}），且与半平面判据一致；'
              '4 个 τ×3 个方向×|x|=0.01,0.03：%s（%.1f s）' % ('；'.join(kl), time.time() - t1))

    # ---- c-full：中等 |x| 的完整恒等式（τ=1）
    t1 = time.time()
    tau = 1.0
    phi = cmath.phase(w_circ(tau))
    ok_full, fl = True, []
    full_cases = [(0, 0.5, 0.45), (1, 0.65, 0.45), (2, 0.62, 0.55)]
    stash = []
    for nu, rad, eta in full_cases:
        y = rad * cmath.exp(1j * (phi / 3 + 2 * math.pi * nu / 3))
        X = y ** 3
        th_m, th_p = phi - eta, phi + eta
        geo, margin, skipped = sector_ok(y, tau, th_m, th_p)
        w0 = w_l(y, tau)
        p0 = p_l(y, tau)
        sst = (p0 - w0) / X
        # Hankel 宽度：不能把 s_* 夹在围道与切口之间
        dist_cut = abs(sst.imag) if sst.real > 0 else abs(sst)
        d = min(1.0, 0.4 * dist_cut)
        Phi = phi_plus(y, tau, phi, d=d, T=22.0)      # e^{-22}≈3e-10 的截断；切口不伸到 w_1(y) 附近
        kv = kappa(y, tau)
        kr = round(kv.real)
        Jpred = cmath.exp(-w0 / X) * Phi - 2j * math.pi * kr * cmath.exp(-p0 / X) / X
        Ip = ray_integral(y, tau, th_p, phi)
        Im_ = ray_integral(y, tau, th_m, phi)
        Jdir = Ip - Im_
        rel = abs(Jdir - Jpred) / abs(Jpred)
        ok_full &= geo and rel < 1e-5 and abs(kv - kr) < 1e-6
        stash.append((Jdir, Jpred, cmath.exp(-w0 / X) * Phi, 2j * math.pi * kr * cmath.exp(-p0 / X) / X, kr))
        fl.append('ν=%d |x|=%.2f η=%.2f：扇形里只有 w_0,p_0 %s（外点最小角距 %.2f；扇形内贡献<e^{-40} 的远点 %d 个）；|J|=%.2e，|I_θ|≈%.2f，κ\'=%d，相对差 %.1e'
                  % (nu, rad, eta, geo, margin, skipped, abs(Jdir), abs(Ip), kr, rel))
    rep.check('c-full', ok_full, '两条射线的积分直接相减 = 切口积分 + 极点项：' + '；'.join(fl) + '（%.1f s）' % (time.time() - t1))

    # ---- c-rev
    t1 = time.time()
    tau = 1.0
    phi = cmath.phase(w_circ(tau))
    rr = []
    for rad in (0.005, 0.01, 0.02):
        y = rad * cmath.exp(1j * phi / 3)
        rr.append(phi_plus(y, tau, phi, drop_g=True) / phi_pred(y))
    half = all(abs(abs(r) - 0.5) < 0.02 for r in rr)
    flips = True
    for nu in range(3):
        y = 0.02 * cmath.exp(1j * (phi / 3 + 2 * math.pi * nu / 3))
        k1 = round(kappa(y, tau).real)
        k2v = kappa(y, tau, wrong_side=True)
        flips &= abs(k2v - (1 - k1)) < 1e-6
    # c-full 的两种漏项
    miss = True
    for Jdir, Jpred, main_t, pole_t, kr in stash:
        if kr == 1:
            miss &= abs(Jdir - main_t) / abs(Jdir) > 1e-3        # 漏掉极点项
        miss &= abs(Jdir - (-pole_t)) / abs(Jdir) > 1e-3         # 漏掉切口（主）项
    rep.check('c-rev', half and flips and miss, '反向检查：g≡1 时 |Φ_+/预测| = %s（应 →1/2）%s；从切口另一侧绕到 s_* 时 κ\' 翻转（三个方向）%s；'
              'c-full 漏掉极点项或主项时相对差 >1e-3 %s（%.1f s）'
              % ('/'.join('%.3f' % abs(r) for r in rr), half, flips, miss, time.time() - t1))

    print('（总用时 %.1f s）' % (time.time() - t0))
    return rep.summary()


if __name__ == '__main__':
    sys.exit(main())
