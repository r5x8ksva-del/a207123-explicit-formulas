# -*- coding: utf-8 -*-
"""表 B 的 B13（t<0 部分）与 B9 的 (★)：t<0 时 f_k(t) 的精确 Gevrey 常数的核对脚本（2026-10-09）。
证明见 notes/17-主Agent-表B-B13-t小于0的Gevrey常数.md。

逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b13 pass=<n> fail=<n>」。
记号：τ=-t>0，u=τe^σ，p=1+u/(1-x)，q=1+u=x+(1-x)p，c_l=ln(1/τ)+iπ(2l+1)，w_l°=c_l-1-τ，
ε(x)=(1-x)ln(1-x)+x，w_l(x)=w_l°-x c_l+ε(x)，p_l(x)=w_l°-x c_l，p_*=-x/(1-x)，R=|w_0°|。
需要 numpy（b13-coef 的二维 FFT 与 b13-jump 的数值积分）。
用法：py -3.14 code/tableB/check_b13.py（约 1 秒）
  b13-alg    引理 1.1（精确，Fraction）：H=g/(1-x+u)，g=1-x^2u/(1+u)^2，等于 (2-x)/((1-x)p)-(1-x)/q-x/q^2；
             引理 1.5（精确）：ω=H·dw/dp 在 p_* 处 a_1=0（Res_w H=0），a_2·(-w'(p_*)/x^3)=1（Res e^{-w/x^3}H=e^{-p_0/x^3}）
  b13-wp     引理 1.2（数值）：w_l(x)、p_l(x) 分别是临界值 ψ_x(σ_c)、极点值 ψ_x(σ_p)；G(p)=(1-p)e^p=e^{(w-w_l(x))/(1-x)}；
             w(p_*)=p_l(x)；|ε(x)|<=0.62|x|^2（|x|<=1/2）
  b13-coef   依赖项的复核（数值）：H 的主分支（对 σ 做 Newton 延拓）的 Taylor 系数给出 a_k=Σ_{3n+j=k} n!H_{n,j}=f_k(t)
             （t=-1、-1/2、-3，k<=24，精确的 f_k 由 N(k,q) 算）
  b13-jump   引理 4.1 的主项（数值）：跳跃积分 Φ(y) 与 √(2π)(2-y)(1-y)^{-1/2}(-y^3)^{-1/2} 之比 → ±1，
             |比值∓1|<=|y|^{1/2}（定理里的误差阶）且随 |y| 减小（三个立方根方向，|y|=0.01、0.02、0.04）；
             三点 Richardson 外推到 |y|=0 后 |比值∓1|<5e-3（2026-10-09 按复核者 s15-b13 的意见加：原判据抓不到 ±5% 的常数错误）
  b13-dom    定理 1 证明里的方向选择：τ=1、arg x=θ_0/3 时 s=0 唯一主导、Re(1/x)>0、两个夹角条件成立；
             另 7 个 τ 各找到满足条件的方向 φ
  b13-geom   引理 1.4 与 §3 的几何：|w_l°|>=R 且只在 l=0、-1 取等（|l|<=2000）；τ=1 时射线 θ_0±η 与所有 w_l° 的夹角下界；
             动点界 |w_l(x)-w_l°|<=|x|(|ln τ|+π|2l+1|+1)（取样）
  b13-data   数值佐证（启发式，不是证明）：扣掉复核者 s15-b13 的包络 C_r n^{r/3-1/2}R^{-n}exp(Re β n^{2/3}+Re β' n^{1/3})
             后，每 10 个 n 的最大值对 n∈[100,330] 的线性漂移 |c|<1e-3（k=3n+r<=1000）；半径错 1.4% 时漂移约 1.4e-2
             （2026-10-09 按复核者意见改：原来的「窗口最大值与 1 相差 <0.04」只能排除半径 π）
  b13-rev    反向检查：去掉 g 的 x^2 项后跳跃比值趋于 1/2、主项常数乘 1.05 后外推偏离（b13-jump 的判据失败）；
             部分分式改一个系数后精确检查失败；把 τ 换错后 b13-coef 失败；半径按 π 或 R(1.05τ) 计算时 b13-data 的判据失败
"""
import cmath
import math
import os
import random
import sys
import time
from fractions import Fraction as Fr

import numpy as np

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []


def report(cid, ok, desc):
    RESULTS.append((cid, ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


# ---------------------------------------------------------------- 精确代数
def H_def_exact(x, u):
    g = 1 - x * x * u / (1 + u) ** 2
    return g / (1 - x + u)


def H_pf_exact(x, u, cq=None):
    p = 1 + u / (1 - x)
    q = 1 + u
    c1 = (1 - x) if cq is None else cq
    return (2 - x) / ((1 - x) * p) - c1 / q - x / q ** 2


def residue_parts(x):
    ps = -x / (1 - x)
    a1 = (1 - x) * ps / (1 - ps) + (x / (1 - x)) / (1 - ps) ** 2
    a2 = (x / (1 - x)) * ps / (1 - ps)
    wprime = -(1 - x) * ps / (1 - ps)
    return a1, a2 * (-wprime / x ** 3)


# ---------------------------------------------------------------- 数值工具
def c_l(tau, l):
    return math.log(1 / tau) + 1j * math.pi * (2 * l + 1)


def w0c(tau, l=0):
    return c_l(tau, l) - 1 - tau


def eps(x):
    return (1 - x) * cmath.log(1 - x) + x


def w_l(x, tau, l):
    return w0c(tau, l) - x * c_l(tau, l) + eps(x)


def p_l(x, tau, l):
    return w0c(tau, l) - x * c_l(tau, l)


def psi(sig, x, tau):
    return (1 - x) * sig + tau * (cmath.exp(sig) - 1)


def H_sigma(w, x, tau, steps=40, newton=6):
    sig = np.zeros_like(w, dtype=complex)
    for i in range(1, steps + 1):
        target = w * (i / steps)
        for _ in range(newton):
            e = tau * np.exp(sig)
            f = (1 - x) * sig + e - tau - target
            sig = sig - f / (1 - x + e)
    u = tau * np.exp(sig)
    g = 1 - x * x * u / (1 + u) ** 2
    return g / (1 - x + u), np.max(np.abs((1 - x) * sig + u - tau - w))


def N_table(K):
    N = [[0] * (K + 3) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1], N[2][2] = 1, 2
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            s = (N[k - 3][q - 2] if q >= 2 else 0) + 2 * N[k - 3][q - 1] + N[k - 3][q]
            N[k][q] = N[k - 1][q - 1] + N[k - 1][q] + (q - 1) * s
    return N


def f_exact(k, t, N):
    t = Fr(t)
    tot = Fr(0)
    for q in range(0, k + 1):
        if N[k][q]:
            tot += N[k][q] * (1 / (1 - t) if q == 0 else t ** (q - 1) / (1 - t) ** (q + 1))
    return tot


def coef_check(t, tau_used, rw, rx, K, N):
    Mw, Mx = 64, 128
    ww = rw * np.exp(2j * np.pi * np.arange(Mw) / Mw)
    xx = rx * np.exp(2j * np.pi * np.arange(Mx) / Mx)
    Wg, Xg = np.meshgrid(ww, xx, indexing='ij')
    Hv, res = H_sigma(Wg, Xg, tau_used)
    C = np.fft.fft2(Hv) / (Mw * Mx)
    Hnj = C / (rw ** np.arange(Mw)[:, None]) / (rx ** np.arange(Mx)[None, :])
    worst = 0.0
    for k in range(K + 1):
        a = sum(math.factorial(n) * Hnj[n, k - 3 * n] for n in range(k // 3 + 1))
        fe = float(f_exact(k, t, N))
        err = abs(a - fe) / max(1.0, abs(fe)) if fe == 0 else abs(a - fe) / abs(fe)
        worst = max(worst, err)
    return worst, res


def Phi_num(y, drop_g=False, M=20000, T=12.0):
    a = cmath.sqrt(y ** 3 / (1 - y))
    tot = 0
    for sgn in (1, -1):
        t = T * (np.arange(M) + .5) / M
        p = sgn * 1j * a * t
        dp = sgn * 1j * a * T / M
        q = y + (1 - y) * p
        if drop_g:
            om = -1 / (1 - p)   # H=1/((1-y)p)（g≡1）时 ω=H·dw/dp
        else:
            om = -(2 - y) / (1 - p) + (1 - y) ** 2 * p / ((1 - p) * q) + y * (1 - y) * p / ((1 - p) * q * q)
        expo = -(1 - y) * (p + np.log(1 - p)) / y ** 3
        tot += sgn * np.sum(np.exp(expo) * om) * dp
    return tot / y ** 3


def Phi_pred(y):
    return math.sqrt(2 * math.pi) * (2 - y) / cmath.sqrt(1 - y) / cmath.sqrt(-y ** 3)


def jump_errors(drop_g=False, scale=1.0):
    """返回 (各半径上 |比值∓1| 的最大值, 外推到 |y|=0 后 |比值∓1| 的最大值)。
    比值按 y 的幂展开（Φ 里 v 的奇次项积分为 0），用 h、2h、4h 三点的二阶 Richardson 外推。"""
    th0 = cmath.phase(w0c(1.0))
    errs, vals = {}, {s: {} for s in range(3)}
    for rad in (0.01, 0.02, 0.04):
        e = []
        for s in range(3):
            y = rad * cmath.exp(1j * (th0 / 3 + 2 * math.pi * s / 3))
            r = Phi_num(y, drop_g) / (scale * Phi_pred(y))
            vals[s][rad] = r
            e.append(min(abs(r - 1), abs(r + 1)))
        errs[rad] = max(e)
    ext = []
    for s in range(3):
        r0 = (8 * vals[s][0.01] - 6 * vals[s][0.02] + vals[s][0.04]) / 3
        ext.append(min(abs(r0 - 1), abs(r0 + 1)))
    return errs, max(ext)


def h_minus1(K):
    """h_k(-1)，k<=K，由 T1.7 的系数递推（只保留三行）。"""
    out = {0: 1, 1: 1, 2: 0}
    rows = {0: [1], 1: [1], 2: [1, 1]}
    for k in range(3, K + 1):
        a, b = rows[k - 1], rows[k - 3]
        deg = (2 * k) // 3
        h = [0] * (deg + 1)
        for i in range(deg + 1):
            v = a[i] if i < len(a) else 0
            if i < len(b):
                v += i * b[i]
            if 1 <= i <= len(b):
                v += (k - 2 * i) * b[i - 1]
            if 2 <= i <= len(b) + 1:
                v -= (k - i) * b[i - 2]
            h[i] = v
        while len(h) > 1 and h[-1] == 0:
            h.pop()
        rows[k] = h
        del rows[k - 3]
        out[k] = sum(c if i % 2 == 0 else -c for i, c in enumerate(h))
    return out


def data_drift(hm, R, kmax, n_lo=100, n_hi=330, win=10):
    """数值佐证（启发式，不是证明）：复核者 s15-b13 的包络
    |f_{3n+r}(-1)/n!| ≈ C_r n^{r/3-1/2} R^{-n} exp(Re β n^{2/3} + Re β' n^{1/3})，
    β=c_0 (w_0°)^{-2/3}，β'=(2/9)β^2-(1/2)(w_0°)^{-1/3}（t=-1：c_0=iπ，w_0°=-2+iπ）。
    扣掉包络后，每 win 个 n 取最大值，对 n 做最小二乘直线，返回三个 r 的斜率（半径对时应 ≈0，
    半径错成 R' 时斜率 ≈ log(R'/R)）。"""
    w0 = complex(-2, math.pi)
    beta = 1j * math.pi * w0 ** (-2 / 3)
    beta1 = (2 / 9) * beta ** 2 - 0.5 * w0 ** (-1 / 3)
    slopes = []
    for r in range(3):
        xs, ys = [], []
        for lo in range(n_lo, n_hi - win + 2, win):
            best = None
            for n in range(lo, lo + win):
                k = 3 * n + r
                if k > kmax or hm[k] == 0:
                    continue
                lf = math.log(abs(hm[k])) - (k + 1) * math.log(2) - math.lgamma(n + 1)
                E = (lf + n * math.log(R) - beta.real * n ** (2 / 3) - beta1.real * n ** (1 / 3)
                     - (r / 3 - 0.5) * math.log(n))
                if best is None or E > best[0]:
                    best = (E, n)
            if best:
                xs.append(float(best[1]))
                ys.append(best[0])
        mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
        c = sum((a - mx) * (b - my) for a, b in zip(xs, ys)) / sum((a - mx) ** 2 for a in xs)
        slopes.append(c)
    return slopes


def main():
    t0 = time.time()
    random.seed(20261009)

    # ---- b13-alg（精确）
    ok1 = True
    for _ in range(300):
        x = Fr(random.randint(-400, 400), random.randint(401, 2000))
        u = Fr(random.randint(-5000, 5000), random.randint(1, 997))
        if u == -1 or 1 - x + u == 0 or u == 0:
            continue
        ok1 &= H_def_exact(x, u) == H_pf_exact(x, u)
    ok2 = True
    for _ in range(300):
        x = Fr(random.randint(-400, 400), random.randint(401, 2000))
        if x == 0:
            continue
        a1, r = residue_parts(x)
        ok2 &= (a1 == 0 and r == 1)
    report('b13-alg', ok1 and ok2, '引理 1.1 部分分式在 300 组有理 (x,u) 上精确成立 %s；引理 1.5：a_1=0 且 a_2·(-w\'(p_*)/x^3)=1（300 个有理 x）%s'
           % (ok1, ok2))

    # ---- b13-wp（数值）
    worst = 0.0
    for _ in range(3000):
        x = complex(random.uniform(-.35, .35), random.uniform(-.35, .35))
        tau = math.exp(random.uniform(-4, 4))
        l = random.randint(-4, 4)
        sc = cmath.log((1 - x) / tau) + 1j * math.pi * (2 * l + 1)
        sp = math.log(1 / tau) + 1j * math.pi * (2 * l + 1)
        e1 = abs(psi(sc, x, tau) - w_l(x, tau, l))
        e2 = abs(psi(sp, x, tau) - p_l(x, tau, l))
        sig = complex(random.uniform(-3, 3), random.uniform(-4, 4))
        u = tau * cmath.exp(sig)
        p = 1 + u / (1 - x)
        # 对数形式比较 log G(p)=log(1-p)+p 与 (w-w_l(x))/(1-x)，差应在 2πiZ 里（避免 e^p 溢出）
        dd = (cmath.log(1 - p) + p - (psi(sig, x, tau) - w_l(x, tau, l)) / (1 - x)) / (2j * math.pi)
        e3 = abs(dd - round(dd.real))
        ps = -x / (1 - x)
        e4 = abs((1 - x) * (ps + cmath.log(1 - ps)) + eps(x))
        worst = max(worst, e1 / max(1, abs(w_l(x, tau, l))), e2 / max(1, abs(p_l(x, tau, l))), e3, e4)
    ok_eps = all(abs(eps(0.5 * r * cmath.exp(2j * math.pi * k / 64))) <= 0.62 * (0.5 * r) ** 2
                 for r in (0.1, 0.3, 0.6, 0.9, 1.0) for k in range(64))
    report('b13-wp', worst < 1e-12 and ok_eps, '临界值、极点值、G(p) 关系、w(p_*)=p_l(x)：最大误差 %.1e（3000 组随机 x、τ、l）；|ε(x)|<=0.62|x|^2 %s'
           % (worst, ok_eps))

    # ---- b13-coef（数值，复核依赖项 a_k=f_k(t)）
    K = 24
    N = N_table(K)
    rows, okc = [], True
    for (t, rw, rx) in [(-1, 1.0, 0.5), (Fr(-1, 2), 0.8, 0.4), (-3, 1.0, 0.5)]:
        wst, res = coef_check(t, float(-t), rw, rx, K, N)
        okc &= wst < 1e-6 and res < 1e-12
        rows.append('t=%s: %.1e' % (t, wst))
    report('b13-coef', okc, 'H 主分支的 Taylor 系数还原 f_k(t)（k<=24），最大相对误差 ' + '，'.join(rows))

    # ---- b13-jump（数值）
    errs, ext = jump_errors()
    okj = all(errs[r] <= math.sqrt(r) for r in errs) and errs[0.01] < errs[0.02] < errs[0.04] and ext < 5e-3
    report('b13-jump', okj, 'Φ(y)/预测 与 ±1 之差：' + '，'.join('|y|=%.2f: %.3f' % (r, errs[r]) for r in sorted(errs))
           + '（判据 <=|y|^{1/2} 且随 |y| 减小）；三点 Richardson 外推到 |y|=0 后 %.1e（判据 <5e-3）' % ext)

    # ---- b13-dom
    th0 = cmath.phase(w0c(1.0))
    c0 = c_l(1.0, 0)
    a = [(c0 * cmath.exp(2j * math.pi * s / 3) * cmath.exp(-2j * th0 / 3)).real for s in range(3)]
    s_star = max(range(3), key=lambda s: a[s])
    gap = a[s_star] - sorted(a)[-2]
    re1x = math.cos(th0 / 3)
    ang1 = min(abs(((math.pi - th0 / 3 - 2 * math.pi * s / 3) + math.pi) % (2 * math.pi) - math.pi) for s in range(3))
    ang2 = min(abs((((th0 / 3 + 2 * math.pi * s / 3) - math.pi) / 2 + math.pi / 2) % math.pi - math.pi / 2) for s in range(3))
    ok_t1 = s_star == 0 and gap > 1 and re1x > 0.5 and ang1 > 0.3 and ang2 > 0.1
    found = []
    for tau in (0.01, 0.1, 0.2785, 0.5, 2.0, 10.0, 100.0):
        thz = cmath.phase(w0c(tau))
        cz = c_l(tau, 0)
        best = None
        for k in range(-50, 51):
            phi = thz + 0.025 * k / 50
            aa = [(cz * cmath.exp(2j * math.pi * s / 3) * cmath.exp(-2j * phi / 3)).real for s in range(3)]
            ss = max(range(3), key=lambda s: aa[s])
            g = aa[ss] - sorted(aa)[-2]
            ry = abs(math.cos(phi / 3 + 2 * math.pi * ss / 3))
            if g > 0.05 and ry > 0.05 and phi < math.pi:
                best = (phi, ss)
                break
        found.append(best is not None)
    report('b13-dom', ok_t1 and all(found), 'τ=1：a_s=%s，s*=%d，差距 %.3f，cos(arg x)=%.3f，两个夹角下界 %.3f、%.3f；另 7 个 τ 找到合适方向 %s'
           % (','.join('%.3f' % v for v in a), s_star, gap, re1x, ang1, ang2, all(found)))

    # ---- b13-geom
    okg = True
    for tau in (0.01, 0.2785, 1.0, 3.0, 100.0):
        R = abs(w0c(tau))
        for l in range(-2000, 2001):
            m = abs(w0c(tau, l))
            if l in (0, -1):
                okg &= abs(m - R) < 1e-12
            else:
                okg &= m > R + 1e-9
    eta = 0.1
    min_ang = min(abs(cmath.phase(w0c(1.0, l) * cmath.exp(-1j * (th0 + sg * eta)))) for l in range(-2000, 2001) for sg in (1, -1))
    okb = True
    for _ in range(2000):
        x = 0.5 * random.random() * cmath.exp(2j * math.pi * random.random())
        tau = math.exp(random.uniform(-4, 4))
        l = random.randint(-50, 50)
        bound = abs(x) * (abs(math.log(tau)) + math.pi * abs(2 * l + 1) + 1)
        okb &= abs(w_l(x, tau, l) - w0c(tau, l)) <= bound and abs(p_l(x, tau, l) - w0c(tau, l)) <= bound
    report('b13-geom', okg and min_ang > 0.05 and okb, '|w_l°|>=R 且只在 l=0,-1 取等（5 个 τ，|l|<=2000）%s；τ=1、η=0.1 时射线与 w_l° 的最小夹角 %.3f；动点界 %s'
           % (okg, min_ang, okb))

    # ---- b13-data（数值佐证）
    hm = h_minus1(1000)
    R1 = abs(w0c(1.0))
    sl = data_drift(hm, R1, 1000)
    okd = all(abs(c) < 1e-3 for c in sl)
    report('b13-data', okd, '数值佐证（启发式包络，不是证明）：扣掉复核者 s15-b13 的包络后，窗口最大值对 n∈[100,330] 的线性漂移 '
           + '/'.join('%+.1e' % c for c in sl) + '（判据 |c|<1e-3；半径错 1.4% 时约 ±1.4e-2）')

    # ---- b13-rev
    errs_bad, ext_bad = jump_errors(drop_g=True)
    rev1 = not (all(errs_bad[r] <= math.sqrt(r) for r in errs_bad) and ext_bad < 5e-3)
    errs_sc, ext_sc = jump_errors(scale=1.05)
    rev1b = ext_sc >= 5e-3
    rev2 = any(H_def_exact(Fr(1, 7), Fr(u, 3)) != H_pf_exact(Fr(1, 7), Fr(u, 3), cq=1 - Fr(1, 7) + Fr(1, 1000))
               for u in range(1, 6))
    wst_bad, _ = coef_check(-1, 1.1, 1.0, 0.5, 12, N_table(12))
    rev3 = wst_bad > 1e-3
    R105 = abs(w0c(1.05))
    sl_pi = data_drift(hm, math.pi, 1000)
    sl_105 = data_drift(hm, R105, 1000)
    rev4 = not all(abs(c) < 1e-3 for c in sl_pi) and not all(abs(c) < 1e-3 for c in sl_105)
    report('b13-rev', rev1 and rev1b and rev2 and rev3 and rev4,
           '反向检查：g≡1 时跳跃误差 %s、外推 %.2f（应不满足判据）%s；主项常数乘 1.05 时外推 %.1e %s；改系数后部分分式不再相等 %s；'
           'τ 取 1.1 时系数误差 %.1e %s；半径取 π、R(1.05τ) 时数据漂移 %s、%s %s'
           % (','.join('%.2f' % errs_bad[r] for r in sorted(errs_bad)), ext_bad, rev1, ext_sc, rev1b, rev2, wst_bad, rev3,
              '/'.join('%+.3f' % c for c in sl_pi), '/'.join('%+.4f' % c for c in sl_105), rev4))

    n_pass = sum(1 for _, ok in RESULTS if ok)
    n_fail = len(RESULTS) - n_pass
    print('（用时 %.1f s）' % (time.time() - t0))
    print('SUMMARY b13 pass=%d fail=%d' % (n_pass, n_fail))
    return 0 if n_fail == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
