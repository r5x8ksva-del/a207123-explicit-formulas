# -*- coding: utf-8 -*-
"""s11-b6a 复核 E1–E6：用显式表示 f_x = (M-1/(1-t))/x + z*omega*J 加数值积分验证 notes/11 定理 2、命题 8。

不导入项目里的任何模块；只用标准库与 numpy（Gauss-Legendre 节点）。不积分 ODE。
  M(t)=sum t^m/P_m，K(t)=sum e_n(z) t^n/(n+1-lam)，J=t^{1-lam}K（主支），omega=t^lam e^{-zt}，theta=1/omega，z=x^-3。
沿道路延拓：R=(M-1/(1-t))/x 单值；omega 随绕 0 的圈数 k 乘 e^{2 pi i lam k}；
  J -> J + ∫_path theta(s)/(1-s) ds，theta 沿道路连续取支（log s 连续跟踪）。
于是 f^{w}(t0) = R(t0) + z*omega_k(t0)*(J(t0) + ∫_w theta/(1-s) ds)。积分用分段 Gauss-Legendre。
这条路线只用命题 1 的结构式，不用 ODE；与 s11b6a_taylor_chain.py（只用 ODE，不用命题 1）互相独立。

输出逐条 PASS/FAIL，最后一行 SUMMARY。
  E1  命题 1 的数值形式：R+z*omega*J 与原始幂级数 sum G_m t^m 在 D 内 4 个点一致（6 个 x）
  E2  归一化：J(t0)+∫_{gamma_0} theta/(1-s)ds = e^{-2 pi i lam} J(t0)（检验 J=t^{1-lam}K 正是原函数、常数也对）；
      ∫_{gamma_1} theta/(1-s)ds = -2 pi i e^z（留数与定向）
  E3  各种字（含 [gamma_0^d,gamma_1^d]，x=3/5 时 d=27）的延拓值与仿射预测 c -> q c、c -> c - nu 一致
  E4  命题 8（lam=-2）的 Ei 闭式：复数 x=(1+i)/2、(1-i)/2 与实数 x=-1，在 |t|<1 的 6 个点上与级数一致；
      沿 gamma_1 数值跟踪 log(1-t) 的支，闭式的跳跃 = -nu*omega(t0)
  E5  x=-1 的整理式 F(-1,t)=[e^t-1+t^2/(1-t)+e^{t-1}(Ei(1-t)-Ei(1))]/t^2 与级数一致（5 个实 t、2 个复 t）
  E6  反向检查：(i) 把 J 换成 J+1（常数错），E2 的归一化失败；(ii) 闭式里 log(1-t) 不跟踪支（每点取主值），
      绕 1 之后没有跳跃，与级数延拓不符；(iii) 把 K 的分母换成 n+2-lam，E1 失败
"""
import cmath
import math
import sys
import time

import numpy as np

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []
EULER_GAMMA = 0.57721566490153286060651209008240243


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


T0 = 0.5
GL_X, GL_W = np.polynomial.legendre.leggauss(30)


def params(x):
    x = complex(x)
    lam = (1 - x) / x ** 3
    z = 1 / x ** 3
    return x, lam, z, cmath.exp(2j * math.pi * lam), 2j * math.pi * z * cmath.exp(z)


def f_series(x, t, N=400):
    prev, s, p = 1.0 + 0j, 0j, 1.0 + 0j
    for m in range(N + 1):
        g = (prev + m * x * x) / (1 - x - m * x ** 3)
        s += g * p
        p *= t
        prev = g
    return s


def M_series(x, t, N=200):
    s, P, p = 0j, 1.0 + 0j, 1.0 + 0j
    for m in range(N + 1):
        P *= (1 - x - m * x ** 3)
        s += p / P
        p *= t
    return s


def K_series(x, t, N=2000, shift=1):
    lam, z = (1 - x) / x ** 3, 1 / x ** 3
    s, e, term, p = 0j, 0j, 1.0 + 0j, 1.0 + 0j
    for n in range(N + 1):
        e += term                 # e_n(z)
        term *= z / (n + 1)
        s += e * p / (n + shift - lam)
        p *= t
        if n > 50 and abs(p) < 1e-22:
            break
    return s


def pieces(x, t, shift=1):
    lam, z = (1 - x) / x ** 3, 1 / x ** 3
    lt = cmath.log(t)            # 主支（t 在 D 内）
    R = (M_series(x, t) - 1 / (1 - t)) / x
    J = cmath.exp((1 - lam) * lt) * K_series(x, t, shift=shift)
    om = cmath.exp(lam * lt - z * t)
    return R, J, om


def seg_integral(fun, a, b, panels=8):
    tot = 0j
    for i in range(panels):
        lo = a + (b - a) * i / panels
        hi = a + (b - a) * (i + 1) / panels
        mid, half = (lo + hi) / 2, (hi - lo) / 2
        for xi, wi in zip(GL_X, GL_W):
            tot += wi * half * fun(mid + half * xi)
    return tot


def loop_integral(x, letter, k):
    """∫ theta_k(s)/(1-s) ds 沿一个字母的圆周；返回 (积分, 新的 k)。theta_k 的 log s 从 ln t0 + 2 pi i k 连续出发。"""
    lam, z = (1 - x) / x ** 3, 1 / x ** 3
    if letter in '0a':
        sg = 1 if letter == '0' else -1

        def integrand(phi):
            s = T0 * cmath.exp(1j * sg * phi)
            logs = math.log(T0) + 1j * (2 * math.pi * k + sg * phi)
            theta = cmath.exp(-lam * logs + z * s)
            return theta / (1 - s) * (1j * sg * s)
        return seg_integral(integrand, 0.0, 2 * math.pi), k + sg
    sg = 1 if letter == '1' else -1
    r = 1 - T0

    def integrand(phi):
        w = cmath.exp(1j * (math.pi + sg * phi))
        s = 1 + r * w
        logs = cmath.log(s) + 2j * math.pi * k      # Re s > 0，主支连续
        theta = cmath.exp(-lam * logs + z * s)
        return theta / (1 - s) * (1j * sg * r * w)
    return seg_integral(integrand, 0.0, 2 * math.pi), k


def continue_word(x, word, R, J, k0=0):
    lam, z = (1 - x) / x ** 3, 1 / x ** 3
    k, acc = k0, J
    for letter in word:
        val, k = loop_integral(x, letter, k)
        acc += val
    om_k = cmath.exp(lam * (math.log(T0) + 2j * math.pi * k) - z * T0)
    return R + z * om_k * acc


def predict(word, q, nu):
    c = 0j
    for letter in word:
        c = {'0': lambda c: q * c, 'a': lambda c: c / q, '1': lambda c: c - nu, 'b': lambda c: c + nu}[letter](c)
    return c


def pw(letter, k):
    inv = {'0': 'a', '1': 'b'}
    return letter * k if k >= 0 else inv[letter] * (-k)


def Ei_entire(w, tol=1e-18):
    s, term, k = 0j, 1.0 + 0j, 0
    while True:
        k += 1
        term *= w / k
        add = term / k
        s += add
        if abs(add) < tol * max(1.0, abs(s)) and k > abs(w) + 5:
            return s


def closed_form_lam_m2(x, t, log1mt):
    """lam=-2 的命题 8 闭式；log1mt 是 log(1-t) 的取值（由调用者给定分支）。"""
    z = 1 / x ** 3
    I0 = (cmath.exp(z * t) - 1) / z
    I1 = t * cmath.exp(z * t) / z - (cmath.exp(z * t) - 1) / z ** 2
    # Ei(-z(1-t)) - Ei(-z) = log(1-t) + E(-z(1-t)) - E(-z)，log 沿像道路连续取支
    dEi = log1mt + Ei_entire(-z * (1 - t)) - Ei_entire(-z)
    bracket = -I0 - I1 - cmath.exp(z) * dEi
    return (M_series(x, t) - 1 / (1 - t)) / x + z * t ** (-2) * cmath.exp(-z * t) * bracket


XS = [('3/5', 0.6), ('1/sqrt2', 1 / math.sqrt(2)), ('2', 2.0), ('0.8+0.3i', 0.8 + 0.3j),
      ('-1', -1.0), ('(1+i)/2', 0.5 + 0.5j)]
TPTS = [0.5, 0.3 + 0.4j, -0.5 + 0.5j, 0.1 - 0.6j]


def main():
    t_start = time.time()
    # E1
    worst, lines = 0.0, []
    for name, xv in XS:
        x = complex(xv)
        w = 0.0
        for t in TPTS:
            R, J, om = pieces(x, t)
            z = 1 / x ** 3
            a = R + z * om * J
            b = f_series(x, t)
            w = max(w, abs(a - b) / max(1.0, abs(b)))
        worst = max(worst, w)
        lines.append('%s:%.1e' % (name, w))
    report('E1', worst < 1e-12, '命题 1 数值形式在 D 内 4 点的最大相对偏差：' + ', '.join(lines))
    # E2
    lines, ok2 = [], True
    for name, xv in XS:
        x, lam, z, q, nu = params(xv)
        R, J, om = pieces(x, T0)
        I0, _ = loop_integral(x, '0', 0)
        I1, _ = loop_integral(x, '1', 0)
        e_norm = abs(J + I0 - cmath.exp(-2j * math.pi * lam) * J) / max(1.0, abs(J))
        e_res = abs(I1 - (-2j * math.pi * cmath.exp(z))) / abs(cmath.exp(z))
        ok2 &= e_norm < 1e-12 and e_res < 1e-12
        lines.append('%s: 归一化 %.1e，留数 %.1e' % (name, e_norm, e_res))
    report('E2', ok2, '; '.join(lines))
    # E3
    lines, ok3 = [], True
    for name, xv in XS:
        x, lam, z, q, nu = params(xv)
        R, J, om = pieces(x, T0)
        f0 = R + z * om * J
        om0 = cmath.exp(lam * math.log(T0) - z * T0)
        scale = abs(nu * om0)
        words = ['1', 'b', '0', '01', '10', '0011', '1100', 'a1', '1a', '01ab', '0' * 2 + '1' * 2 + 'a' * 2 + 'b' * 2]
        if name == '3/5':
            words.append(pw('0', 27) + pw('1', 27) + pw('0', -27) + pw('1', -27))
        w = 0.0
        for word in words:
            val = continue_word(x, word, R, J)
            pred = f0 + predict(word, q, nu) * om0
            w = max(w, abs(val - pred) / max(scale, abs(pred - f0)))
        ok3 &= w < 1e-11
        lines.append('%s:%.1e' % (name, w))
    report('E3', ok3, '11 个字（x=3/5 另加 [gamma_0^27,gamma_1^27]）的延拓值与仿射预测的最大相对偏差：' + ', '.join(lines))
    # E4
    lines, ok4 = [], True
    for name, xv in [('(1+i)/2', 0.5 + 0.5j), ('(1-i)/2', 0.5 - 0.5j), ('-1', -1.0)]:
        x, lam, z, q, nu = params(xv)
        w = 0.0
        for t in [0.5, -0.9, 0.7, 0.3 + 0.6j, -0.4 - 0.7j, 0.85]:
            a = closed_form_lam_m2(x, t, cmath.log(1 - t))
            b = f_series(x, t, N=3000)
            w = max(w, abs(a - b) / max(1.0, abs(b)))
        # 沿 gamma_1 跟踪 log(1-t)
        Kp = 4000
        r = 1 - T0
        arg_prev = cmath.phase(1 - T0)
        logmod = math.log(r)
        acc_arg = arg_prev
        for j in range(1, Kp + 1):
            tt = 1 + r * cmath.exp(1j * (math.pi + 2 * math.pi * j / Kp))
            a_now = cmath.phase(1 - tt)
            d = a_now - arg_prev
            d -= 2 * math.pi * round(d / (2 * math.pi))
            acc_arg += d
            arg_prev = a_now
        log_after = logmod + 1j * acc_arg
        f_before = closed_form_lam_m2(x, T0, cmath.log(1 - T0))
        f_after = closed_form_lam_m2(x, T0, log_after)
        om0 = cmath.exp(lam * math.log(T0) - z * T0)
        e_jump = abs((f_after - f_before) - (-nu * om0)) / abs(nu * om0)
        good = abs(lam + 2) < 1e-12 and w < 1e-11 and e_jump < 1e-12
        ok4 &= good
        lines.append('x=%s: 闭式 vs 级数 %.1e，绕 1 跳跃相对误差 %.1e（log(1-t) 的辐角增量 %.6f·2π）'
                     % (name, w, e_jump, (acc_arg - cmath.phase(1 - T0)) / (2 * math.pi)))
    report('E4', ok4, '; '.join(lines))
    # E5
    w = 0.0
    for t in [-0.9, -0.5, 0.3, 0.7, 0.95, 0.2 + 0.5j, -0.3 - 0.4j]:
        dEi = cmath.log(1 - t) + Ei_entire(1 - t) - Ei_entire(1)
        a = (cmath.exp(t) - 1 + t * t / (1 - t) + cmath.exp(t - 1) * dEi) / t ** 2
        b = f_series(-1.0 + 0j, t, N=4000)
        w = max(w, abs(a - b) / max(1.0, abs(b)))
    report('E5', w < 1e-11, 'F(-1,t) 的整理式与级数的最大相对偏差 %.1e（7 个 t，含 2 个复 t、t=0.95）' % w)
    # E6
    x, lam, z, q, nu = params(0.6)
    R, J, om = pieces(x, T0)
    I0, _ = loop_integral(x, '0', 0)
    bad_norm = abs((J + 1) + I0 - cmath.exp(-2j * math.pi * lam) * (J + 1)) / abs(J)
    xc = 0.5 + 0.5j
    xc, lamc, zc, qc, nuc = params(xc)
    fb = closed_form_lam_m2(xc, T0, cmath.log(1 - T0))
    fa_naive = closed_form_lam_m2(xc, T0, cmath.log(1 - T0))     # 不跟踪支：回到 t0 时又取主值
    jump_naive = abs(fa_naive - fb)
    om0 = cmath.exp(lamc * math.log(T0) - zc * T0)
    R3, J3, om3 = pieces(x, 0.3 + 0.4j, shift=2)
    bad_E1 = abs(R3 + z * om3 * J3 - f_series(x, 0.3 + 0.4j))
    ok6 = bad_norm > 1e-3 and abs(jump_naive - abs(nuc * om0)) > 1 and bad_E1 > 1e-3
    report('E6', ok6, '(i) J 加常数 1 后归一化偏差 %.3g（应非零）；(ii) 不跟踪 log 支时的跳跃 %.1e（真跳跃 %.4g）；'
           '(iii) K 分母改成 n+2-lam 后命题 1 偏差 %.3g' % (bad_norm, jump_naive, abs(nuc * om0), bad_E1))
    n_pass = sum(RES)
    print('SUMMARY s11b6a_explicit_quad pass=%d fail=%d time=%.1fs' % (n_pass, len(RES) - n_pass, time.time() - t_start))
    return 0 if n_pass == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
