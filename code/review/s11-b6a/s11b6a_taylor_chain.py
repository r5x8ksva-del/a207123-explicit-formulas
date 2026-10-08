# -*- coding: utf-8 -*-
"""s11-b6a 复核 T1–T4：用 Taylor 链（Weierstrass 解析延拓）独立验证 notes/11 定理 2 的单值公式。

不导入项目里的任何模块（check_b6.py、core.py 都不导入），只用标准库。
与 check_b6 的 RK4 不同：这里在道路上取一串中心 c_j，用 ODE 的系数递推求出 f 在 c_j 处的 Taylor 级数
（只用 f(c_j) 一个初值，因为方程是一阶的），再在下一个中心求值。初值 f_x(t0) 用原始递推
b_m G_m = G_{m-1} + m x^2（G_{-1}=1，T1.3(1)）的幂级数求和。不经过命题 1 的结构式。

ODE：x^3 t f' = (1-x-t) f - gamma(t)，gamma(t) = 1 + x^2 t/(1-t)^2（T1.6，即 L[f]=gamma）。
中心 c 处 f = sum a_n s^n（s=t-c）的递推：
  x^3 c (n+1) a_{n+1} = (1-x-c-x^3 n) a_n - a_{n-1} - g_n，g_n = [s^n] gamma(c+s)。
道路：gamma_0 = 圆周 |t|=t0，gamma_1 = 圆周 |t-1|=1-t0，都逆时针、都从 t0 出发；字母 '0','1' 表示它们，
'a','b' 表示它们的逆。字 w = w_1 w_2 ... 表示先走 w_1、再走 w_2（与 notes/11 的 f^{gamma gamma'} 约定相同）。

预测（由 notes/11 定理 2(2) 推出）：f 的每个分支都形如 f + c*omega（omega 取 t0 处主支），
  gamma_0: c -> q c（q = e^{2 pi i lam}），gamma_1: c -> c - nu（nu = 2 pi i x^-3 e^{x^-3}），按字的顺序作用。

输出逐条 PASS/FAIL，最后一行 SUMMARY。
  TC1  每个 x：绕 0 不变；绕 1 的跳跃 = -nu*omega(t0)；绕 1 的逆 = +nu*omega(t0)
  TC2  每个 x：(a,b) in {(1,1),(2,1),(1,2),(-1,1),(1,-1),(2,-2)} 的 f^{g0^a g1^b} - f^{g1^b g0^a} = -b nu (1-q^a) omega
  TC3  群换位子 [g0^d, g1^d] = g0^d g1^d g0^-d g1^-d 作用后的差 = d nu (1-q^-d) omega：
       x=3/5（lam=50/27）时 d=1,9 非零、d=27 为零；x=1/sqrt2（lam=2sqrt2-2，无理）d=1,2,3 都非零
  TC4  lam=-2 的两个 x（x=-1 与复数 x=(1+i)/2）：各种换位子数值为 0，绕 1 的跳跃非零
  TC5  反向检查：(i) 把 nu 换成「二阶极点主部系数」的朴素值 2 pi i z x^2 e^z，与链式延拓不符；
       (ii) 把跳跃的符号取反（+nu*omega），不符；(iii) 右端换成零留数的 gamma + t/(1-t)，绕 1 的跳跃为 0；
       (iv) 把 Taylor 链的步数减半、项数减少，结果不变（数值稳定性）
"""
import cmath
import math
import sys
import time

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


T0 = 0.5


def params(x):
    x = complex(x)
    lam = (1 - x) / x ** 3
    z = 1 / x ** 3
    q = cmath.exp(2j * math.pi * lam)
    nu = 2j * math.pi * z * cmath.exp(z)
    omega = cmath.exp(lam * math.log(T0) - z * T0)
    return x, lam, z, q, nu, omega


def f_series(x, t, rhs='gamma', N=260):
    """原始递推的幂级数 sum G_m t^m（|t|<1）。rhs='zerores' 时右端多一项 t/(1-t)。"""
    prev = 1.0 + 0j
    s, p = 0j, 1.0 + 0j
    for m in range(N + 1):
        bm = 1 - x - m * x ** 3
        r = m * x * x + (1 if (rhs == 'zerores' and m >= 1) else 0)
        g = (prev + r) / bm
        s += g * p
        p *= t
        prev = g
    return s


def g_coef(x, c, n, rhs):
    u = 1 - c
    if n == 0:
        v = 1 + x * x * c / u ** 2
        if rhs == 'zerores':
            v += c / u
        return v
    v = x * x * (c * (n + 1) / u ** (n + 2) + n / u ** (n + 1))
    if rhs == 'zerores':          # t/(1-t) = (c+s)/(u-s) = (c+s) sum s^k/u^{k+1}
        v += c / u ** (n + 1) + 1 / u ** n
    return v


def step(x, c, a0, h, N, rhs):
    x3 = x ** 3
    a = [a0]
    for n in range(N):
        anm1 = a[n - 1] if n >= 1 else 0
        a.append(((1 - x - c - x3 * n) * a[n] - anm1 - g_coef(x, c, n, rhs)) / (x3 * c * (n + 1)))
    v = 0j
    for coef in reversed(a):
        v = v * h + coef
    return v


def loop_points(letter, K):
    pts = []
    for j in range(K + 1):
        s = j / K
        if letter in '0a':
            sg = 1 if letter == '0' else -1
            pts.append(T0 * cmath.exp(sg * 2j * math.pi * s))
        else:
            sg = 1 if letter == '1' else -1
            pts.append(1 + (1 - T0) * cmath.exp(1j * (math.pi + sg * 2 * math.pi * s)))
    pts[-1] = T0 + 0j      # 闭合
    return pts


def continue_word(x, word, f0, K=64, N=40, rhs='gamma'):
    f = f0
    for letter in word:
        pts = loop_points(letter, K)
        for j in range(K):
            f = step(x, pts[j], f, pts[j + 1] - pts[j], N, rhs)
    return f


def predict(word, q, nu):
    c = 0j
    for letter in word:
        if letter == '0':
            c = q * c
        elif letter == 'a':
            c = c / q
        elif letter == '1':
            c = c - nu
        elif letter == 'b':
            c = c + nu
    return c


def pw(letter, k):
    """letter^k，k 可为负。"""
    inv = {'0': 'a', '1': 'b'}
    return letter * k if k >= 0 else inv[letter] * (-k)


XS = [
    ('3/5', 0.6),
    ('1/sqrt2', 1 / math.sqrt(2)),
    ('2', 2.0),
    ('0.8+0.3i', 0.8 + 0.3j),
    ('-1', -1.0),
    ('(1+i)/2', 0.5 + 0.5j),
]


def main():
    t_start = time.time()
    cache = {}
    # TC1, TC2
    for name, xv in XS:
        x, lam, z, q, nu, om = params(xv)
        f0 = f_series(x, T0)
        scale = abs(nu * om)
        cache[name] = (x, lam, z, q, nu, om, f0, scale)
        e0 = abs(continue_word(x, '0', f0) - f0) / scale
        j1 = continue_word(x, '1', f0) - f0
        e1 = abs(j1 - (-nu * om)) / scale
        jb = continue_word(x, 'b', f0) - f0
        eb = abs(jb - nu * om) / scale
        ok = e0 < 1e-10 and e1 < 1e-10 and eb < 1e-10 and abs(j1) > 1e-6
        report('TC1', ok, 'x=%s lam=%s: |nu omega|=%.6g, 绕0相对差 %.1e，绕1 跳跃相对误差 %.1e，逆绕1 %.1e'
               % (name, ('%.6g' % lam.real) if abs(lam.imag) < 1e-15 else ('%.4g%+.4gi' % (lam.real, lam.imag)),
                  scale, e0, e1, eb))
        worst = 0.0
        for a_, b_ in [(1, 1), (2, 1), (1, 2), (-1, 1), (1, -1), (2, -2)]:
            w1 = pw('0', a_) + pw('1', b_)
            w2 = pw('1', b_) + pw('0', a_)
            d = continue_word(x, w1, f0) - continue_word(x, w2, f0)
            pred = -b_ * nu * (1 - q ** a_) * om
            # 预测与 predict() 的仿射计算一致（自检）
            assert abs((predict(w1, q, nu) - predict(w2, q, nu)) * om - pred) <= 1e-9 * max(1, abs(pred))
            denom = max(scale, abs(pred))
            worst = max(worst, abs(d - pred) / denom)
        report('TC2', worst < 1e-9, 'x=%s: 六组 (a,b) 的交换次序之差与 -b nu (1-q^a) omega 的最大相对偏差 %.1e'
               % (name, worst))
    # TC3
    lines, ok3 = [], True
    for name, ds, zero_d in [('3/5', (1, 9, 27), 27), ('1/sqrt2', (1, 2, 3), None)]:
        x, lam, z, q, nu, om, f0, scale = cache[name]
        for d in ds:
            word = pw('0', d) + pw('1', d) + pw('0', -d) + pw('1', -d)
            diff = continue_word(x, word, f0) - f0
            pred = d * nu * (1 - q ** (-d)) * om
            assert abs(predict(word, q, nu) * om - pred) <= 1e-9 * max(1, abs(pred))
            err = abs(diff - pred) / scale
            nonzero = abs(diff) / scale
            expect_zero = (zero_d is not None and d % zero_d == 0)
            good = err < 1e-8 and ((nonzero < 1e-8) if expect_zero else (nonzero > 1e-3))
            ok3 &= good
            lines.append('x=%s d=%d: |差|/|nu omega|=%.3g（预测 %.3g），偏差 %.1e' % (name, d, nonzero, abs(pred) / scale, err))
    report('TC3', ok3, '; '.join(lines))
    # TC4
    lines, ok4 = [], True
    for name in ('-1', '(1+i)/2'):
        x, lam, z, q, nu, om, f0, scale = cache[name]
        worst = 0.0
        for w1, w2 in [('01', '10'), ('0011', '1100'), ('a1', '1a'), ('0' + '1' + 'a' + 'b', '')]:
            d = continue_word(x, w1, f0) - continue_word(x, w2, f0)
            worst = max(worst, abs(d) / scale)
        jump = abs(continue_word(x, '1', f0) - f0)
        good = abs(lam + 2) < 1e-12 and worst < 1e-9 and jump > 1e-3
        ok4 &= good
        lines.append('x=%s（lam=%.3g%+.1gi）：换位子最大 |差|/|nu omega|=%.1e，|绕1 跳跃|=%.6g'
                     % (name, lam.real, lam.imag, worst, jump))
    report('TC4', ok4, '; '.join(lines))
    # TC5
    x, lam, z, q, nu, om, f0, scale = cache['3/5']
    j1 = continue_word(x, '1', f0) - f0
    naive = -(2j * math.pi * z * x * x * cmath.exp(z)) * om
    r_i = abs(j1 - naive) / scale
    r_ii = abs(j1 - nu * om) / scale
    f0z = f_series(x, T0, rhs='zerores')
    jz = continue_word(x, '1', f0z, rhs='zerores') - f0z
    r_iii = abs(jz) / scale
    j1_coarse = continue_word(x, '1', f0, K=32, N=30) - f0
    r_iv = abs(j1_coarse - j1) / scale
    ok5 = r_i > 0.1 and r_ii > 0.1 and r_iii < 1e-10 and r_iv < 1e-10
    report('TC5', ok5, '(x=3/5) (i) 朴素常数的相对偏差 %.3g（应明显非零）；(ii) 符号取反的偏差 %.3g（应为 2）；'
           '(iii) 零留数右端的绕 1 跳跃 %.1e（应为 0）；(iv) 步数 32、项数 30 与 64、40 之差 %.1e'
           % (r_i, r_ii, r_iii, r_iv))
    n_pass = sum(RES)
    print('SUMMARY s11b6a_taylor_chain pass=%d fail=%d time=%.1fs' % (n_pass, len(RES) - n_pass, time.time() - t_start))
    return 0 if n_pass == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
