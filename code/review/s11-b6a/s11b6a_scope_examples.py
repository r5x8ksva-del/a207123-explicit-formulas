# -*- coding: utf-8 -*-
"""s11-b6a 复核 S1–S5：检验 notes/11 的函数类定义与附注 (d) 的边界（反例与基点问题）。

不导入项目里的任何模块，只用标准库。所有延拓都是数值地沿离散化道路连续跟踪辐角（或 Newton 跟踪根）。
道路：基点 t0=1/2，a = 圆周 |t|=1/2（绕 0，逆时针），b = 圆周 |t-1|=1/2（绕 1，逆时针），A、B 为它们的逆；
字按「先走左边」的约定（与 notes/11 的 f^{gamma gamma'} 相同）。

  S1  附注 (d) 末条的反例：u(t)=log t 属于 𝔄，可全纯延拓，各分支的零点只有 t=1（闭离散），
      但 log u = log log t 的群换位子 [a^d, b^d] 对一切 d=1..6 都作用非平凡（差 = -2 pi i d），
      按 notes/11 定理 6 第 2 步的同一论证，log log t 不属于 𝔙。
  S2  同样，li(t)=Ei(log t)（不完全 Gamma 型函数 Ei 以初等函数 log t 为自变量）的 [a^d, b^d] 差 = -2 pi i d，
      不属于 𝔙。（反向对照：Ei(t) 本身、Ei(t/(1-t)) 的同一换位子为 0。）
  S3  基点问题：代数函数 y^3 - y^2 - t = 0 在 t0=0 处取 y(0)=1 的全纯芽。沿 0 -> -4/27 附近绕一圈 -> 回到 0 的道路
      延拓后，芽变成 y ~ ±sqrt(-t) 的分支，在 t=0 不亚纯。所以按 notes/11 的字面定义（t0 不在 S 中、沿 C\\S 中
      每条道路都能亚纯延拓），这个代数芽不属于 𝔙_0，引理 4.1 在分支点处不成立（换到一般的基点就成立）。
  S4  同一问题对 f_x 本身：lam=1/2（x^3+2x-2=0 的实根）时，f_x 在 t=0 的芽沿「0 -> 1/2 -> 绕 1 一圈 -> 回到 0 附近」
      延拓后多出 -nu*omega，omega=t^{1/2}e^{-zt} 在 0 处是平方根型分歧：用 Taylor 链（只用 ODE）从 1/2 绕 1、
      再沿实轴走到 eps=0.05、再绕 0 一小圈，差 = 2*nu*omega(eps)（不绕 1 时差为 0）。所以 f_x 在 t=0 的芽
      不属于 𝔙_0，定理 6.2 的「⇐」不能对 t=0 这一点成立（对 t1 ∈ C\\{0,1} 成立）。
  S5  推论 5 末句「代入整函数」需要引理 3 的前提「可全纯延拓」：r(t)=1/(t^mu-1)（mu=sqrt2）在各分支上的极点
      e^{2 pi i j/mu} 在单位圆上稠密（到 -1、e^{0.3i} 的最近距离随 |j|<=J 增大趋于 0），
      所以 exp(r) 不能沿任何 C\\S（S 闭离散）中的每条道路亚纯延拓，不属于 𝔙。
"""
import cmath
import math
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []
EULER_GAMMA = 0.57721566490153286060651209008240243


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


T0 = 0.5


def path_points(word, K=4000):
    pts = [complex(T0)]
    for letter in word:
        for j in range(1, K + 1):
            s = j / K
            if letter in "aA":
                sg = 1 if letter == 'a' else -1
                pts.append(T0 * cmath.exp(sg * 2j * math.pi * s))
            else:
                sg = 1 if letter == 'b' else -1
                pts.append(1 + (1 - T0) * cmath.exp(1j * (math.pi + sg * 2 * math.pi * s)))
    return pts


def track_log(values, start_log):
    """沿一串复数值连续地跟踪 log：返回每点的 log 值。"""
    out = [start_log]
    cur = start_log
    for v_prev, v in zip(values[:-1], values[1:]):
        d = cmath.phase(v) - cmath.phase(v_prev)
        d -= 2 * math.pi * round(d / (2 * math.pi))
        cur = complex(math.log(abs(v)), cur.imag + d)
        out.append(cur)
    return out


def loglog_along(word):
    pts = path_points(word)
    L = track_log(pts, cmath.log(pts[0]))           # log t
    LL = track_log(L, cmath.log(L[0]))              # log log t
    return L, LL


def Ei_entire(w):
    s, term, k = 0j, 1.0 + 0j, 0
    while True:
        k += 1
        term *= w / k
        add = term / k
        s += add
        if abs(add) < 1e-18 * max(1.0, abs(s)) and k > abs(w) + 5:
            return s


def comm_word(d):
    return 'a' * d + 'b' * d + 'A' * d + 'B' * d


def main():
    # S1
    lines, ok1 = [], True
    for d in range(1, 7):
        L, LL = loglog_along(comm_word(d))
        diffL = L[-1] - L[0]
        diffLL = LL[-1] - LL[0]
        good = abs(diffL) < 1e-9 and abs(diffLL - (-2j * math.pi * d)) < 1e-9
        ok1 &= good
        lines.append('d=%d: Δlog t=%.1e, Δlog log t=%.6f i（预测 %.6f i）' % (d, abs(diffL), diffLL.imag, -2 * math.pi * d))
    # 对照：单独绕 b 一圈（在 log 的主叶上）log log t 增加 2 pi i；先绕 a 再绕 b 则不变
    _, LLb = loglog_along('b')
    _, LLab = loglog_along('ab')
    _, LLa = loglog_along('a')
    ctrl = abs((LLb[-1] - LLb[0]) - 2j * math.pi) < 1e-9 and abs((LLab[-1] - LLab[0]) - (LLa[-1] - LLa[0])) < 1e-9
    report('S1', ok1 and ctrl, 'log log t 的群换位子 [a^d,b^d]：' + '; '.join(lines)
           + '；对照：绕 b 一圈 Δ=2πi、先 a 后 b 与只走 a 相同：%s' % ctrl)
    # S2
    lines, ok2 = [], True
    for d in (1, 2, 3):
        L, LL = loglog_along(comm_word(d))
        li0 = EULER_GAMMA + LL[0] + Ei_entire(L[0])
        li1 = EULER_GAMMA + LL[-1] + Ei_entire(L[-1])
        # 反向对照：Ei(t) 与 Ei(t/(1-t)) 在同一字下的变化
        pts = path_points(comm_word(d))
        lt = track_log(pts, cmath.log(pts[0]))
        w = [p / (1 - p) for p in pts]
        lw = track_log(w, cmath.log(w[0]))
        dEi_t = (lt[-1] + Ei_entire(pts[-1])) - (lt[0] + Ei_entire(pts[0]))
        dEi_w = (lw[-1] + Ei_entire(w[-1])) - (lw[0] + Ei_entire(w[0]))
        good = abs((li1 - li0) - (-2j * math.pi * d)) < 1e-9 and abs(dEi_t) < 1e-9 and abs(dEi_w) < 1e-9
        ok2 &= good
        lines.append('d=%d: Δli=%.6f%+.6fi（预测 %.6f i）；ΔEi(t)=%.1e，ΔEi(t/(1-t))=%.1e'
                     % (d, (li1 - li0).real, (li1 - li0).imag, -2 * math.pi * d, abs(dEi_t), abs(dEi_w)))
    report('S2', ok2, 'li(t)=Ei(log t) 的 [a^d,b^d]：' + '; '.join(lines))
    # S3
    def newton(t, y):
        for _ in range(60):
            fy = y ** 3 - y ** 2 - t
            dy = 3 * y ** 2 - 2 * y
            step_ = fy / dy
            y -= step_
            if abs(step_) < 1e-15:
                break
        return y
    c0, rad = -4 / 27, 0.02
    pathp = []
    n1 = 4000
    for j in range(n1 + 1):                        # 0 -> c0 + rad（实轴，t 从 0 减到 c0+rad）
        pathp.append(complex((c0 + rad) * j / n1))
    for j in range(1, n1 + 1):                     # 绕 c0 一圈（逆时针），起点 c0+rad
        pathp.append(c0 + rad * cmath.exp(2j * math.pi * j / n1))
    for j in range(1, n1 + 1):                     # 回到 -1e-6（不碰 0 本身）
        pathp.append(complex((c0 + rad) + (-1e-6 - (c0 + rad)) * j / n1))
    y = 1.0 + 0j
    for t in pathp[1:]:
        y = newton(t, y)
    y_end = y
    # 在 t=-1e-6 附近再绕 0 一小圈：若是分歧分支，y 变号
    y2 = y_end
    for j in range(1, 4001):
        y2 = newton(-1e-6 * cmath.exp(2j * math.pi * j / 4000), y2)
    # 对照：不绕 c0，直接回到 -1e-6，仍是 y≈1 的分支
    y3 = 1.0 + 0j
    for j in range(1, 4001):
        y3 = newton(complex(-1e-6 * j / 4000), y3)
    # 两个小根是 y^2(1-y) = 1e-6 的 ±1e-3(1 ± 5e-4)，不是严格的相反数，所以分别判断符号与大小
    ok3 = (abs(abs(y_end) - 1e-3) < 1e-5 and y_end.real > 0 and y2.real < 0 and abs(abs(y2) - 1e-3) < 1e-5
           and abs(y2 ** 3 - y2 ** 2 + 1e-6) < 1e-15 and abs(y3 - 1) < 1e-5)
    report('S3', ok3, 'y^3-y^2-t=0：从 y(0)=1 出发绕 -4/27 一圈回到 t=-1e-6 时 y=%.3e%+.3ei（|y|≈sqrt(1e-6)=1e-3，分歧分支）；'
           '再绕 0 一小圈后 y=%.3e%+.3ei（变号）；对照：不绕 -4/27 时 y=%.6f' % (y_end.real, y_end.imag, y2.real, y2.imag, y3.real))
    # S4
    def newton_x(f, df, x0):
        x = x0
        for _ in range(100):
            dx = f(x) / df(x)
            x -= dx
            if abs(dx) < 1e-16:
                break
        return x
    x = newton_x(lambda u: u ** 3 + 2 * u - 2, lambda u: 3 * u ** 2 + 2, 0.77) + 0j
    lam = (1 - x) / x ** 3
    z = 1 / x ** 3
    nu = 2j * math.pi * z * cmath.exp(z)

    def f_ser(t, N=300):
        prev, s, p = 1.0 + 0j, 0j, 1.0 + 0j
        for m in range(N + 1):
            g = (prev + m * x * x) / (1 - x - m * x ** 3)
            s += g * p
            p *= t
            prev = g
        return s

    def tstep(c, a0, h, N=60):          # ODE x^3 t f' = (1-x-t) f - gamma 在中心 c 的 Taylor 递推
        x3, u = x ** 3, 1 - c
        a = [a0]
        for n in range(N):
            gn = (1 + x * x * c / u ** 2) if n == 0 else x * x * (c * (n + 1) / u ** (n + 2) + n / u ** (n + 1))
            anm1 = a[n - 1] if n >= 1 else 0
            a.append(((1 - x - c - x3 * n) * a[n] - anm1 - gn) / (x3 * c * (n + 1)))
        v = 0j
        for coef in reversed(a):
            v = v * h + coef
        return v

    def run(pts, f):
        for p0, p1 in zip(pts[:-1], pts[1:]):
            f = tstep(p0, f, p1 - p0)
        return f
    eps = 0.05
    circ1 = [1 + (1 - T0) * cmath.exp(1j * (math.pi + 2 * math.pi * j / 64)) for j in range(65)]
    circ1[-1] = complex(T0)
    seg = [complex(T0)]
    while seg[-1].real * 0.75 > eps:
        seg.append(seg[-1] * 0.75)
    seg.append(complex(eps))
    circ0 = [eps * cmath.exp(2j * math.pi * j / 64) for j in range(65)]
    circ0[-1] = complex(eps)
    f_half = f_ser(complex(T0))
    g_b = run(seg, run(circ1, f_half))           # 绕 1 后到 eps 的分支
    g_b_after = run(circ0, g_b)                  # 再绕 0 一圈
    g_0 = run(seg, f_half)                       # 对照：不绕 1
    g_0_after = run(circ0, g_0)
    om_eps = cmath.exp(lam * math.log(eps) - z * eps)
    e_pred = abs((g_b_after - g_b) - 2 * nu * om_eps) / abs(nu * om_eps)
    e_ctrl = abs(g_0_after - g_0) / abs(nu * om_eps)
    e_branch = abs((g_b - g_0) - (-nu * om_eps)) / abs(nu * om_eps)
    ok4 = abs(lam - 0.5) < 1e-14 and e_pred < 1e-10 and e_ctrl < 1e-10 and e_branch < 1e-10
    report('S4', ok4, 'lam=%.15f：绕 1 后的分支在 eps=0.05 处 = f - nu*omega（偏差 %.1e）；再绕 0 一圈的差与 2 nu omega(eps) '
           '的相对偏差 %.1e（|2 nu omega|=%.4g）；对照（不绕 1）绕 0 一圈的差 %.1e'
           % (lam.real, e_branch, e_pred, abs(2 * nu * om_eps), e_ctrl))
    # S5
    mu = math.sqrt(2)
    lines, ok5 = [], True
    for target in (-1 + 0j, cmath.exp(0.3j)):
        dists = []
        for J in (10, 100, 1000, 10000, 100000):
            best = min(abs(cmath.exp(2j * math.pi * j / mu) - target) for j in range(-J, J + 1))
            dists.append(best)
        mono = all(dists[i + 1] <= dists[i] for i in range(len(dists) - 1))
        ok5 &= mono and dists[-1] < 1e-3
        lines.append('目标 %.3f%+.3fi：' % (target.real, target.imag) + ', '.join('J=%d:%.1e' % (J, dd) for J, dd in
                                                                                 zip((10, 100, 1000, 10000, 100000), dists)))
    # 核对：e^{2 pi i j/mu} 确实是第 k=round(j/mu) 叶上 1/(t^mu-1) 的极点
    worst = 0.0
    for j in (7, 70, 701, -333):
        k = round(j / mu)
        phi = 2 * math.pi * j / mu - 2 * math.pi * k
        logt = 1j * phi + 2j * math.pi * k
        worst = max(worst, abs(cmath.exp(mu * logt) - 1))
    ok5 &= worst < 1e-9
    report('S5', ok5, '1/(t^mu-1)（mu=sqrt2）各叶极点到目标点的最近距离：' + '; '.join(lines)
           + '；极点核对 |t^mu-1| 最大 %.1e' % worst)
    n_pass = sum(RES)
    print('SUMMARY s11b6a_scope_examples pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
    return 0 if n_pass == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
