# -*- coding: utf-8 -*-
"""s11-b6a 复核 D1–D4：60 位十进制精度的 Taylor 链解析延拓，验证 notes/11 定理 2(2)(3)。

不导入项目里的任何模块，只用标准库 decimal（复数运算自己实现：C 类 = 一对 Decimal）。
方法同 s11b6a_taylor_chain.py（只用 ODE x^3 t f' = (1-x-t)f - gamma 的系数递推与原始幂级数初值，不用命题 1），
但全程 60 位精度，每圈 48 段，每段 Taylor 级数取 90 项（截断误差约 (0.065/0.5)^90 < 1e-79）。
pi 用 Python 文档里的级数算法计算，并与 50 位常数核对；cos、sin 用 Taylor 级数加约化。

输出逐条 PASS/FAIL，最后一行 SUMMARY。
  D0  自检：pi 与 50 位常数一致；exp(i pi) = -1 到 1e-55
  D1  x=3/5、1/sqrt2、(1+i)/2：绕 0 不变；绕 1 的跳跃 = -nu*omega(t0)，nu = 2 pi i x^-3 e^{x^-3}
  D2  同上三个 x：f^{gamma_0 gamma_1} - f^{gamma_1 gamma_0} = -nu(1 - e^{2 pi i lam}) omega(t0)（lam=-2 时为 0）
  D3  灵敏度（反向）：把预测的 nu 乘 (1+1e-40)，偏差能被检测到（应约为 1e-40，远大于 D1 的误差）
"""
import sys
import time
from decimal import Decimal as D, getcontext, localcontext

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

getcontext().prec = 60
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def dpi():
    with localcontext() as ctx:
        ctx.prec += 4
        three = D(3)
        lasts, t, s, n, na, d, da = 0, three, D(3), 1, 0, 0, 24
        while s != lasts:
            lasts = s
            n, na = n + na, na + 8
            d, da = d + da, da + 32
            t = (t * n) / d
            s += t
    return +s


PI = dpi()
TWO_PI = 2 * PI


def dcos_sin(x):
    with localcontext() as ctx:
        ctx.prec += 6
        k = (x / TWO_PI).to_integral_value()
        y = x - k * TWO_PI
        c, s = D(1), y
        term_c, term_s = D(1), y
        i = 0
        y2 = y * y
        while True:
            i += 2
            term_c = -term_c * y2 / (i * (i - 1))
            term_s = -term_s * y2 / ((i + 1) * i)
            c += term_c
            s += term_s
            if abs(term_c) < D(10) ** (-(ctx.prec + 2)) and abs(term_s) < D(10) ** (-(ctx.prec + 2)):
                break
    return +c, +s


class C:
    __slots__ = ('r', 'i')

    def __init__(self, r, i=D(0)):
        self.r = r if isinstance(r, D) else D(r)
        self.i = i if isinstance(i, D) else D(i)

    def __add__(self, o):
        o = cc(o)
        return C(self.r + o.r, self.i + o.i)
    __radd__ = __add__

    def __sub__(self, o):
        o = cc(o)
        return C(self.r - o.r, self.i - o.i)

    def __rsub__(self, o):
        o = cc(o)
        return C(o.r - self.r, o.i - self.i)

    def __mul__(self, o):
        o = cc(o)
        return C(self.r * o.r - self.i * o.i, self.r * o.i + self.i * o.r)
    __rmul__ = __mul__

    def __truediv__(self, o):
        o = cc(o)
        den = o.r * o.r + o.i * o.i
        return C((self.r * o.r + self.i * o.i) / den, (self.i * o.r - self.r * o.i) / den)

    def __rtruediv__(self, o):
        return cc(o) / self

    def __neg__(self):
        return C(-self.r, -self.i)

    def abs(self):
        return (self.r * self.r + self.i * self.i).sqrt()


def cc(o):
    if isinstance(o, C):
        return o
    return C(D(o))


def cexp(w):
    w = cc(w)
    m = w.r.exp()
    c, s = dcos_sin(w.i)
    return C(m * c, m * s)


I = C(0, 1)
T0 = D(1) / 2
LN_T0 = T0.ln()


def f_series(x, t, N=230):
    prev, s, p = C(1), C(0), C(1)
    x2, x3 = x * x, x * x * x
    for m in range(N + 1):
        g = (prev + x2 * m) / (1 - x - x3 * m)
        s = s + g * p
        p = p * t
        prev = g
    return s


def step(x, x2, x3, c, a0, h, N):
    u = 1 - c
    inv_u = 1 / u
    a = [a0]
    up = inv_u * inv_u        # u^{-(n+2)}，n=0
    up1 = inv_u               # u^{-(n+1)}，n=0
    xc = x3 * c
    for n in range(N):
        if n == 0:
            gn = 1 + x2 * c * up
        else:
            gn = x2 * (c * (n + 1) * up + up1 * n)
        anm1 = a[n - 1] if n >= 1 else C(0)
        a.append(((1 - x - c - x3 * n) * a[n] - anm1 - gn) / (xc * (n + 1)))
        up = up * inv_u
        up1 = up1 * inv_u
    v = C(0)
    for coef in reversed(a):
        v = v * h + coef
    return v


def loop_points(letter, K):
    pts = []
    sg = 1 if letter in '01' else -1
    for j in range(K + 1):
        ang = TWO_PI * j / K * sg
        c_, s_ = dcos_sin(ang)
        e = C(c_, s_)
        if letter in '0a':
            pts.append(e * T0)
        else:
            pts.append(1 - e * (1 - T0))       # 1 + (1-t0) e^{i(pi + ang)}
    pts[-1] = C(T0)
    return pts


def continue_word(x, word, f0, K=48, N=90):
    x2, x3 = x * x, x * x * x
    f = f0
    for letter in word:
        pts = loop_points(letter, K)
        for j in range(K):
            f = step(x, x2, x3, pts[j], f, pts[j + 1] - pts[j], N)
    return f


def fmt(v):
    return '%.2e' % float(v)


def main():
    t_start = time.time()
    pi50 = D('3.14159265358979323846264338327950288419716939937510')
    e_ipi = cexp(I * PI) + 1
    report('D0', abs(PI - pi50) < D('1e-49') and e_ipi.abs() < D('1e-55'),
           'pi 与 50 位常数之差 %s；|exp(i pi)+1| = %s' % (fmt(abs(PI - pi50)), fmt(e_ipi.abs())))
    xs = [('3/5', C(D(3) / 5)), ('1/sqrt2', C((D(1) / 2).sqrt())), ('(1+i)/2', C(D(1) / 2, D(1) / 2))]
    for name, x in xs:
        x3 = x * x * x
        lam = (1 - x) / x3
        z = 1 / x3
        nu = 2 * PI * I * z * cexp(z)
        om = cexp(lam * LN_T0 - z * T0)
        q = cexp(2 * PI * I * lam)
        f0 = f_series(x, C(T0))
        scale = (nu * om).abs()
        e0 = (continue_word(x, '0', f0) - f0).abs() / scale
        j1 = continue_word(x, '1', f0) - f0
        e1 = (j1 - (-nu * om)).abs() / scale
        report('D1', e0 < D('1e-45') and e1 < D('1e-45'),
               'x=%s：绕 0 相对差 %s；绕 1 跳跃相对误差 %s（|nu omega| = %s）' % (name, fmt(e0), fmt(e1), fmt(scale)))
        d = continue_word(x, '01', f0) - continue_word(x, '10', f0)
        pred = -nu * (1 - q) * om
        e2 = (d - pred).abs() / scale
        report('D2', e2 < D('1e-45'), 'x=%s：交换次序之差 |d|/|nu omega| = %s，与预测的相对误差 %s'
               % (name, fmt(d.abs() / scale), fmt(e2)))
        if name == '3/5':
            nu_bad = nu * (1 + D('1e-40'))
            e3 = (j1 - (-nu_bad * om)).abs() / scale
            report('D3', D('5e-41') < e3 < D('5e-40') and e3 > 1000 * e1,
                   'x=3/5：把 nu 乘 (1+1e-40) 后的偏差 %s（D1 的误差 %s）' % (fmt(e3), fmt(e1)))
    n_pass = sum(RES)
    print('SUMMARY s11b6a_decimal_chain pass=%d fail=%d time=%.1fs' % (n_pass, len(RES) - n_pass, time.time() - t_start))
    return 0 if n_pass == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
