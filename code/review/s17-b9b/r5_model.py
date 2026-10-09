# -*- coding: utf-8 -*-
"""s17-b9b r5：notes/18 §3 的模型量（不 import 项目代码）。
  r5-xi      ξ*、t*、α* 的高精度值（50 位十进制二分 g'(t)=0）；g 在 (0,1) 上单峰（g' 在 (0,t*) 正、(t*,1) 负，对数网格抽样）
  r5-circle  圆周 |t|=s 上 Φ(se^{iθ})<Φ(s)（0<θ<=π）：s 从 1e-12 到 t*（对数网格 400 个 s，θ 网格 20000 个）；
             并验证 θ=0 处 ∂_θ^2Φ=-s g'(s)（调和性），所以 s>t* 时 θ=0 变成圆周上的局部极小——转变恰在 t*
  r5-path    复鞍点 t_s(ξ)（g(t)=ξ，上半平面，从 t* 延拓到 ξ→2/3）；∫arg t_s dξ/π；路径终点的辐角；
             恒等式 ∫_{ξ*}^{ξ_1}arg t_s dξ=[ξ arg t_s-Im G(t_s)]（G=log(1-t)-(1/3)log ψ(t)，沿路径连续取支）
  r5-toy     同一计算换成玩具势 G=a·log(1-t)+b·log(1+t/0.05)（a+b=2/3）：积分等于 a（正根质量），与 ψ 无关——
             所以 1/3 这个「自洽性」只检验了 t=1 处点质量 1/3 与路径的数值延拓，不检验 (H) 本身
  r5-beta    二阶项：tβ'(t) 在 t* 处的值（原文「约 −0.026」）；ℓ_k 的修正 ξ_c(k)=max_s[g(s)+ε sβ'(s)]，ε=(k/3)^{2/3}/k
  r5-freq    局部变号频率 arg t_s(ξ)/π 在 ξ=0.155、0.38 的值（原文 0.48、0.69）
  r5-H       负实轴上的密度与 F(1)=arg(−2+iπ)/(3π)；ψ（主支）在 C∖(−∞,0] 上只有 t=1 一个零点（在若干起点上用 Newton 搜 t=e^{t-1} 的其他解）；
             对复数 t，主支 ψ 不一定是 {ψ+2πil} 中模最小的（例如 t=5i、20i）
用法：py -3.14 code/review/s17-b9b/r5_model.py
"""
import cmath
import math
import os
import sys
import time
from decimal import Decimal as D, getcontext

sys.stdout.reconfigure(encoding='utf-8')
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


t00 = time.time()
# ---------------------------------------------------------------- ξ*
getcontext().prec = 60


def gp_dec(t):
    psi = t - 1 - t.ln()
    return (-psi + (1 - t) ** 2 / t) / (3 * psi * psi) - 1 / (1 - t) ** 2


def g_dec(t):
    psi = t - 1 - t.ln()
    return (1 - t) / (3 * psi) - t / (1 - t)


lo, hi = D('0.01'), D('0.3')
assert gp_dec(lo) > 0 > gp_dec(hi)
for _ in range(200):
    m = (lo + hi) / 2
    if gp_dec(m) > 0:
        lo = m
    else:
        hi = m
tstar = (lo + hi) / 2
xistar = g_dec(tstar)
alpha = 1 / xistar


def psi(t):
    return t - 1 - math.log(t)


def g(t):
    return (1 - t) / (3 * psi(t)) - t / (1 - t)


def gp(t):
    p = psi(t)
    return (-p + (1 - t) ** 2 / t) / (3 * p * p) - 1 / (1 - t) ** 2


ts, xs = float(tstar), float(xistar)
grid = [10 ** (-15 + 15 * s / 3000) for s in range(3000)] + [ts + (1 - ts) * s / 3000 for s in range(1, 3000)]
uni = all((gp(t) > 0) if t < ts * (1 - 1e-6) else (gp(t) < 0) for t in grid if abs(t - ts) > 1e-6 * ts)
report('r5-xi', abs(xistar - D('0.1040749769')) < D('1e-10') and abs(tstar - D('0.0754868881')) < D('1e-10')
       and abs(alpha - D('9.6084575704')) < D('1e-9') and uni,
       't*=%s，ξ*=g(t*)=%s，α*=1/ξ*=%s（50 位二分；与原文 0.0754868881、0.1040749769、9.6084575704 一致）；'
       'g\' 在 (0,t*) 上为正、(t*,1) 上为负（%d 个网格点，t 从 1e-15 到 1）'
       % (str(tstar)[:16], str(xistar)[:16], str(alpha)[:14], len(grid)))


# ---------------------------------------------------------------- 圆周
def Phi(t):
    return math.log(abs(1 - t)) - math.log(abs(t - 1 - cmath.log(t))) / 3


ok_circ = True
worst_margin = 1e9
svals = [10 ** (-12 + (math.log10(ts) + 12) * s / 399) for s in range(400)]
NT = 20000
for s in svals:
    base = Phi(s)
    mx = max(Phi(s * cmath.exp(1j * math.pi * n / NT)) for n in range(1, NT + 1))
    ok_circ = ok_circ and mx < base
    worst_margin = min(worst_margin, base - mx)
# 局部：∂_θ^2 Φ(se^{iθ})|_{θ=0} = -s g'(s)
def d2theta(s, hstep=1e-4):
    return (Phi(s * cmath.exp(1j * hstep)) + Phi(s * cmath.exp(-1j * hstep)) - 2 * Phi(s)) / hstep ** 2


loc = [(s, d2theta(s), -s * gp(s)) for s in (0.01, 0.05, ts * 0.99, ts * 1.01, 0.1, 0.2)]
loc_ok = all(abs(a - b) < 1e-4 * max(1, abs(b)) for _, a, b in loc)
beyond = [(s, max(Phi(s * cmath.exp(1j * math.pi * n / 4000)) for n in range(1, 4001)) - Phi(s)) for s in (ts * 1.01, 0.1, 0.2)]
report('r5-circle', ok_circ and loc_ok and all(v > 0 for _, v in beyond),
       '|t|=s 的圆周上 Φ 只在 θ=0 取最大：s∈[1e-12,t*] 的 400 个 s、θ∈(0,π] 的 %d 个点全部成立（最小差 %.2e，出现在 s→t* 处）；'
       '∂_θ^2Φ|_{θ=0}=-s g\'(s) 数值成立（%s），所以 s<t* 时 θ=0 是局部极大、s>t* 时是局部极小；s=1.01t*、0.1、0.2 时圆周上确有更大的值（差 %s）。'
       '原文说检查了 s 从 1e-6 到 t*，作者脚本实际只查了 s∈{0.001,0.01,0.03,0.05,0.07,0.075}'
       % (NT, worst_margin, ', '.join('s=%.3g: %.4g vs %.4g' % x for x in loc[:3]), ', '.join('%.2e' % v for _, v in beyond)))


# ---------------------------------------------------------------- 复鞍点路径
def gc(t):
    return (1 - t) / (3 * (t - 1 - cmath.log(t))) - t / (1 - t)


def gcp(t):
    p = t - 1 - cmath.log(t)
    return (-p + (1 - t) ** 2 / t) / (3 * p * p) - 1 / (1 - t) ** 2


def track(fun, dfun, t_start, xi0, xi1, N=40000, second=None):
    """沿 ξ 从 xi0 到 xi1 跟踪 fun(t)=ξ 的上半平面解（起点在实的二重根 t_start 处，按 sqrt 分叉出发）。"""
    out = []
    t = None
    for n in range(1, N + 1):
        xi = xi0 + (xi1 - xi0) * (n / N) ** 2
        if t is None:
            t = t_start + 1j * math.sqrt(2 * (xi - xi0) / abs(second))
        for _ in range(80):
            f = fun(t) - xi
            st = f / dfun(t)
            if abs(st) > 0.3 * abs(t):
                st *= 0.3 * abs(t) / abs(st)
            t = t - st
            if abs(f) < 1e-14:
                break
        out.append((xi, t))
    return out


def unwrap_arg(vals):
    out, prev = [], None
    for v in vals:
        a = cmath.phase(v)
        if prev is not None:
            while a - prev > math.pi:
                a -= 2 * math.pi
            while a - prev < -math.pi:
                a += 2 * math.pi
        out.append(a)
        prev = a
    return out


g2 = (g(ts + 1e-4) + g(ts - 1e-4) - 2 * g(ts)) / 1e-8
xi_end = 2 / 3 - 1e-7
path = track(gc, gcp, ts, xs, xi_end, N=60000, second=g2)
args = [cmath.phase(t) for _, t in path]
minim = min(t.imag for _, t in path)
integ = 0.0
prev = (xs, 0.0)
for (x, t), a in zip(path, args):
    integ += (x - prev[0]) * (a + prev[1]) / 2
    prev = (x, a)
integ_pi = integ / math.pi
# 恒等式：Im G 沿路径连续取支
a1 = unwrap_arg([1 - ts] + [1 - t for _, t in path])
apsi = unwrap_arg([ts - 1 - math.log(ts)] + [t - 1 - cmath.log(t) for _, t in path])
ImG_end = a1[-1] - apsi[-1] / 3
x_end, t_end = path[-1]
ident = x_end * args[-1] - ImG_end
merge_H = None
for n, (x, t) in enumerate(path):
    if n > 10 and abs(t.imag) < 1e-10 * abs(t):
        merge_H = (x, t.real)
        break
# g 在 (1,∞) 上的最小值（对数网格三分）
lo_, hi_ = math.log(1.0001), math.log(1e6)
for _ in range(300):
    m1 = lo_ + (hi_ - lo_) / 3
    m2 = hi_ - (hi_ - lo_) / 3
    if g(math.exp(m1)) < g(math.exp(m2)):
        hi_ = m2
    else:
        lo_ = m1
tmin_g = math.exp((lo_ + hi_) / 2)
gmin = g(tmin_g)
freq = {}
for target in (0.155, 0.38, 0.6, 0.66):
    best = min(path, key=lambda p: abs(p[0] - target))
    freq[target] = cmath.phase(best[1]) / math.pi
report('r5-path', abs(integ_pi - 1 / 3) < 2e-3 and minim > -1e-9 and abs(ident - integ) < 2e-3,
       '复鞍点从 t* 出发留在上半平面（最小虚部 %.2e）；ξ→2/3 时 t_s→%s（|t_s|=%.3g，arg/π=%.4f，即回到正实轴方向的无穷远）；'
       '∫_{ξ*}^{2/3}arg t_s dξ/π=%.5f（原文 0.333333）；恒等式右边 [ξ arg t_s−Im G]=%.5f·π，arg ψ 沿路径从 0 连续变到 %.4f·π，'
       'arg(1−t) 变到 %.4f·π；复鞍点在 ξ_2=%s 处落回正实轴 t_2=%s（=g 在 (1,∞) 上的最小值 %.5f，在 t=%.3f），之后是 (1,∞) 上的两个实鞍点，局部变号频率为 0'
       % (minim, '%.3g%+.3gi' % (t_end.real, t_end.imag), abs(t_end), args[-1] / math.pi, integ_pi, ident / math.pi,
          apsi[-1] / math.pi, a1[-1] / math.pi, '%.5f' % merge_H[0] if merge_H else '-', '%.3f' % merge_H[1] if merge_H else '-', gmin, tmin_g))
report('r5-freq', abs(freq[0.155] - 0.48) < 0.015 and abs(freq[0.38] - 0.69) < 0.015,
       '局部变号频率 arg t_s(ξ)/π：ξ=0.155 时 %.4f、ξ=0.38 时 %.4f（原文约 0.48、0.69）；ξ=0.6、0.66 时 %.4f、%.4f（2/3 附近减小）'
       % (freq[0.155], freq[0.38], freq[0.6], freq[0.66]))


# ---------------------------------------------------------------- 玩具势
def arg_up(t):
    """上半平面（含实轴）的辐角：实轴上的负数取 π，避免 -0.0 虚部给出 -π。"""
    im = t.imag if abs(t.imag) > 1e-12 * abs(t) else 0.0
    return math.atan2(im, t.real)


def toy(a, b, c0=0.05, N=200000):
    """G=a log(1-t)+b log(1+t/c0)。tG'(t)=ξ 化为二次方程 (ξ-a-b)t^2+(b-ξ-a c0+ξ c0)t-ξ c0=0，精确求根；
    复根取上半平面那个，实根按连续性取最近的。返回 ξ*、∫arg t dξ/π、复根重新落回实轴的 (ξ_2,t_2)。"""
    def fun(t):
        return -a * t / (1 - t) + b * t / (c0 + t)
    lo_, hi_ = 1e-9, 0.999
    for _ in range(300):
        m1 = lo_ + (hi_ - lo_) / 3
        m2 = hi_ - (hi_ - lo_) / 3
        if fun(m1) < fun(m2):
            lo_ = m1
        else:
            hi_ = m2
    tt = (lo_ + hi_) / 2
    xx = fun(tt)
    xi1 = a + b - 1e-9
    I, prev_x, prev_a, prev_t = 0.0, xx, 0.0, complex(tt, 0)
    merge = None
    for n in range(1, N + 1):
        xi = xx + (xi1 - xx) * (n / N) ** 2
        A = xi - a - b
        B = b - xi - a * c0 + xi * c0
        C = -xi * c0
        disc = B * B - 4 * A * C
        if disc < 0:
            t = (-B + 1j * math.sqrt(-disc)) / (2 * A)
            if t.imag < 0:
                t = t.conjugate()
        else:
            r1 = (-B + math.sqrt(disc)) / (2 * A)
            r2 = (-B - math.sqrt(disc)) / (2 * A)
            t = complex(min((r1, r2), key=lambda r: abs(r - prev_t)), 0.0)
            if merge is None and n > 10:
                merge = (xi, t.real)
        ar = arg_up(t)
        I += (xi - prev_x) * (ar + prev_a) / 2
        prev_x, prev_a, prev_t = xi, ar, t
    return xx, I / math.pi, merge


toys = [(1 / 3, 1 / 3, 0.05), (1 / 4, 5 / 12, 0.05), (1 / 6, 1 / 2, 0.05), (1 / 3, 1 / 3, 0.5)]
tres = [toy(a, b, c0) for a, b, c0 in toys]
report('r5-toy', all(abs(r[1] - a) < 2e-3 for r, (a, b, c0) in zip(tres, toys)),
       '玩具势 G=a log(1−t)+b log(1+t/c0)（负根全在 −c0 一点，正根全在 1），二次方程精确求根：'
       + '；'.join('(a,b,c0)=(%.3f,%.3f,%.2f)：ξ*_toy=%.4f，∫arg t_s dξ/π=%.4f，复根在 ξ_2=%s 处落回实轴 t_2=%s'
                  % (a, b, c0, r[0], r[1], '%.4f' % r[2][0] if r[2] else '-', '%.4f' % r[2][1] if r[2] else '-')
                  for r, (a, b, c0) in zip(tres, toys))
       + '。积分恰为各自的正根质量 a，与负根的位置无关。所以 notes/18 的「自洽性 0.333333」是恒等式 ∫arg t_s dξ=π·μ((0,∞)) 的一个实例，'
       '它检验的是 t=1 处的点质量 1/3（由 (H) 在 t→1 的形状给出，A19 本来就保证）与路径的数值延拓，不检验 (H) 在别处的形状')


# ---------------------------------------------------------------- 二阶项
def beta(t):
    return math.log(1 / t) / psi(t) ** (2 / 3)


def tbeta_p(t, h=1e-6):
    return t * (beta(t + h) - beta(t - h)) / (2 * h)


tb = tbeta_p(ts)
tb_closed = -1 / psi(ts) ** (2 / 3) - (2 / 3) * math.log(1 / ts) * (ts - 1) / psi(ts) ** (5 / 3)
shifts = []
for k in (1000, 5000, 20000, 10 ** 6):
    eps = (k / 3) ** (2 / 3) / k
    # ξ_c(k)=max_s [g(s)+eps*s β'(s)]
    lo_, hi_ = 0.01, 0.3
    f = lambda s: g(s) + eps * tbeta_p(s)
    for _ in range(200):
        m1 = lo_ + (hi_ - lo_) / 3
        m2 = hi_ - (hi_ - lo_) / 3
        if f(m1) < f(m2):
            lo_ = m1
        else:
            hi_ = m2
    xc = f((lo_ + hi_) / 2)
    shifts.append((k, (xc - xs) * k, tb * (k / 3) ** (2 / 3)))
report('r5-beta', abs(tb - tb_closed) < 1e-6,
       'tβ\'(t) 在 t* 处 = %.5f（差分与闭式一致；原文写约 −0.026）；按二阶项把鞍点方程改成 g(s)+ε sβ\'(s)=ξ 后，ℓ_k 的漂移 (ξ_c−ξ*)k：%s'
       '（与 tβ\'(t*)(k/3)^{2/3} 相符；只是启发式，没有 Airy 项）'
       % (tb, '; '.join('k=%d: %.2f（线性近似 %.2f）' % x for x in shifts)))

# ---------------------------------------------------------------- 负实轴密度、F(1)、ψ 的零点、主支与最近支
def dens(tau):
    v = tau + 1 + math.log(tau)
    return (1 / 3) * (1 + 1 / tau) / (v * v + math.pi ** 2)


def F(tau):
    v = tau + 1 + math.log(tau)
    return (math.atan(v / math.pi) + math.pi / 2) / (3 * math.pi)


# 数值积分密度与 F 对比；总质量 1/3
def integ_dens(a, b, n=200000):
    # 换元 τ=e^x
    xa, xb = math.log(a), math.log(b)
    hstep = (xb - xa) / n
    s = 0.0
    for m in range(n + 1):
        x = xa + m * hstep
        w = 0.5 if m in (0, n) else 1.0
        s += w * dens(math.exp(x)) * math.exp(x)
    return s * hstep


okF = all(abs(integ_dens(1e-12, tau) - (F(tau) - F(1e-12))) < 1e-7 for tau in (0.1, 1, 10, 1000))
F1 = F(1.0)
argw0 = cmath.phase(complex(-2, math.pi)) / (3 * math.pi)
# 由 Φ 的跳跃算密度：μ'(x)=-(1/π)Im G'(x+i0)
def Gp(t):
    return -1 / (1 - t) - (1 / 3) * (1 - 1 / t) / (t - 1 - cmath.log(t))


jump_ok = all(abs(-(1 / math.pi) * Gp(complex(-tau, 1e-12)).imag - dens(tau)) < 1e-9 for tau in (0.05, 0.5, 1, 3, 30))
# ψ 的零点：Newton 从许多起点出发
zeros = set()
for re_ in [x * 0.5 for x in range(-20, 21)]:
    for im_ in [y * 0.5 for y in range(-20, 21)]:
        t = complex(re_, im_)
        if abs(t) < 1e-9:
            continue
        ok = True
        for _ in range(200):
            if t.imag == 0 and t.real <= 0:
                ok = False
                break
            f = t - 1 - cmath.log(t)
            fp = 1 - 1 / t
            if abs(fp) < 1e-14:
                ok = False
                break
            t2 = t - f / fp
            if abs(t2 - t) < 1e-13:
                t = t2
                break
            t = t2
        if ok and abs(t - 1 - cmath.log(t)) < 1e-10 and not (t.imag == 0 and t.real <= 0):
            zeros.add((round(t.real, 6), round(t.imag, 6)))
only_one = all(abs(z[0] - 1) < 1e-4 and abs(z[1]) < 1e-4 for z in zeros)
near = []
for t in (5j, 20j, 3 + 8j, -3 + 8j, 0.5j, -1 + 0.5j):
    p0 = t - 1 - cmath.log(t)
    ls = range(-6, 7)
    best = min(ls, key=lambda l: abs(p0 + 2j * math.pi * l))
    near.append((t, abs(p0), best, abs(p0 + 2j * math.pi * best)))
report('r5-H', okF and abs(F1 - argw0) < 1e-12 and abs(F1 - 0.22682) < 1e-5 and jump_ok and only_one,
       '负实轴密度积分 = F 的差（τ=0.1,1,10,1000，误差 <1e-7），总质量 1/3；由 G\'(x+i0) 的虚部算出的密度与 μ\'(τ) 一致；'
       'F(1)=%.6f=arg(−2+iπ)/(3π)；主支 ψ 的零点（1681 个 Newton 起点）只找到 t=1。'
       '主支与最近支：%s（l≠0 时主支 ψ 不是 {ψ+2πil} 中模最小的）'
       % (F1, '; '.join('t=%s: |ψ_0|=%.3f，最近 l=%d，|ψ_l|=%.3f' % (str(t), a, l, b) for t, a, l, b in near)))
print('# elapsed %.1fs' % (time.time() - t00))
print('SUMMARY s17-r5 pass=%d fail=%d' % (RES.count(True), RES.count(False)))
