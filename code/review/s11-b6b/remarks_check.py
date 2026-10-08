# -*- coding: utf-8 -*-
"""s11-b6b 复核脚本 6：附注 (a)、附注 (d) 与 §0 的几个具体说法。
  R-res     附注 (a)/「nu 的来源」：用圆周 |s-1|=0.3 上的梯形公式（解析周期函数，指数收敛；decimal 40 位，N=160）算
            Res_{s=1} theta(s)gamma(s)/s = e^z；Res_{s=1} theta(s)[gamma(s)+s/(1-s)]/s = 0；
            Res_{s=1} theta(s)/(1-s) = -e^z；另外 Res_{t=1}[gamma(t)+t/(1-t)] = x^2-1 ≠ 0
            （说明附注 (a) 的「留数为零」指被积式 theta*rho/s 的留数，不是右端 rho 本身的留数）
  R-loglog  附注 (d) 末条的反例：z(t)=log t 属于 A（可全纯延拓，各分支的零点只有 t=1），但 log(log t) 不在 V：
            沿 g0=|t|=1/2、g1=|t-1|=1/2（基点 1/2）连续追踪分支，[g0^d, g1^d] 的差 = -2 pi i d（d=1,2,3）≠ 0；
            对照：log t 本身的交换子为 0
  R-sqrt    附注 (d) 第 1 条可以加强：w(t)=sqrt(t) 时 log w = (log t)/2 属于 A，所以 1F1(a;b;sqrt t) 的交换子为 0
            （属于 A）；而 log(1+sqrt t) 的交换子 = ±2 pi i ≠ 0（属于 V 但不属于 A）
  R-triv    §0 的两个平凡化恒等式：1F1(-1;be;w) = 1 - w/be（精确），1F1(1;1;w) = e^w（数值）
"""
import cmath
import math
import os
import sys
import time
from decimal import Decimal as D
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cdec import CD, set_prec, cexp, clog, pi, sincos  # noqa: E402

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')

PREC = 40
set_prec(PREC)
RES = []


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


def contour_res(fun, center, radius, N=160):
    """(1/2 pi i) ∮ fun(s) ds，圆周逆时针，梯形公式。"""
    tot = CD(0)
    for j in range(N):
        s_, c_ = sincos(2 * pi() * j / N)
        u = CD(c_, s_)
        s = CD.of(center) + CD(radius) * u
        ds = CD(radius) * u * CD(0, 2 * pi() / N)
        tot = tot + fun(s) * ds
    return tot / CD(0, 2 * pi())


def main():
    t0 = time.time()
    ok = True
    lines = []
    for name, x in (('0.6', CD(D('0.6'))), ('0.6+0.2i', CD(D('0.6'), D('0.2'))), ('-1.5', CD(D('-1.5')))):
        z = CD(1) / (x * x * x)
        lam = (1 - x) * z
        x2 = x * x

        def theta(s):
            return cexp(CD(0) - lam * clog(s) + z * s)

        def gam(s):
            return 1 + x2 * s / ((1 - s) * (1 - s))

        r1 = contour_res(lambda s: theta(s) * gam(s) / s, 1, D('0.3'))
        r2 = contour_res(lambda s: theta(s) * (gam(s) + s / (1 - s)) / s, 1, D('0.3'))
        r3 = contour_res(lambda s: theta(s) / (1 - s), 1, D('0.3'))
        r4 = contour_res(lambda s: gam(s) + s / (1 - s), 1, D('0.3'))
        ez = cexp(z)
        e1 = (r1 - ez).abs() / ez.abs()
        e2 = r2.abs() / ez.abs()
        e3 = (r3 + ez).abs() / ez.abs()
        e4 = (r4 - (x2 - 1)).abs()
        good = e1 < D('1e-30') and e2 < D('1e-30') and e3 < D('1e-30') and e4 < D('1e-30') and (x2 - 1).abs() > D('0.1')
        ok &= good
        lines.append('x=%s: err %.1e/%.1e/%.1e/%.1e，Res rho = %s' % (name, float(e1), float(e2), float(e3), float(e4),
                                                                 '%.4f%+.4fi' % (float((x2 - 1).r), float((x2 - 1).i))))
    report('R-res', ok, 'Res theta*gamma/s = e^z、Res theta*(gamma+s/(1-s))/s = 0、Res theta/(1-s) = -e^z、Res_{t=1}(gamma+t/(1-t)) = x^2-1：'
           + '; '.join(lines))

    # ---------------- 分支追踪（双精度即可，只看 2 pi i 的整数倍） ----------------
    T0 = 0.5
    NPT = 4000

    def path_pts(kind, power=1):
        pts = []
        for rep in range(power):
            for j in range(NPT):
                th = 2 * math.pi * j / NPT
                if kind == 0:
                    pts.append(T0 * cmath.exp(1j * th))
                else:
                    pts.append(1 + (1 - T0) * cmath.exp(1j * (math.pi + th)))
        pts.append(pts[0])
        return pts

    def track_log(values, start):
        """沿离散曲线 values 连续追踪 log：返回终点的 log 值（起点取 start）。"""
        cur = start
        prev = values[0]
        for v in values[1:]:
            dv = cmath.log(v / prev)          # 相邻点比值接近 1，主值即正确增量
            cur = cur + dv
            prev = v
        return cur

    def loglog_word(word_powers):
        """word_powers：[(kind, d), ...]；返回沿该字延拓后 (log t, log log t) 的值。"""
        lt = cmath.log(T0)                     # log t 的初值（主值，实数）
        llt = cmath.log(lt)                    # log log t 的初值（主值）
        for kind, d in word_powers:
            pts = path_pts(kind, d)
            # 先追踪 log t，再用它追踪 log(log t)
            lts = [lt]
            prev = pts[0]
            cur = lt
            for p in pts[1:]:
                cur = cur + cmath.log(p / prev)
                prev = p
                lts.append(cur)
            llt = track_log(lts, llt)
            lt = cur
        return lt, llt

    okl = True
    vals = []
    for d in (1, 2, 3):
        lt_a, ll_a = loglog_word([(0, d), (1, d)])
        lt_b, ll_b = loglog_word([(1, d), (0, d)])
        diff_ll = ll_a - ll_b
        diff_lt = lt_a - lt_b
        vals.append('d=%d: %.6f%+.6fi' % (d, diff_ll.real, diff_ll.imag))
        okl &= abs(diff_lt) < 1e-9 and abs(diff_ll - (-2j * math.pi * d)) < 1e-6
    report('R-loglog', okl, 'log(log t)：[g0^d,g1^d] 的差（先 g0^d 后 g1^d 减先 g1^d 后 g0^d）= ' + '；'.join(vals) +
           '（预测 -2 pi i d）；log t 本身的差为 0')

    # sqrt：1F1(1/3;1/2;sqrt t) 与 log(1+sqrt t)
    def f11(a, b, w, terms=200):
        s, term = 0j, 1 + 0j
        for n in range(terms):
            s += term
            term *= (a + n) / (b + n) * w / (n + 1)
        return s

    def sqrt_word(word):
        """追踪 sqrt t（由 log t/2）与 log(1+sqrt t)。"""
        lt = cmath.log(T0)
        l1 = cmath.log(1 + cmath.sqrt(T0))
        for kind in word:
            pts = path_pts(kind, 1)
            prev = pts[0]
            cur = lt
            vals_1p = [1 + cmath.exp(lt / 2)]
            for p in pts[1:]:
                cur = cur + cmath.log(p / prev)
                prev = p
                vals_1p.append(1 + cmath.exp(cur / 2))
            l1 = track_log(vals_1p, l1)
            lt = cur
        return cmath.exp(lt / 2), l1

    sa, la = sqrt_word([0, 1])
    sb, lb = sqrt_word([1, 0])
    f_a = f11(1 / 3, 1 / 2, sa)
    f_b = f11(1 / 3, 1 / 2, sb)
    oks = abs(f_a - f_b) < 1e-9 and abs(abs(la - lb) - 2 * math.pi) < 1e-6
    report('R-sqrt', oks, '1F1(1/3;1/2;sqrt t) 的交换子 = %.1e（为 0，属于 A）；log(1+sqrt t) 的交换子 = %.6f%+.6fi（±2 pi i，不属于 A）'
           % (abs(f_a - f_b), (la - lb).real, (la - lb).imag))

    # §0 平凡化
    okt = True
    for be in (Fr(3, 7), Fr(-5, 2), Fr(11, 3)):
        for w in (Fr(1), Fr(2, 9), Fr(-4)):
            s, term = Fr(0), Fr(1)
            for n in range(6):
                s += term
                term *= Fr(-1 + n) / (be + n) * w / (n + 1)
            okt &= (s == 1 - w / be)
    for w in (0.3, -2.0, 1.7 + 0.4j):
        okt &= abs(f11(1, 1, w) - cmath.exp(w)) < 1e-12
    report('R-triv', okt, '1F1(-1;be;w) = 1 - w/be（9 组有理数，精确）；1F1(1;1;w) = e^w（3 个 w）')
    print('time %.1fs' % (time.time() - t0))
    print('SUMMARY s11-b6b remarks_check pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
    return 0 if all(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
