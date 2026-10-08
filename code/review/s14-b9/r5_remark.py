# -*- coding: utf-8 -*-
"""复核者 s14-b9：§5「附注」的按极点展开 f_k(t)=sum_{j>=0} t^j sum_{σ∈Z_j} γ_j(σ) σ^k e^{-σ^3 t} 的数值核对
（数值佐证，不是证明；不 import 项目代码）。

  r5-remark  t = 1/5、27/100、-1/5，0<=k<=15：50 位 Decimal 复数运算的部分和（j<=J）与精确值 f_k(t)=h_k(t)/(1-t)^{k+1}
             （Fraction）之差；同时用双精度复数重算，看作者报告的 3e-15 / 5e-9 是不是舍入误差的量级
  r5-abs     （信息）c_j = e^{j+O(j^{2/3})} 的数值迹象：(ln c_j - j)/j^{2/3}（j=10..10^4）
"""
import sys
import time
import cmath
from decimal import Decimal as D, getcontext, localcontext
from fractions import Fraction as Fr
from math import factorial, log, exp

sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from s14_common import h_rec_iter  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []
PI = D('3.14159265358979323846264338327950288419716939937510582097494459230781640628620899')


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


def cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def cdiv(a, b):
    d = b[0] * b[0] + b[1] * b[1]
    return ((a[0] * b[0] + a[1] * b[1]) / d, (a[1] * b[0] - a[0] * b[1]) / d)


def cos_sin(y):
    """Decimal 的 cos、sin（先模 2π 化简，再 Taylor）。"""
    with localcontext() as ctx:
        ctx.prec += 10
        twopi = 2 * PI
        y = y - twopi * (y / twopi).to_integral_value()
        c, s = D(1), D(0)
        term = D(1)
        n = 0
        while True:
            n += 1
            term = term * y / n
            if n % 4 == 1:
                s += term
            elif n % 4 == 2:
                c -= term
            elif n % 4 == 3:
                s -= term
            else:
                c += term
            if abs(term) < D(10) ** -(ctx.prec + 2) and n > 4:
                break
    return +c, +s


def cexp(z):
    e = z[0].exp()
    c, s = cos_sin(z[1])
    return (e * c, e * s)


def roots(j):
    if j == 0:
        return [(D(1), D(0))]
    x = D(repr(float(j) ** (1 / 3) + 0.4))
    for _ in range(80):
        x = x - (x * x * x - x * x - j) / (3 * x * x - 2 * x)
    rho = x
    im = ((rho - 1) * (3 * rho + 1)).sqrt() / 2
    re = (1 - rho) / 2
    return [(rho, D(0)), (re, im), (re, -im)]


def gamma2(j, s):
    """第二种形式 [σ^{3j+3}/j! + sum_{l<j}(j-l)σ^{3l+1}/l!]/(σ^2+3j)。"""
    if j == 0:
        return (D(1), D(0))
    s2 = cmul(s, s)
    s3 = cmul(s2, s)
    p = s                                   # σ^{3l+1}/l!，l=0
    num = (D(0), D(0))
    for l in range(j):
        num = (num[0] + (j - l) * p[0], num[1] + (j - l) * p[1])
        p = cmul(p, s3)
        p = (p[0] / (l + 1), p[1] / (l + 1))
    # 循环结束时 p = σ^{3j+1}/j!，再乘 σ^2 得 σ^{3j+3}/j!
    lead = cmul(p, s2)
    num = (num[0] + lead[0], num[1] + lead[1])
    return cdiv(num, (s2[0] + 3 * j, s2[1]))


def main():
    t0 = time.time()
    getcontext().prec = 50
    hs = {k: h for k, h in h_rec_iter(15)}
    cases = [(Fr(1, 5), 160), (Fr(27, 100), 200), (Fr(-1, 5), 700)]
    allok = True
    lines = []
    Jmax = max(J for _, J in cases)
    R = {j: roots(j) for j in range(Jmax + 1)}
    G = {j: [gamma2(j, s) for s in R[j]] for j in range(Jmax + 1)}
    for t, J in cases:
        td = D(t.numerator) / D(t.denominator)
        tf = float(td)
        # 与 k 无关的部分 E = γ_j(σ) t^j e^{-σ^3 t}；σ^k 随 k 递推
        E, P, Ed, Pd = [], [], [], []
        tj = D(1)
        for j in range(J + 1):
            for s, g in zip(R[j], G[j]):
                s3 = cmul(cmul(s, s), s)
                e = cexp((-s3[0] * td, -s3[1] * td))
                term = cmul(g, e)
                E.append(((term[0] * tj, term[1] * tj), s))
                if j <= 300:
                    sd = complex(float(s[0]), float(s[1]))
                    gd = complex(float(g[0]), float(g[1]))
                    Ed.append((gd * cmath.exp(-sd ** 3 * tf) * tf ** j, sd))
            tj *= td
        P = [(D(1), D(0)) for _ in E]
        Pd = [1 + 0j for _ in Ed]
        worst, worst_dbl, biggest = D(0), 0.0, D(0)
        for k in range(0, 16):
            exact = sum(Fr(c) * t ** i for i, c in enumerate(hs[k])) / (1 - t) ** (k + 1)
            ex = D(exact.numerator) / D(exact.denominator)
            tot = (D(0), D(0))
            for idx, ((e, s), pk) in enumerate(zip(E, P)):
                term = cmul(e, pk)
                tot = (tot[0] + term[0], tot[1] + term[1])
                biggest = max(biggest, abs(term[0]))
                P[idx] = cmul(pk, s)
            totd = 0j
            for idx, ((e, sd), pk) in enumerate(zip(Ed, Pd)):
                totd += e * pk
                Pd[idx] = pk * sd
            err = abs(tot[0] - ex) + abs(tot[1])
            worst = max(worst, err / max(D(1), abs(ex)))
            worst_dbl = max(worst_dbl, abs(totd - float(ex)) / max(1.0, abs(float(ex))))
        ok = worst < D(10) ** -25
        allok &= ok
        lines.append('t=%s（j<=%d）：50 位时相对误差 <= %.1e，双精度（j<=%d）时 <= %.1e，最大单项约 %.1e'
                     % (t, J, float(worst), min(J, 300), worst_dbl, float(biggest)))
    report('r5-remark', allok, '；'.join(lines) + '（%.1fs）' % (time.time() - t0))
    # r5-abs：c_j = e^{j+O(j^{2/3})}（附注里绝对收敛论证所用的量级）
    out = []
    for j in (10, 100, 1000, 10000):
        rho = roots(j)[0]
        c = gamma2(j, rho)[0]
        lc = c.ln()
        out.append('j=%d：(ln c_j - j)/j^{2/3}=%.4f，ln(ρ_j^3)-ln j=%.4f' % (j, float((lc - j) / D(j) ** (D(2) / 3)), float((rho[0] ** 3).ln() - D(j).ln())))
    print('信息（r5-abs）：' + '；'.join(out))
    print('total %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
    n_pass = sum(RES)
    print('SUMMARY s14-b9 r5 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
    sys.exit(0 if all(RES) else 1)
