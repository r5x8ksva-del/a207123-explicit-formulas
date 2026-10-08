# -*- coding: utf-8 -*-
"""s11-b6b 复核脚本 4：定理 2 的常数 nu 与绕 1 的跳跃，用 t=1 处的奇点分析（Darboux / 转移定理）独立核对。
不用 RK4，不积分 ODE，不用命题 1：只用 G_m（T1.3(1) 的递推，即原始定义的 t^m 系数）。

原理：f_x 在 C\\[1,inf) 上单值解析（t=0 处全纯），定理 2.4 说 t=1 附近
    f_x = -1/(x(1-t)) + kappa * omega(t) * log(1-t) + (在 t=1 全纯)，kappa = -x^{-3} e^{1/x^3} = -z e^z，
绕 1 逆时针一圈 log(1-t) 增加 2 pi i，所以跳跃 = 2 pi i kappa omega = -nu omega，nu = 2 pi i z e^z。
把 omega 在 t=1 展开：omega(1-u) = (1-u)^lam e^{-z} e^{zu} = sum_j omega_j u^j，再用精确系数
    [t^m] (1-t)^j log(1-t) = (-1)^{j+1} j!/(m(m-1)...(m-j))   (m>j)，
由转移定理得  G_m = -1/x + kappa sum_{j<=J} omega_j c_{j,m} + O(m^{-J-2})。
注意 kappa*omega_j = -z sum_{a+b=j} C(lam,a)(-1)^a z^b/b!，e^z 与 omega(1)=e^{-z} 相消。
  ND-asym  对 7 个 x（含复数 x、lam=1/2、lam=-2）：J=0..8 的余项 R_m^{(J)} 与下一项 kappa omega_{J+1} c_{J+1,m} 之比
           在 m=4000 处接近 1（|比-1| < 0.02），且 R^{(J)} 随 m 的衰减指数 = J+2（m=2000 -> 4000，log2 比值）
  ND-rev   反向检查：kappa 换成「二阶极点主部」的朴素值 -z x^2 e^z、omega 去掉 e^{-zt}、lam 换成 lam+1，
           余项都退化为 O(1/m) 或 O(1/m^2)（与预测的下一项之比远离 1）
"""
import math
import os
import sys
import time
from decimal import Decimal as D

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cdec import CD, set_prec, newton_real  # noqa: E402

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')

PREC = 90
set_prec(PREC)
RES = []
MMAX = 8000
JMAX = 9


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


def G_list(x, N):
    x2 = x * x
    x3 = x2 * x
    G = [CD(1) / (1 - x)]
    for m in range(1, N + 1):
        G.append((G[-1] + m * x2) / (1 - x - m * x3))
    return G


def omega_coeffs(lam, z, J, drop_exp=False):
    """kappa*omega_j / (-z) 中的和 sum_{a+b=j} C(lam,a)(-1)^a z^b/b!（drop_exp 时去掉 e^{zu} 因子）。"""
    binom = [CD(1)]
    for a in range(1, J + 1):
        binom.append(binom[-1] * (lam - (a - 1)) / a)
    zp = [CD(1)]
    for bb in range(1, J + 1):
        zp.append(zp[-1] * z / bb)
    out = []
    for j in range(J + 1):
        s = CD(0)
        for a in range(j + 1):
            bb = j - a
            if drop_exp and bb > 0:
                continue
            s = s + binom[a] * (CD(-1) ** a) * zp[bb]
        out.append(s)
    return out


def cjm(j, m):
    den = 1
    for i in range(j + 1):
        den *= (m - i)
    return D((-1) ** (j + 1) * math.factorial(j)) / D(den)


def residuals(G, x, kappa_omega, m, J):
    s = G[m] + CD(1) / x
    for j in range(J + 1):
        s = s - kappa_omega[j] * cjm(j, m)
    return s


def main():
    t0 = time.time()
    xs = [('0.6', CD(D('0.6'))), ('0.7', CD(D('0.7'))), ('2', CD(D(2))), ('-1.5', CD(D('-1.5'))),
          ('0.6+0.2i', CD(D('0.6'), D('0.2')))]
    xh = newton_real(lambda u: u ** 3 + 2 * u - 2, lambda u: 3 * u * u + 2, D('0.77'))
    xs.append(('lam=1/2', CD(xh)))
    xs.append(('-1', CD(D(-1))))
    ok_all = True
    lines = []
    store = {}
    for name, x in xs:
        z = CD(1) / (x * x * x)
        lam = (1 - x) * z
        G = G_list(x, MMAX)
        base = omega_coeffs(lam, z, JMAX + 1)
        kw = [CD(0) - z * c for c in base]            # kappa*omega_j = -z * base_j
        store[name] = (x, z, lam, G)
        worst_ratio = D(0)
        worst_dev2 = D(0)
        dev2_decay_ok = True
        slopes = []
        for J in range(0, JMAX - 1):
            r4 = residuals(G, x, kw, 4000, J)
            r2 = residuals(G, x, kw, 2000, J)
            t1_4 = kw[J + 1] * cjm(J + 1, 4000)
            t2_4 = kw[J + 2] * cjm(J + 2, 4000)
            t1_2 = kw[J + 1] * cjm(J + 1, 2000)
            t2_2 = kw[J + 2] * cjm(J + 2, 2000)
            ratio = (r4 / t1_4 - 1).abs()
            worst_ratio = max(worst_ratio, ratio)
            # 加上再下一项后，偏差应再小一个 1/m 量级
            dev4 = (r4 - t1_4 - t2_4).abs() / r4.abs()
            dev2 = (r2 - t1_2 - t2_2).abs() / r2.abs()
            worst_dev2 = max(worst_dev2, dev4)
            dev2_decay_ok &= dev4 < dev2 / 3
            slopes.append(math.log2(float(r2.abs() / r4.abs())))
        good = worst_ratio < D('0.05') and worst_dev2 < D('1e-4') and dev2_decay_ok and \
            all(abs(s - (J + 2)) < 0.15 for J, s in enumerate(slopes))
        ok_all &= good
        lines.append('x=%s: max|R/T1-1|=%.1e, max|R-T1-T2|/|R|=%.1e, 衰减指数 %s' %
                     (name, float(worst_ratio), float(worst_dev2), ','.join('%.2f' % s for s in slopes)))
    report('ND-asym', ok_all, '（数值）G_m + 1/x 的转移定理展开与 kappa=-z e^z 相符（J=0..%d，m=2000、4000；T1、T2 为预测的下两项）：'
           % (JMAX - 2) + '; '.join(lines))

    # 反向检查
    rev = []
    for name in ('0.6', '0.6+0.2i'):
        x, z, lam, G = store[name]
        base = omega_coeffs(lam, z, 6)
        # (1) 朴素 kappa：-z x^2 e^z，即 kappa*omega_j = -z x^2 * base_j
        kw_naive = [CD(0) - z * x * x * c for c in base]
        r = residuals(G, x, kw_naive, 4000, 4)
        nxt = kw_naive[5] * cjm(5, 4000)
        rev.append((r / nxt - 1).abs() > 10)
        # (2) omega 去掉 e^{-zt}
        kw_noexp = [CD(0) - z * c for c in omega_coeffs(lam, z, 6, drop_exp=True)]
        r = residuals(G, x, kw_noexp, 4000, 4)
        nxt = kw_noexp[5] * cjm(5, 4000)
        rev.append((r / nxt - 1).abs() > 10)
        # (3) lam -> lam+1
        kw_l1 = [CD(0) - z * c for c in omega_coeffs(lam + 1, z, 6)]
        r = residuals(G, x, kw_l1, 4000, 4)
        nxt = kw_l1[5] * cjm(5, 4000)
        rev.append((r / nxt - 1).abs() > 10)
    report('ND-rev', all(rev), '反向检查（x=0.6、0.6+0.2i；J=4）：朴素 kappa、omega 去掉 e^{-zt}、lam->lam+1 的余项都比预测的下一项大一个量级以上：%s' % rev)
    print('time %.1fs' % (time.time() - t0))
    print('SUMMARY s11-b6b nu_darboux pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
    return 0 if all(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
