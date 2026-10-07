# -*- coding: utf-8 -*-
"""s8-b3 独立核对 2：纤维的浮点检验（numpy；不是证明的一部分）。

不导入 code/tableB 下的任何脚本。对 alpha,beta>=0、1<=alpha+beta<=NMAX 的每个形状：
  f1  纤维 {v=v0}，v=x^(a+b)/(1-x)^b，v0=v(xi)=xi^e（e=a-2b）：
      alpha>=1 时为 F=x^(a+b)-xi^e(1-x)^b 的根；alpha=0 时为 x_zeta=zeta/(xi^2+zeta)（与 F 的根逐个对照）
  f2  Vieta：prod eta = (-1)^(n+1) xi^e，prod (1-eta) = F(1)
  f3  对每个纤维点令 w:=(1-eta)/eta^3（复数），核对 (★) eta^e = w^beta xi^e 与
      prod w^beta = (-1)^((n+1)e) xi^(-3 beta e)（beta>=1）
  f4  统计「w 是正整数」的纤维点个数；全部纤维点都满足的形状应只有 (1,0)、(0,1)、(2,1)
  f5  情形 (IV)：w_zeta zeta^3 = xi^2 (xi^2+zeta)^2，(-1)^(beta+1) prod w_zeta = a^2，
      |a(xi)| 与 |a(xi_2)| 的估计
  f6  F 是否有重根（最小根距）
"""
import sys
from math import comb
import numpy as np

P = np.polynomial.polynomial
NMAX = 20
TOL_INT = 1e-7

FAILS = []


def check(name, ok, info=''):
    print(('PASS ' if ok else 'FAIL ') + name + ((' | ' + info) if info else ''))
    if not ok:
        FAILS.append(name)


def real_xi():
    z = 0.68
    for _ in range(60):
        z -= (z ** 3 + z - 1) / (3 * z * z + 1)
    return z


xi = real_xi()
cr = [r for r in np.roots([1, 0, 1, -1]) if abs(r.imag) > 1e-9]
xi2 = complex(cr[0])
for _ in range(20):
    xi2 -= (xi2 ** 3 + xi2 - 1) / (3 * xi2 * xi2 + 1)


def F_coeffs(alpha, beta):
    """低次在前的 F(x)=x^(a+b) - v0 (1-x)^b。"""
    n = alpha + beta
    e = alpha - 2 * beta
    v0 = xi ** e
    c = np.zeros(n + 1, dtype=complex)
    c[n] += 1
    for j in range(beta + 1):
        c[j] -= v0 * comb(beta, j) * (-1) ** j
    return c, v0


def refine(c, z, it=30):
    dc = P.polyder(c)
    for _ in range(it):
        fz = P.polyval(z, c)
        dz = P.polyval(z, dc)
        if dz == 0:
            break
        step = fz / dz
        z = z - step
        if abs(step) < 1e-17 * max(1.0, abs(z)):
            break
    return z


def v_of(alpha, beta, x):
    return x ** (alpha + beta) / (1 - x) ** beta


def is_pos_int(w):
    r = round(w.real)
    return r >= 1 and abs(w.imag) < TOL_INT * max(1.0, abs(w)) and abs(w.real - r) < TOL_INT * max(1.0, abs(w))


def main():
    NSTRICT = 14          # 双精度在 alpha+beta<=14 内足够准；更高次只作参考
    full_shapes = {}
    err = {}              # n -> [res_v, vieta, star, prodw(log), xzeta]
    min_gap = 1e9
    neg_min = [1e9]
    multi_rows = []
    for n in range(1, NMAX + 1):
        err[n] = [0.0, 0.0, 0.0, 0.0, 0.0]
        for alpha in range(0, n + 1):
            beta = n - alpha
            e = alpha - 2 * beta
            if alpha >= 1:
                c, v0 = F_coeffs(alpha, beta)
                roots = np.array([refine(c, z) for z in P.polyroots(c)])
            else:
                v0 = xi ** (-2 * beta)
                zetas = np.exp(2j * np.pi * np.arange(beta) / beta)
                roots = zetas / (xi ** 2 + zetas)
                # 与 F 的根对照（F 次数 beta，首项 1-v0(-1)^beta）
                c = np.zeros(beta + 1, dtype=complex)
                c[beta] += 1
                for j in range(beta + 1):
                    c[j] -= v0 * comb(beta, j) * (-1) ** j
                froots = np.array([refine(c, z) for z in P.polyroots(c)])
                dmatch = max(min(abs(froots - r)) for r in roots)
                err[n][4] = max(err[n][4], dmatch)
            # f1 纤维残差
            rv = max(abs(v_of(alpha, beta, r) - v0) / abs(v0) for r in roots)
            err[n][0] = max(err[n][0], rv)
            # f6 重根
            if len(roots) >= 2 and n <= NSTRICT:
                gaps = [abs(roots[i] - roots[j]) for i in range(len(roots)) for j in range(i)]
                min_gap = min(min_gap, min(gaps))
            # f2 Vieta（alpha>=1：F 首一）
            if alpha >= 1:
                pe = np.prod(roots)
                target = (-1) ** (n + 1) * xi ** e
                dv = abs(pe - target) / abs(target)
                F1 = 1.0 if beta >= 1 else 1 - xi ** alpha
                d1 = abs(np.prod(1 - roots) - F1) / abs(F1)
                err[n][1] = max(err[n][1], dv, d1)
            ws = (1 - roots) / roots ** 3
            # f3 (★) 与乘积（乘积在对数里比较，避免溢出）
            if beta >= 1 and alpha >= 1:
                star = max(abs(r ** e / (w ** beta * xi ** e) - 1) for r, w in zip(roots, ws))
                err[n][2] = max(err[n][2], star)
                logabs = beta * float(np.sum(np.log(np.abs(ws))))
                phase = beta * float(np.sum(np.angle(ws)))
                tgt_log = -3 * beta * e * np.log(xi)
                tgt_sign = (-1) ** ((n + 1) * e)
                dphase = abs(np.exp(1j * phase) - tgt_sign)
                dl = abs(logabs - tgt_log) / max(1.0, abs(tgt_log))
                err[n][3] = max(err[n][3], dl, dphase)
                if n <= NSTRICT:
                    wrong = abs(logabs - (tgt_log - np.log(xi))) / max(1.0, abs(tgt_log))
                    neg_min[0] = min(neg_min[0], wrong)
            # f4 计数
            cnt = sum(1 for w in ws if is_pos_int(w))
            wint = sorted(int(round(w.real)) for w in ws if is_pos_int(w))
            if cnt == len(roots):
                full_shapes[(alpha, beta)] = n
            if cnt >= 2 and n <= 20:
                multi_rows.append((alpha, beta, len(roots), cnt, wint))
            if cnt == 0 and n <= NSTRICT:
                check('f4-xi-itself-in-fiber-(%d,%d)' % (alpha, beta), False, 'no integral point found')
    def mx(i, lo, hi):
        return max(err[n][i] for n in range(lo, hi + 1))
    print('  per-degree max errors [res_v, vieta, star, prodw, xzeta]:')
    for n in range(1, NMAX + 1):
        print('   n=%2d  ' % n + '  '.join('%.1e' % x for x in err[n]))
    check('f1-fiber-residual', mx(0, 1, NSTRICT) < 1e-6, 'alpha+beta<=%d: %.2e (<=%d: %.2e)' % (NSTRICT, mx(0, 1, NSTRICT), NMAX, mx(0, 1, NMAX)))
    check('f1-alpha0-xzeta-equals-roots-of-F', mx(4, 1, NSTRICT) < 1e-6, 'beta<=%d: %.2e (<=%d: %.2e)' % (NSTRICT, mx(4, 1, NSTRICT), NMAX, mx(4, 1, NMAX)))
    check('f2-vieta', mx(1, 1, NSTRICT) < 1e-6, 'alpha+beta<=%d: %.2e' % (NSTRICT, mx(1, 1, NSTRICT)))
    check('f3-star', mx(2, 1, NSTRICT) < 1e-6, 'alpha+beta<=%d: %.2e' % (NSTRICT, mx(2, 1, NSTRICT)))
    check('f3-prod-w^beta', mx(3, 1, NSTRICT) < 1e-6, 'alpha+beta<=%d: %.2e (log|.| rel err and phase)' % (NSTRICT, mx(3, 1, NSTRICT)))
    check('f6-no-repeated-fiber-points', min_gap > 1e-4, 'alpha+beta<=%d: min distance between fiber points = %.3e' % (NSTRICT, min_gap))
    check('neg-prod-w^beta-with-exponent-shifted-by-1-detected', neg_min[0] > 1e-4, 'min rel log err with wrong exponent = %.2e' % neg_min[0])
    fs = sorted(k for k, v in full_shapes.items() if v <= NSTRICT)
    check('f4-only-(1,0),(0,1),(2,1)-fully-integral', fs == [(0, 1), (1, 0), (2, 1)],
          'alpha+beta<=%d: %s; (alpha+beta<=%d, low precision: %s)' % (NSTRICT, fs, NMAX, sorted(full_shapes)))
    print('  shapes (alpha+beta<=20) with >=2 fiber points having w in Z>=1  (alpha,beta,#fiber,#int,w):')
    for row in multi_rows:
        print('   ', row)
    print('  all other shapes: exactly one such point (xi itself, w=1)')
    # f5 情形 (IV)
    max_r1 = 0.0
    max_r2 = 0.0
    for beta in range(2, 41):
        zetas = np.exp(2j * np.pi * np.arange(beta) / beta)
        xs = zetas / (xi ** 2 + zetas)
        ws = (1 - xs) / xs ** 3
        r1 = max(abs(w * z ** 3 - xi ** 2 * (xi ** 2 + z) ** 2) for w, z in zip(ws, zetas))
        max_r1 = max(max_r1, r1)
        a = xi ** beta * (xi ** (2 * beta) - (-1) ** beta)
        lhs = (-1) ** (beta + 1) * np.prod(ws)
        r2 = abs(lhs - a * a) / abs(a * a)
        max_r2 = max(max_r2, r2)
    check('f5-IV-wzeta-identity', max_r1 < 1e-9, 'max |w z^3 - xi^2(xi^2+z)^2| = %.2e (2<=beta<=40)' % max_r1)
    check('f5-IV-product-identity', max_r2 < 1e-8, 'max rel |(-1)^(b+1) prod w - a^2| = %.2e' % max_r2)
    ok_b = True
    rows = []
    for beta in range(3, 42, 2):
        a1 = abs(xi ** (3 * beta) + xi ** beta)
        a2 = abs(xi2 ** beta * (xi2 ** (2 * beta) + 1))
        lb = xi ** (-beta / 2) * (xi ** (-beta) - 1)
        rows.append((beta, a1, a2, lb))
        if not (a1 < 0.64 and a2 >= lb - 1e-9 and lb > 3.8):
            ok_b = False
    check('f5-IV-bounds', ok_b, 'beta=3: |a(xi)|=%.4f, |a(xi2)|=%.4f, bound=%.4f' % rows[0][1:])
    check('f5-|xi2|^2=1/xi', abs(abs(xi2) ** 2 - 1 / xi) < 1e-12, '|xi2|^2=%.15f, 1/xi=%.15f' % (abs(xi2) ** 2, 1 / xi))
    # 情形 (II)：xi*zeta 不是任何 b_w 的根（w<=2000）
    mn = 1e9
    for alpha in range(2, 40):
        for k in range(1, alpha):
            z = xi * np.exp(2j * np.pi * k / alpha)
            wv = np.arange(1, 2001)
            mn = min(mn, float(np.min(np.abs(1 - z - wv * z ** 3))))
    check('f7-II-xi*zeta-not-root', mn > 1e-3, 'min |b_w(xi zeta)| over 2<=alpha<40, zeta!=1, w<=2000: %.4f' % mn)
    # 情形 (III)：u(eta)=zeta 的点不是 b_w 的根
    mn3 = 1e9
    for beta in range(2, 15):
        for k in range(1, beta):
            z = np.exp(2j * np.pi * k / beta)
            for eta in np.roots([1, z, -z]):          # x^3 + z x - z = x^3 - z(1-x)
                wv = np.arange(1, 2001)
                mn3 = min(mn3, float(np.min(np.abs(1 - eta - wv * eta ** 3))))
    check('f8-III-u=zeta-not-root', mn3 > 1e-3, 'min |b_w(eta)| over 2<=beta<15, u(eta)=zeta!=1, w<=2000: %.4f' % mn3)
    print('xi = %.15f, xi2 = %s' % (xi, xi2))
    print('SUMMARY: %d FAIL' % len(FAILS), FAILS)
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
