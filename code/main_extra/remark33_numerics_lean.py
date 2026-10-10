# -*- coding: utf-8 -*-
r"""注记 3.3 的数值（Lean 续作第十五项）：用精确分数选出 ρ_m、c_m、κ_m（1 ≤ m ≤ 24）的有理区间，核对论文注记 3.3 的
全部数值说法，并生成 `lean/A207123/AsympNumerics.lean` 里的数值部分。

论文注记 3.3 的数值说法（「≈」按四舍五入理解为误差小于末位的半个单位）：
  ρ_1 ≈ 1.46557，c_1 ≈ 2.20961，c_2 ≈ 7.84112，c_3 ≈ 28.97686；
  1 ≤ m ≤ 24 内 κ_m 随 m 递增，κ_1 ≈ 0.453，κ_4 ≈ 1.745，κ_24 ≈ 9.869；
  相对误差 U_k(m)/(c_m ρ_m^k) − 1：k = 3m 时 m = 2 约 −0.36、m = 24 约 −0.996；k = 10m 时约 −0.05 与 −0.41。
做法（与 Lean 里的证明一一对应）：
  ρ_m ∈ (lo, hi)：lo³ − lo² < m < hi³ − hi²（lo ≥ 1；y³ − y² 在 y ≥ 1 上严格增）。
  c_m = N(ρ_m)/D(ρ_m)，N(x) = x^{3m+3} + Σ_{j=1}^m j·m^{\underline j}·x^{3(m−j)+1}，D(x) = m!(x² + 3m)，两者在 x > 0 上增，
  故 N(lo)/D(hi) ≤ c_m ≤ N(hi)/D(lo)；取 A ≤ N(lo)/D(hi)、B ≥ N(hi)/D(lo) 为较短的分数。
  κ_m = c_{m−1}ρ_{m−1}³/c_m ∈ (A_{m−1}·lo_{m−1}³/B_m, B_{m−1}·hi_{m−1}³/A_m)（m = 1 时 c_0 = ρ_0 = 1）。
  U_k(m)/(c_m ρ_m^k) ∈ [U/(B·hi^k), U/(A·lo^k)]，U 的精确值按引理 1 递推。
用法（在任务 C 根目录）：py -3.14 code/main_extra/remark33_numerics_lean.py [--lean]
"""
import sys
from fractions import Fraction as F
from math import factorial, perm

M = 24
RHO_DIGITS = 12       # ρ 的区间宽 10^-12
C_SIG = 14            # A、B 的有效数字
K_SIG = 10            # κ 区间端点的有效数字


def rho_interval(m):
    lo, hi = F(1), F(m + 2)
    while hi - lo > F(1, 10 ** (RHO_DIGITS + 2)):
        mid = (lo + hi) / 2
        if mid ** 3 - mid ** 2 < m:
            lo = mid
        else:
            hi = mid
    s = 10 ** RHO_DIGITS
    L = F((lo * s).numerator // (lo * s).denominator, s)          # 向下取整
    H = L + F(1, s)
    if L ** 3 - L ** 2 >= m:          # 根恰为端点（如 ρ_4 = 2）时往外挪一格
        L -= F(1, s)
    if H ** 3 - H ** 2 <= m:
        H += F(1, s)
    assert L ** 3 - L ** 2 < m < H ** 3 - H ** 2 and L >= 1
    return L, H


def N(m, x):
    return x ** (3 * m + 3) + sum(j * perm(m, j) * x ** (3 * (m - j) + 1) for j in range(1, m + 1))


def Dn(m, x):
    return factorial(m) * (x ** 2 + 3 * m)


def round_sig(x, sig, up):
    """把正分数 x 按 sig 位有效数字向下（up=False）或向上取成 a/10^e。"""
    e = len(str(x.numerator // x.denominator)) if x >= 1 else 0
    scale = 10 ** (sig - e) if sig - e >= 0 else None
    if scale is None:
        scale = F(1, 10 ** (e - sig))
    y = x * scale
    q = y.numerator // y.denominator
    if up and q * y.denominator != y.numerator:
        q += 1
    return F(q) / scale


def ucols(Mx, K):
    cols = [[1] * (K + 1)]
    for m in range(Mx):
        p = cols[-1]
        v = [1]
        for k in range(1, K + 1):
            three = v[k - 3] if k >= 3 else (1 if k == 2 else 0)
            v.append(p[k] + v[k - 1] + (m + 1) * three)
        cols.append(v)
    return cols


def frac_lean(x):
    return '(%d / %d : ℚ)' % (x.numerator, x.denominator) if x.denominator != 1 else '(%d : ℚ)' % x.numerator


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    ok = True
    R, Cb, Kb = {}, {}, {}
    R[0] = (F(1), F(1))
    Cb[0] = (F(1), F(1))
    for m in range(1, M + 1):
        L, H = rho_interval(m)
        R[m] = (L, H)
        lo_q, hi_q = N(m, L) / Dn(m, H), N(m, H) / Dn(m, L)
        A, B = round_sig(lo_q, C_SIG, False), round_sig(hi_q, C_SIG, True)
        assert A <= lo_q and hi_q <= B and A > 0
        Cb[m] = (A, B)
    for m in range(1, M + 1):
        if m == 1:
            klo, khi = 1 / Cb[1][1], 1 / Cb[1][0]
        else:
            a, b = Cb[m - 1]
            lo, hi = R[m - 1]
            a2, b2 = Cb[m]
            klo, khi = a * lo ** 3 / b2, b * hi ** 3 / a2
        KL, KU = round_sig(klo, K_SIG, False), round_sig(khi, K_SIG, True)
        assert KL <= klo and khi <= KU
        Kb[m] = (KL, KU)

    def within(lo, hi, target, eps):
        return target - eps < lo and hi < target + eps

    checks = []
    checks.append(('rho_1 ≈ 1.46557', within(*R[1], F('1.46557'), F(5, 10 ** 6))))
    for m, t in [(1, '2.20961'), (2, '7.84112'), (3, '28.97686')]:
        checks.append(('c_%d ≈ %s' % (m, t), within(*Cb[m], F(t), F(5, 10 ** 6))))
    for m, t in [(1, '0.453'), (4, '1.745'), (24, '9.869')]:
        checks.append(('kappa_%d ≈ %s' % (m, t), within(*Kb[m], F(t), F(5, 10 ** 4))))
    checks.append(('kappa increasing on 1..24', all(Kb[m][1] < Kb[m + 1][0] for m in range(1, M))))
    cols = ucols(M, 240)
    rel = [(2, 6, '-0.36', 3), (24, 72, '-0.996', 4), (2, 20, '-0.05', 3), (24, 240, '-0.41', 3)]   # ε = 5/10^e
    Uv = {}
    for m, k, t, e in rel:
        eps = F(5, 10 ** e)
        u = cols[m][k]
        Uv[(m, k)] = u
        A, B = Cb[m]
        L, H = R[m]
        rlo, rhi = F(u) / (B * H ** k), F(u) / (A * L ** k)
        checks.append(('relerr m=%d k=%d ≈ %s' % (m, k, t), within(rlo - 1, rhi - 1, F(t), eps)))
    for name, good in checks:
        print('%-30s %s' % (name, 'PASS' if good else 'FAIL'))
        ok &= good
    print('ALL PASS' if ok else 'SOME FAIL')
    if '--lean' not in sys.argv:
        return
    out = []
    out.append('/-! ## 数值：ρ_m、c_m、κ_m 的有理区间（1 ≤ m ≤ 24；由 `code/main_extra/remark33_numerics_lean.py` 生成） -/')
    for m in range(1, M + 1):
        L, H = R[m]
        out.append('')
        out.append('/-- 辅助引理（注记 3.3）：`ρ_%d` 的有理区间。 -/' % m)
        out.append('theorem rho_bnd_%d : (%s : ℝ) < rho %d ∧ rho %d < (%s : ℝ) :=' %
                   (m, frac_lean(L), m, m, frac_lean(H)))
        out.append('  ⟨lt_rho_of_cubic (by norm_num) (by norm_num), rho_lt_of_cubic (by norm_num) (by norm_num)⟩')
    for m in range(1, M + 1):
        L, H = R[m]
        A, B = Cb[m]
        out.append('')
        out.append('/-- 辅助引理（注记 3.3）：`c_%d` 的有理区间。 -/' % m)
        out.append('theorem cm_bnd_%d : (%s : ℝ) < cm %d ∧ cm %d < (%s : ℝ) :=' %
                   (m, frac_lean(A), m, m, frac_lean(B)))
        out.append('  cm_mem rho_bnd_%d (by norm_num) (by decide +kernel) (by decide +kernel)' % m)
    for m in range(1, M + 1):
        KL, KU = Kb[m]
        out.append('')
        out.append('/-- 辅助引理（注记 3.3）：`κ_%d` 的有理区间。 -/' % m)
        out.append('theorem kappa_bnd_%d : (%s : ℝ) < kappaConst %d ∧ kappaConst %d < (%s : ℝ) :=' %
                   (m, frac_lean(KL), m, m, frac_lean(KU)))
        if m == 1:
            out.append('  kappa_one_mem cm_bnd_1 (by norm_num) (by norm_num) (by norm_num)')
        else:
            out.append('  kappa_mem (m := %d) cm_bnd_%d rho_bnd_%d cm_bnd_%d (by norm_num) (by norm_num) (by norm_num)'
                       % (m, m - 1, m - 1, m))
            out.append('    (by norm_num) (by norm_num)')
    for (m, k), u in Uv.items():
        out.append('')
        out.append('/-- 辅助引理（注记 3.3）：`U_{%d}(%d)` 的精确值（`Ucol` 在内核里算）。 -/' % (k, m))
        out.append('theorem U_%d_%d : U %d %d = %d := by' % (k, m, k, m, u))
        out.append('  rw [U_eq_Ucol_getD %d %d %d le_rfl]' % (k, m, k))
        out.append('  decide +kernel')
    names = {1: 'one', 2: 'two', 3: 'three', 4: 'four', 24: 'twentyfour'}
    out.append('')
    out.append('/-! ## 论文注记 3.3 的数值说法 -/')
    out.append('')
    out.append('/-- **注记 3.3**（数值）：`ρ_1 ≈ 1.46557`。 -/')
    out.append('theorem rho_one_approx : |rho 1 - 1.46557| < 5 / 10 ^ 6 :=')
    out.append('  approx_of_bounds rho_bnd_1.1 rho_bnd_1.2 (by norm_num) (by norm_num)')
    for m, t in [(1, '2.20961'), (2, '7.84112'), (3, '28.97686')]:
        out.append('')
        out.append('/-- **注记 3.3**（数值）：`c_%d ≈ %s`。 -/' % (m, t))
        out.append('theorem cm_%s_approx : |cm %d - %s| < 5 / 10 ^ 6 :=' % (names[m], m, t))
        out.append('  approx_of_bounds cm_bnd_%d.1 cm_bnd_%d.2 (by norm_num) (by norm_num)' % (m, m))
    for m, t in [(1, '0.453'), (4, '1.745'), (24, '9.869')]:
        out.append('')
        out.append('/-- **注记 3.3**（数值）：`κ_%d ≈ %s`。 -/' % (m, t))
        out.append('theorem kappa_%s_approx : |kappaConst %d - %s| < 5 / 10 ^ 4 :=' % (names[m], m, t))
        out.append('  approx_of_bounds kappa_bnd_%d.1 kappa_bnd_%d.2 (by norm_num) (by norm_num)' % (m, m))
    out.append('')
    out.append('/-- **注记 3.3**（数值）：在 `1 ≤ m ≤ 24` 内 `κ_m` 随 `m` 递增。 -/')
    out.append('theorem kappa_increasing : ∀ m, 1 ≤ m → m < 24 → kappaConst m < kappaConst (m + 1) := by')
    out.append('  intro m h1 h2')
    out.append('  interval_cases m')
    for m in range(1, M):
        out.append('  · exact lt_trans kappa_bnd_%d.2 (lt_trans (by norm_num) kappa_bnd_%d.1)' % (m, m + 1))
    rnames = {(2, 6): 'two_six', (24, 72): 'twentyfour_seventytwo', (2, 20): 'two_twenty',
              (24, 240): 'twentyfour_twoforty'}
    for m, k, t, e in rel:
        tq = F(t)
        out.append('')
        out.append('/-- **注记 3.3**（数值）：`U_{%d}(%d)/(c_%d ρ_%d^{%d}) − 1 ≈ %s`（`k = %s`）。 -/'
                   % (k, m, m, m, k, t, '3m' if k == 3 * m else '10m'))
        out.append('theorem relerr_%s : |(U %d %d : ℝ) / (cm %d * rho %d ^ %d) - 1 - (%s)| < 5 / 10 ^ %d := by'
                   % (rnames[(m, k)], k, m, m, m, k, t, e))
        out.append('  have h := relerr_of_bounds (u := U %d %d) (k := %d) (t := %d / %d) (ε := 5 / %d) cm_bnd_%d rho_bnd_%d'
                   % (k, m, k, tq.numerator, tq.denominator, 10 ** e, m, m))
        out.append('    (by norm_num) (by norm_num) (by rw [U_%d_%d]; norm_num) (by rw [U_%d_%d]; decide +kernel)'
                   % (k, m, k, m))
        out.append('    (by rw [U_%d_%d]; decide +kernel)' % (k, m))
        out.append('  have e1 : ((%d / %d : ℚ) : ℝ) = %s := by norm_num' % (tq.numerator, tq.denominator, t))
        out.append('  have e2 : ((5 / %d : ℚ) : ℝ) = 5 / 10 ^ %d := by norm_num' % (10 ** e, e))
        out.append('  rwa [e1, e2] at h')
    print('\n'.join(out))


if __name__ == '__main__':
    main()
