# -*- coding: utf-8 -*-
"""s15-b13 / E：notes/17 §3–§5 的几何条件与常数（独立实现；不导入项目代码）。

  e-c123     对 13 个 τ（10^-6…10^6，含 W(1/e)）显式构造 δ_1、η，逐条核对 (C1)：θ_±∈(0,π) 且 ∉{arg w_l°}∪{π/2}；
             (C2)：|w|<=R_1 内 Λ 只有 w_0°、w_{-1}°，且 w_{-1}° 不在扇形里，圆 |w|=R_1 上没有 Λ 的点；(C3)：R_1cos2η>=R+δ_1/2；
             引理 3.1 的 α=inf_l∠(w_l°,e^{iθ_±})>0
  e-phi      取 φ=θ_0：a_s=Re(c_0ω^s e^{-2iφ/3}) 的最大值唯一且在 s*=0，cos(φ/3)>0；三个立方根方向 arg y≠π
             （夹角条件 |sin((arg y-π)/2)| 的下界）；在 τ∈[1e-8,1e8] 的 4001 个对数网格点上都成立，
             并核对我的论证：ψ_0:=arg c_0-2θ_0/3∈(-π/3,π/3)（θ_0>arg c_0，且 τ>W(1/e) 时 arg c_0>1.18）
  e-kappa0   半平面判据给出主导方向 ν=0 上 κ'=0（对一切 φ∈(0,π)：sin(-φ/6-π/2)<0），ν=1、2 上 κ'=1——
             所以 §5 的下界在 s*=0 时总是“鞍点项主导”的情形（c-kappa 已在 4 个 τ 上数值证实）
  e-W        τ=W(1/e)：Re w_0°=0，θ_0=π/2，l>=0 的 w_l° 都在虚轴上，R=π，|w_1°|=3π>R_1
  e-nums     §6 的数：R(-100)^{-1/3}、R(-3)^{-1/3}、8/√(4+π²)、Γ(1+k/3)/(n!n^{r/3})→1、(★) 的换算
  e-rev      反向：故意取 η 过大（越过 w_1° 的辐角或违反 (C3)）、φ 取在 a_s 打平处，检查都应失败
用法：py -3.14 code/review/s15-b13/e_geometry.py
"""
import cmath
import math
import sys

from s15_common import Reporter, setup_stdout

setup_stdout()
W_E = 0.2784645427610738


def wl(tau, l):
    return math.log(1 / tau) - 1 - tau + 1j * math.pi * (2 * l + 1)


def c0(tau):
    return math.log(1 / tau) + 1j * math.pi


def args_list(tau, L=20000):
    return [cmath.phase(wl(tau, l)) for l in range(-L, L + 1)]


def choose(tau):
    R = abs(wl(tau, 0))
    R2 = abs(wl(tau, 1))
    th0 = cmath.phase(wl(tau, 0))
    delta1 = min(0.5 * (R2 - R), 0.05 * R)
    R1 = R + delta1
    # (C1)：θ_± 不碰 arg w_l°（l>=1 的辐角单调趋于 π/2）与 π/2
    gaps = [th0, math.pi - th0]
    a1 = cmath.phase(wl(tau, 1))
    if abs(a1 - th0) > 1e-12:
        gaps.append(abs(a1 - th0))
    if abs(th0 - math.pi / 2) > 1e-12:
        gaps.append(abs(th0 - math.pi / 2))
    eta = 0.4 * min(gaps)
    # (C3)
    need = (R + delta1 / 2) / R1
    eta = min(eta, 0.4 * math.acos(need))
    return R, R1, th0, delta1, eta


def check_C(tau, R, R1, th0, delta1, eta):
    ok = True
    thp, thm = th0 + eta, th0 - eta
    ok &= 0 < thm < thp < math.pi
    ok &= abs(thp - math.pi / 2) > 1e-12 and abs(thm - math.pi / 2) > 1e-12
    angs = args_list(tau, 3000)
    ok &= all(abs(a - thp) > 1e-12 and abs(a - thm) > 1e-12 for a in angs)
    # (C2)
    inside = [l for l in range(-3000, 3001) if abs(wl(tau, l)) <= R1]
    ok &= sorted(inside) == [-1, 0]
    ok &= not (thm <= cmath.phase(wl(tau, -1)) <= thp)
    ok &= all(abs(abs(wl(tau, l)) - R1) > 1e-9 for l in range(-3000, 3001))
    # (C3)
    ok &= R1 * math.cos(2 * eta) >= R + delta1 / 2
    # 引理 3.1 的 α
    wrap = lambda d: abs((d + math.pi) % (2 * math.pi) - math.pi)
    alpha = min(min(wrap(a - th) for a in angs) for th in (thp, thm))
    alpha = min(alpha, abs(thp - math.pi / 2), abs(thm - math.pi / 2))   # l→∞ 的极限方向
    ok &= alpha > 0
    return ok, alpha


def a_s(tau, phi):
    return [(c0(tau) * cmath.exp(2j * math.pi * s / 3) * cmath.exp(-2j * phi / 3)).real for s in range(3)]


def main():
    rep = Reporter('s15_e_geometry')

    # ---- e-c123
    taus = [1e-6, 1e-3, 0.01, 0.1, W_E, 0.5, 1.0, 2.0, 3.0, 10.0, 100.0, 1e3, 1e6]
    ok_c, rows = True, []
    for tau in taus:
        R, R1, th0, d1, eta = choose(tau)
        ok, alpha = check_C(tau, R, R1, th0, d1, eta)
        ok_c &= ok
        rows.append('τ=%.3g:R=%.3f,δ1=%.2e,η=%.2e,α=%.2e,%s' % (tau, R, d1, eta, alpha, 'ok' if ok else 'BAD'))
    rep.check('e-c123', ok_c, '(C1)(C2)(C3) 与引理 3.1 的 α>0：' + '；'.join(rows))

    # ---- e-phi / e-kappa0
    ok_phi, ok_k0, worst_gap, worst_ang, worst_psi = True, True, 9, 9, 9
    ntau = 4001
    for i in range(ntau):
        tau = 10 ** (-8 + 16 * i / (ntau - 1))
        th0 = cmath.phase(wl(tau, 0))
        a = a_s(tau, th0)
        srt = sorted(a)
        gap = srt[2] - srt[1]
        ok_phi &= a.index(max(a)) == 0 and gap > 0 and math.cos(th0 / 3) > 0
        worst_gap = min(worst_gap, gap / abs(c0(tau)))
        psi0 = cmath.phase(c0(tau)) - 2 * th0 / 3
        worst_psi = min(worst_psi, math.pi / 3 - abs(psi0))
        ok_phi &= th0 > cmath.phase(c0(tau)) and (tau <= W_E or cmath.phase(c0(tau)) > 1.18)
        for nu in range(3):
            argy = th0 / 3 + 2 * math.pi * nu / 3
            worst_ang = min(worst_ang, abs(math.sin((argy - math.pi) / 2)))
            D = cmath.exp(1j * (th0 + math.pi) / 2)
            k = 1 if (cmath.exp(1j * argy) / D).imag > 0 else 0
            ok_k0 &= k == (0 if nu == 0 else 1)
    th1 = cmath.phase(wl(1.0, 0))
    ang_tau1 = min(abs(math.sin((th1 / 3 + 2 * math.pi * nu / 3 - math.pi) / 2)) for nu in range(3))
    ok_phi &= worst_ang > 0
    rep.check('e-phi', ok_phi and worst_psi > 0, 'φ=θ_0 时 s*=0 唯一最大（4001 个 τ∈[1e-8,1e8]），最小相对差距 (a_0-次大)/|c_0|=%.3f；'
              'ψ_0 到 ±π/3 的最小距离 %.3f；θ_0>arg c_0；夹角条件 |sin((arg y-π)/2)| 对每个 τ 为正，网格上最小 %.1e（τ→∞ 时 θ_0→π，ν=1 的 arg y→π，'
              '下界不一致，但定理只需固定 τ；τ=1 时为 %.3f）' % (worst_gap, worst_psi, worst_ang, ang_tau1))
    rep.check('e-kappa0', ok_k0, '半平面判据：所有 τ 上 ν=0 时 κ\'=0，ν=1,2 时 κ\'=1 %s（故 §5 的下界在 s*=0 时总是鞍点项主导）' % ok_k0)

    # ---- e-W
    w0 = wl(W_E, 0)
    okW = abs(w0.real) < 1e-15 and abs(cmath.phase(w0) - math.pi / 2) < 1e-15 and abs(abs(w0) - math.pi) < 1e-14
    okW &= all(abs(wl(W_E, l).real) < 1e-15 for l in range(0, 200))
    R, R1, th0, d1, eta = choose(W_E)
    okW &= abs(abs(wl(W_E, 1)) - 3 * math.pi) < 1e-13 and abs(wl(W_E, 1)) > R1
    okW &= abs(W_E * math.exp(W_E) - math.exp(-1)) < 1e-16
    rep.check('e-W', okW, 'τ=W(1/e)：Re w_0°=%.1e，θ_0-π/2=%.1e，l>=0 的 w_l° 都在虚轴上，R=π，|w_1°|=3π>R_1=%.4f %s'
              % (w0.real, cmath.phase(w0) - math.pi / 2, R1, okW))

    # ---- e-nums
    r100 = abs(wl(100.0, 0)) ** (-1 / 3)
    r3 = abs(wl(3.0, 0)) ** (-1 / 3)
    star = 8 / math.sqrt(4 + math.pi ** 2)
    # 笔记 §6 写 R(-100)^{-1/3}=0.2116；真值 0.211534…，四舍五入应为 0.2115（notes/09 写的是 0.2115）。这里核对真值，并把笔误单独报告。
    note_slip = round(r100, 4) != 0.2116
    okn = abs(r100 - 0.21153) < 1e-5 and abs(r3 - 0.5507) < 5e-5 and abs(abs(wl(1.0, 0)) - math.sqrt(4 + math.pi ** 2)) < 1e-15
    gam = [math.exp(math.lgamma(1 + (3 * n + r) / 3) - math.lgamma(n + 1) - (r / 3) * math.log(n)) for n in (10 ** 4,) for r in range(3)]
    okn &= all(abs(g - 1) < 1e-4 for g in gam)
    # (★) 的换算：|h_{3n+r}/n!|^{1/n}=2^{(3n+r+1)/n}|f_{3n+r}/n!|^{1/n} → 8/R
    okn &= abs(8 / abs(wl(1.0, 0)) - star) < 1e-15
    rep.check('e-nums', okn, 'R(-100)^{-1/3}=%.6f（笔记 §6 写 0.2116，%s），R(-3)^{-1/3}=%.5f（笔记 0.5507，一致），8/√(4+π²)=%.6f，Γ(1+k/3)/(n!n^{r/3}) 在 n=10^4：%s'
              % (r100, '四舍五入应为 0.2115，笔误' if note_slip else '一致', r3, star, ','.join('%.6f' % g for g in gam)))

    # ---- e-rev
    tau = 1.0
    R, R1, th0, d1, eta = choose(tau)
    eta_hit = th0 - cmath.phase(wl(tau, 1))                                     # θ_- 恰好等于 arg w_1°
    bad1, _ = check_C(tau, R, R1, th0, d1, eta_hit)
    bad2, _ = check_C(tau, R, R1, th0, d1, 0.4)                                 # 违反 (C3)
    R1big = abs(wl(tau, 1)) + 0.1                                               # R_1 越过 |w_1°|，(C2) 失败
    bad3, _ = check_C(tau, R, R1big, th0, R1big - R, eta)
    phi_tie = 1.5 * (cmath.phase(c0(tau)) + math.pi / 3)                        # a_0=a_2 打平
    a = a_s(tau, phi_tie)
    tie = abs(sorted(a)[2] - sorted(a)[1]) < 1e-12
    rep.check('e-rev', (not bad1) and (not bad2) and (not bad3) and tie,
              '反向：θ_- 取成 arg w_1° 时 (C1) 失败 %s；η=0.4 时 (C3) 失败 %s；R_1>|w_1°| 时 (C2) 失败 %s；φ=%.4f 时 a_s 最大值不唯一 %s'
              % (not bad1, not bad2, not bad3, phi_tie, tie))
    return rep.summary()


if __name__ == '__main__':
    sys.exit(main())
