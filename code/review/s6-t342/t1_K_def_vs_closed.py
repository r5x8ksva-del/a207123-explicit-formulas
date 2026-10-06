# -*- coding: utf-8 -*-
"""s6-t342 / t1：K(x) 的定义 vs 闭式 Γ(−λ)[1+λx^5 J(x)]。

定义（a=1 的形式，不用任何变形）：
    K(x) = Σ_{n≥0} φ_n/(n−λ) + ∫_1^∞ τ^{−λ−1} φ(τ) dτ,   φ(τ) = e^{−τ} − x^5 τ e^{−τ}(1+x^3τ)^{−2}
  · φ_n 用精确有理数：φ_n = (−1)^n/n! − x^5 c_n，c_n 由 (1+x^3τ)^2 ψ = τe^{−τ} 的三项递推
    c_n = d_n − 2x^3 c_{n−1} − x^6 c_{n−2}（d_n=(−1)^{n−1}/(n−1)!）精确得到（t0 已与直接卷积比对）；
    每项 φ_n/(n−λ) 精确算出后舍入一次到工作精度再求和。
  · 级数尾项用 Cauchy 估计严格控制：|φ_n| ≤ M(r)/r^n，M(r)=e^r(1+x^5 r/(1−x^3 r)^2)，1<r<1/x^3，
      Σ_{n>N} |φ_n|/|n−λ| ≤ M(r) r^{−(N+1)} / ((1−1/r)(N+1−λ))      （N+1>λ）
    对 r 在一组候选值上取最小。
  · 积分：τ = 1+v，v ∈ [0,∞)，Ooura–Mori 指数型双指数公式，尺度 1/(λ+2)；
    同一组节点上同时算 B0=∫_1^∞τ^{−λ−1}e^{−τ}、B5=∫_1^∞τ^{−λ}e^{−τ}(1+x^3τ)^{−2}，B = B0 − x^5 B5。
  · 工作精度 = 抵消位数 + 50 + 20 位保护位，抵消位数 = log10(max(|级数|,|积分|)/|K|)。
闭式：Γ(−λ) 用反射公式（另用递推算法复核），J 用同一积分程序在两种尺度（1/x 与 1/(2x)）下各算一次。
诊断（拆成两半分别核对）：
    Prym 半：Σ(−1)^n/(n!(n−λ)) + B0  应等于 Γ(−λ)；
    x^5 半：Σ c_n/(n−λ) + B5        应等于 Γ(1−λ)·J = −λΓ(−λ)J。
用法：t1_K_def_vs_closed.py [x 的序号列表，如 0 或 1,2,3]；默认全部。
"""
import sys, os, time, math
sys.stdout.reconfigure(line_buffering=True)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import Decimal as D, getcontext, localcontext
from fractions import Fraction as Fr
import hp

X_LIST = [Fr(3, 20), Fr(9, 50), Fr(21, 100), Fr(23, 100), Fr(7, 25), Fr(7, 20), Fr(2, 5),
          Fr(11, 20), Fr(3, 5), Fr(7, 10), Fr(3, 4), Fr(4, 5), Fr(17, 20), Fr(9, 10)]
AGREE_DIGITS = 45          # 目标：定义与闭式一致到这么多位
FAIL = 0


def lam_of(x):
    return (1 - x) / x ** 3


def J_quad(x, lam, digits, scale):
    """J = ∫_0^∞ w e^{−w} (1+x^3 w)^{λ−1} dw。"""
    x3 = hp.dec(x ** 3)
    lm1 = hp.dec(lam - 1)
    f = lambda w: [w * (-w + lm1 * (1 + x3 * w).ln()).exp()]
    q, e, info = hp.de_exp_quad_vec(f, 1, digits, scale=scale)
    return q[0], e[0], info


def closed_form(x, lam, digits=80):
    """返回 (Γ(−λ), J, 1+λx^5J, K_closed, J 两种尺度之差, Γ 两种算法之差, 信息)。精度 digits+15。"""
    with localcontext() as ctx:
        ctx.prec = digits + 15
        G = hp.gamma_neg_frac(lam)
        G2 = hp.gamma_neg_frac_rec(lam)
        xd = hp.dec(x)
        J1, e1, i1 = J_quad(x, lam, digits + 5, scale=1 / xd)
        J2, e2, i2 = J_quad(x, lam, digits + 5, scale=1 / (2 * xd))
        R = 1 + hp.dec(lam * x ** 5) * J1
        K = G * R
        return dict(G=G, J=J1, R=R, K=K, dJ=abs(J1 - J2) / J1, dG=abs(G - G2) / abs(G),
                    Jerr=e1 / J1, info="J:" + i1 + "/" + i2)


def log10_cauchy_tail(x, lam, N):
    """log10 of min_r M(r) r^{−(N+1)} / ((1−1/r)(N+1−λ))，用 float 对数计算（只作上界，留余量）。"""
    xf = float(x)
    R = 1.0 / xf ** 3
    best = float("inf")
    cands = [R * (1 - 2.0 ** -k) for k in range(1, 30)] + [min(N + 1.0, R * 0.999)]
    for r in cands:
        if not (1.0 < r < R):
            continue
        logM = r / math.log(10) + math.log10(1 + xf ** 5 * r / (1 - xf ** 3 * r) ** 2)
        val = logM - (N + 1) * math.log10(r) - math.log10(1 - 1 / r) - math.log10(N + 1 - float(lam))
        best = min(best, val)
    return best + 1e-6 * abs(best) + 1e-9          # 浮点余量


def run_one(idx, x):
    global FAIL
    T = time.time()
    lam = lam_of(x)
    fl = int(lam)
    frac = lam - fl
    print("=" * 100)
    print("[%d] x = %s = %.4f   lambda = %s = %.10f   frac(lambda) = %.4f   ceil = %d"
          % (idx, x, float(x), lam, float(lam), float(frac), fl + 1))
    if frac == 0:
        print("    lambda 是整数，跳过")
        return
    # ---- 闭式
    cf = closed_form(x, lam)
    getcontext().prec = 40
    print("    closed: Gamma(-lam) = %s   J = %s   ratio K/Gamma(-lam) = 1+lam x^5 J = %s"
          % (hp.sci(cf["G"], 25), hp.sci(cf["J"], 25), hp.sci(cf["R"], 25)))
    print("            K_closed = %s" % hp.sci(cf["K"], 30))
    print("            self-checks: Gamma reflection vs recursion rel %s ; J two scales rel %s ; J quad est %s ; %s"
          % (hp.sci(cf["dG"], 2), hp.sci(cf["dJ"], 2), hp.sci(cf["Jerr"], 2), cf["info"]))
    Kc = cf["K"]
    # ---- 精度
    lamf = float(lam)
    log_piece = math.log10(math.exp(-1) / lamf)            # |积分| ≤ e^{−1}/λ
    cancel = max(0, math.ceil(log_piece - hp.log10_abs(Kc)))
    P = cancel + AGREE_DIGITS + 5
    getcontext().prec = P + 20
    eps_abs_log = hp.log10_abs(Kc) - (AGREE_DIGITS + 3)      # 允许的绝对误差 10^{eps_abs_log}
    print("    precision: cancellation ~%d digits -> working %d (+20 guard); target abs err 1e%.1f"
          % (cancel, P, eps_abs_log))
    # ---- 级数（精确 φ_n）
    t0 = time.time()
    x3, x5, x6 = x ** 3, x ** 5, x ** 6
    A0 = D(0)
    A5 = D(0)
    c_m1 = Fr(0)    # c_{n−1}
    c_m2 = Fr(0)    # c_{n−2}
    fact = 1
    n = 0
    absmax_term = D(0)
    while True:
        if n >= 1:
            fact *= n
            dn = Fr((-1) ** (n - 1), fact // n)          # (n−1)!
        else:
            dn = Fr(0)
        cn = dn - 2 * x3 * c_m1 - x6 * c_m2
        e_term = Fr((-1) ** n, fact) / (n - lam)
        c_term = cn / (n - lam)
        te = hp.dec(e_term)
        tc = hp.dec(c_term)
        A0 += te
        A5 += tc
        absmax_term = max(absmax_term, abs(te), abs(tc))
        c_m2, c_m1 = c_m1, cn
        if n > lam + 1 and n % 5 == 0:
            if log10_cauchy_tail(x, lam, n) < eps_abs_log - 2:
                break
        n += 1
        if n > 20000:
            raise RuntimeError("级数项数过多")
    N = n
    tail_log = log10_cauchy_tail(x, lam, N)
    A = A0 - hp.dec(x5) * A5
    print("    series: N = %d terms (exact phi_n), Cauchy tail bound 1e%.1f, |A| = %s, max|term| = %s  (%.1fs)"
          % (N + 1, tail_log, hp.sci(A, 6), hp.sci(absmax_term, 3), time.time() - t0))
    # ---- 积分
    t0 = time.time()
    lamd = hp.dec(lam)
    x3d = hp.dec(x3)

    def fB(v):
        tau = 1 + v
        E = (-(lamd + 1) * tau.ln() - tau).exp()           # τ^{−λ−1} e^{−τ}
        den = 1 + x3d * tau
        return [E, E * tau / (den * den)]
    getcontext().prec = P + 20
    Bmag = math.exp(-1) / (lamf + 1)
    digits_B = max(30, math.ceil(math.log10(Bmag) - eps_abs_log) + 2)
    (B0, B5), (e0, e5), infoB = hp.de_exp_quad_vec(fB, 2, digits_B, scale=1 / (lamd + 2))
    B = B0 - hp.dec(x5) * B5
    errB = e0 + hp.dec(x5) * e5
    print("    integral: B0 = %s  B5 = %s  B = %s ; quad est |dB| <= %s ; %s  (%.1fs)"
          % (hp.sci(B0, 8), hp.sci(B5, 8), hp.sci(B, 8), hp.sci(errB, 3), infoB, time.time() - t0))
    # ---- 合成
    Kd = A + B
    prym = A0 + B0
    half5 = A5 + B5
    getcontext().prec = 60
    rel_K = abs(Kd - Kc) / abs(Kc)
    G = cf["G"]
    rel_prym = abs(prym - G) / abs(G)
    target5 = -hp.dec(lam) * G * cf["J"]
    rel_5 = abs(half5 - target5) / abs(target5)
    budget = (errB + D(10) ** D(repr(tail_log)) + D(N + 1) * absmax_term * D(10) ** (-(P + 19))) / abs(Kc)
    print("    K_def    = %s" % hp.sci(Kd, 30))
    print("    K_closed = %s" % hp.sci(Kc, 30))
    print("    rel |K_def - K_closed|/|K| = %s    (error budget of K_def / |K| <= %s)" % (hp.sci(rel_K, 3), hp.sci(budget, 3)))
    print("    diagnostics: Prym half rel dev %s ; x^5 half vs Gamma(1-lam) J rel dev %s" % (hp.sci(rel_prym, 3), hp.sci(rel_5, 3)))
    R = cf["R"]
    xf = float(x)
    ok_main = rel_K < D(10) ** -(AGREE_DIGITS - 5)
    ok_ratio = (R > 1) and (R < 2 - hp.dec(x))
    sgn_expected = 1 if (fl + 1) % 2 == 0 else -1
    ok_sign = (Kd > 0) == (sgn_expected > 0)
    print("    corollary: 1 < K/Gamma(-lam) = %s < 2-x = %s : %s ; sign(K_def) = %s, (-1)^ceil(lam) = %+d : %s"
          % (hp.sci(R, 12), float(2 - x), ok_ratio, "+" if Kd > 0 else "-", sgn_expected, ok_sign))
    ok = ok_main and ok_ratio and ok_sign and rel_prym < D(10) ** -(AGREE_DIGITS - 5) and rel_5 < D(10) ** -(AGREE_DIGITS - 7)
    print(("PASS" if ok else "FAIL") + " x=%s  rel_dev=%s  digits_used=%d  (%.1fs)" % (x, hp.sci(rel_K, 3), P + 20, time.time() - T))
    if not ok:
        FAIL += 1
    return rel_K


if __name__ == "__main__":
    T0 = time.time()
    if len(sys.argv) > 1:
        idxs = [int(s) for s in sys.argv[1].split(",")]
    else:
        idxs = list(range(len(X_LIST)))
    worst = D(0)
    for i in idxs:
        r = run_one(i, X_LIST[i])
        if r is not None:
            worst = max(worst, r)
    print("=" * 100)
    print("SUMMARY t1: points=%d FAIL=%d worst rel dev=%s elapsed %.1fs" % (len(idxs), FAIL, hp.sci(worst, 3), time.time() - T0))
    sys.exit(1 if FAIL else 0)
