# -*- coding: utf-8 -*-
"""s6-t342 / t2：端到端核对  I(x,t) − 𝒮(x,t)  =  x^{−3} e^a a^λ Γ(−λ)[1+λx^5 J(x)]，a = −t/x^3。

  · I：直接对原始 σ 积分做复合 tanh-sinh（不经 τ 代换）：
        I = x^{−3} ∫_0^∞ exp((t(e^σ−1) − (1−x)σ)/x^3) g(t e^σ) dσ,  g(w)=1+x^2 w/(1−w)^2；
    截断点 Σ 用严格界：被积函数 ≤ e^{−λσ} e^{−a(e^σ−1)}（t<0 时 0<g≤1），
        ∫_Σ^∞ ≤ e^{−λΣ} e^{−Σ} e^{−a(e^Σ−1)} / a。
    另用 τ 形式 x^{−3}e^a a^λ ∫_a^∞ τ^{−λ−1}φ(τ)dτ（指数型 DE）独立再算一次，核对 I 的表示。
  · 𝒮：精确有理部分和。x=p/q，t=r/s，b_i=β_i/q^3，β_i=q^3−pq^2−ip^3，Π_m=∏_{i≤m}β_i，
        ω_0=q^2，ω_m=q^3 ω_{m−1}+p^2 m Π_{m−1}，G_m = W_m/P_m = q ω_m/Π_m，
        部分和 S_m = Num_m/(s^m Π_m)，Num_0=q^3，Num_m = s β_m Num_{m−1} + r^m q ω_m（纯整数，无舍入）。
    前 60 项另用定义 W_m/P_m（Fraction）逐项核对。
    尾项严格界：由 b_m G_m = G_{m−1} + x^2 m，当 x^3 M > 2−x 时对一切 m ≥ M 有
        |G_m| ≤ β := max(|G_M|, x^2 M/(x^3 M − 2 + x))，故 Σ_{m>M}|t^m G_m| ≤ β|t|^{M+1}/(1−|t|)。
  · 闭式：Γ(−λ)（反射公式），J（指数型 DE），80 位。
"""
import sys, os, time, math
sys.stdout.reconfigure(line_buffering=True)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import Decimal as D, getcontext, localcontext
from fractions import Fraction as Fr
import hp

PAIRS = [(Fr(9, 10), Fr(-1, 2)), (Fr(4, 5), Fr(-3, 10)), (Fr(4, 5), Fr(-4, 5)), (Fr(7, 10), Fr(-1, 2)),
         (Fr(3, 5), Fr(-1, 4)), (Fr(2, 5), Fr(-3, 5)), (Fr(7, 20), Fr(-1, 20)), (Fr(21, 100), Fr(-1, 10)),
         (Fr(3, 20), Fr(-1, 4)),
         # 下面两组是报告 T3.4(3)(5) 里印出的数值例（读完 r-c3a §4 和报告 T3.4 段之后加的，用来核对报告里的数字）：
         # (3/5,−1/2)：报告称 𝒮 = −1057.81087256356…；(21/100,−1/20)：报告称差值 3.81401776553037367e−62
         (Fr(3, 5), Fr(-1, 2)), (Fr(21, 100), Fr(-1, 20))]
AGREE = 50
FAIL = 0


def lam_of(x):
    return (1 - x) / x ** 3


def closed(x, t, lam, a, digits=80):
    with localcontext() as ctx:
        ctx.prec = digits + 15
        G = hp.gamma_neg_frac(lam)
        x3 = hp.dec(x ** 3)
        lm1 = hp.dec(lam - 1)
        f = lambda w: [w * (-w + lm1 * (1 + x3 * w).ln()).exp()]
        (J,), (eJ,), _ = hp.de_exp_quad_vec(f, 1, digits + 5, scale=1 / hp.dec(x))
        ad = hp.dec(a)
        pref = (ad + hp.dec(lam) * ad.ln()).exp() / x3          # x^{−3} e^a a^λ
        C = pref * G * (1 + hp.dec(lam * x ** 5) * J)
        return C, pref, G, J


def S_exact(x, t, lam, C_abs_log, want_digits):
    """精确部分和；返回 (Num, Den, M, tail_log10, 前 60 项核对是否通过)。"""
    p, q = x.numerator, x.denominator
    r, s = t.numerator, t.denominator
    q3 = q ** 3
    beta = lambda i: q3 - p * q * q - i * p ** 3
    omega = q * q
    Pi = beta(0)
    Num = q3
    Den = Pi
    rpow = 1
    # 定义核对（Fraction）
    xf, tf = Fr(x), Fr(t)
    b = lambda i: 1 - xf - i * xf ** 3
    P_def = b(0)
    W_def = Fr(1)
    ok_def = (Fr(q * omega, Pi) == W_def / P_def)
    G_prev = Fr(q * omega, Pi)
    m = 0
    x3, x2 = float(x) ** 3, float(x) ** 2
    absT = abs(float(t))
    target = C_abs_log - want_digits
    while True:
        m += 1
        Pi_prev = Pi
        bm = beta(m)
        omega = q3 * omega + p * p * m * Pi_prev
        Pi = Pi_prev * bm
        rpow *= r
        Num = s * bm * Num + rpow * q * omega
        Den = Den * s * bm
        if m <= 60:
            W_def = W_def + xf ** 2 * m * P_def       # W_m = W_{m−1} + x^2 m P_{m−1}
            P_def = P_def * b(m)
            Gm = Fr(q * omega, Pi)
            ok_def = ok_def and (Gm == W_def / P_def) and (Gm == (G_prev + xf ** 2 * m) / b(m))
            G_prev = Gm
        if x3 * m > 2 - float(x) + 1e-9:
            with localcontext() as ctx:
                ctx.prec = 30
                Gm_abs = abs(D(q * omega) / D(Pi))
                fM = D(repr(x2 * m / (x3 * m - 2 + float(x))))
                betaB = max(Gm_abs, fM) * D('1.01')
                tail = betaB * D(repr(absT)) ** (m + 1) / (1 - D(repr(absT)))
                tl = float(tail.log10())
            if tl < target:
                return Num, Den, m, tl, ok_def
        if m > 100000:
            raise RuntimeError("𝒮 项数过多")


def I_sigma(x, t, lam, a, digits, tail_target_log):
    """x^{−3}∫_0^∞ exp(−a(e^σ−1) − λσ) g(te^σ) dσ；返回 (I, 误差估计, Σ, 信息)。"""
    ad, lamd, td, x2d = hp.dec(a), hp.dec(lam), hp.dec(t), hp.dec(x * x)
    x3inv = 1 / hp.dec(x ** 3)
    af, lf = float(a), float(lam)
    Sig = 0.25
    while True:   # 严格尾项界：x^{−3} e^{−λΣ} e^{−Σ} e^{−a(e^Σ−1)} / a
        lg = (-lf * Sig - Sig - af * (math.exp(Sig) - 1) - math.log(af) - 3 * math.log(float(x))) / math.log(10)
        if lg < tail_target_log:
            break
        Sig += 0.25

    def f(sig):
        es = sig.exp()
        w = td * es
        g = 1 + x2d * w / ((1 - w) * (1 - w))
        return (-ad * (es - 1) - lamd * sig).exp() * g
    q, e, info = hp.ts_quad_composite(f, D(0), hp.dec(Fr(Sig).limit_denominator(4)), digits, piece=D('0.5'))
    return q * x3inv, e * x3inv, Sig, info


def I_tau(x, t, lam, a, digits):
    """x^{−3} e^a a^λ ∫_a^∞ τ^{−λ−1} φ(τ) dτ，τ = a+v，指数型 DE，尺度 1/((λ+1)/a+1)。"""
    ad, lamd = hp.dec(a), hp.dec(lam)
    x3d, x5d = hp.dec(x ** 3), hp.dec(x ** 5)

    def f(v):
        tau = ad + v
        den = 1 + x3d * tau
        return [(-(lamd + 1) * tau.ln() - tau).exp() * (1 - x5d * tau / (den * den))]
    (q,), (e,), info = hp.de_exp_quad_vec(f, 1, digits, scale=1 / ((lamd + 1) / ad + 1))
    pref = (ad + lamd * ad.ln()).exp() / x3d
    return q * pref, e * pref, info


def run_one(k, x, t):
    global FAIL
    T = time.time()
    lam = lam_of(x)
    a = -t / x ** 3
    print("=" * 100)
    print("[%d] x=%s t=%s  lambda=%.8f (ceil %d)  a=-t/x^3=%s=%.8f" % (k, x, t, float(lam), int(lam) + 1, a, float(a)))
    C, pref, G, J = closed(x, t, lam, a)
    getcontext().prec = 30
    Ilow, _, _, _ = I_sigma(x, t, lam, a, 25, -40)
    logC = hp.log10_abs(C)
    logI = hp.log10_abs(Ilow)
    P = max(0, math.ceil(max(logI, logC) - logC)) + AGREE + 5
    getcontext().prec = P + 20
    print("    closed form C = x^-3 e^a a^lam Gamma(-lam)[1+lam x^5 J] = %s" % hp.sci(C, 30))
    print("    |I| ~ 1e%.1f, |C| ~ 1e%.1f  ->  working precision %d (+20)" % (logI, logC, P))
    t0 = time.time()
    Num, Den, M, tl, ok_def = S_exact(x, t, lam, logC, AGREE + 5)
    S = D(Num) / D(Den)
    print("    S: exact rational partial sum up to m=%d (Den has %d digits), rigorous tail <= 1e%.1f ; first 60 G_m == W_m/P_m and recurrence: %s  (%.1fs)"
          % (M, len(str(abs(Den))), tl, ok_def, time.time() - t0))
    t0 = time.time()
    I, eI, Sig, info = I_sigma(x, t, lam, a, P + 3, logC - AGREE - 8)
    print("    I (sigma form): %s  quad est %s  cutoff Sigma=%.2f  %s  (%.1fs)" % (hp.sci(I, 30), hp.sci(eI, 3), Sig, info, time.time() - t0))
    t0 = time.time()
    with localcontext() as ctx:
        ctx.prec = 70
        It, eIt, infot = I_tau(x, t, lam, a, 60)
    relI = abs(It - I) / abs(I)
    print("    I (tau form x^-3 e^a a^lam int_a^inf tau^(-lam-1) phi): %s  rel diff vs sigma form %s  %s  (%.1fs)"
          % (hp.sci(It, 30), hp.sci(relI, 3), infot, time.time() - t0))
    Dif = I - S
    getcontext().prec = 60
    rel = abs(Dif - C) / abs(C)
    close_IS = abs(Dif) / abs(I)
    print("    S          = %s" % hp.sci(S, 30))
    print("    I - S      = %s" % hp.sci(Dif, 30))
    print("    closed C   = %s" % hp.sci(C, 30))
    print("    |(I-S) - C|/|C| = %s ;  |I-S|/|I| = %s (I and S agree to ~%.0f digits but are not equal)"
          % (hp.sci(rel, 3), hp.sci(close_IS, 3), max(0.0, -hp.log10_abs(close_IS))))
    sgn_exp = 1 if (int(lam) + 1) % 2 == 0 else -1
    ok = rel < D(10) ** -(AGREE - 5) and relI < D(10) ** -55 and ok_def and ((Dif > 0) == (sgn_exp > 0))
    print(("PASS" if ok else "FAIL") + " (x,t)=(%s,%s) rel=%s sign(I-S)=%s (-1)^ceil(lam)=%+d  (%.1fs)"
          % (x, t, hp.sci(rel, 3), "+" if Dif > 0 else "-", sgn_exp, time.time() - T))
    if not ok:
        FAIL += 1
    return rel


if __name__ == "__main__":
    T0 = time.time()
    idxs = [int(s) for s in sys.argv[1].split(",")] if len(sys.argv) > 1 else list(range(len(PAIRS)))
    worst = D(0)
    for k in idxs:
        x, t = PAIRS[k]
        worst = max(worst, run_one(k, x, t))
    print("=" * 100)
    print("SUMMARY t2: pairs=%d FAIL=%d worst rel dev=%s elapsed %.1fs" % (len(idxs), FAIL, hp.sci(worst, 3), time.time() - T0))
    sys.exit(1 if FAIL else 0)
