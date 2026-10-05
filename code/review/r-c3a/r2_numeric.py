# -*- coding: utf-8 -*-
"""r-c3a 独立复核脚本 2：解析部分的高精度数值核对（decimal；数值证据，不是证明）。

不调用被复核者代码；π 用 Gauss-Legendre AGM，Bernoulli 数用 Akiyama-Tanigawa，
上不完全 Gamma Γ(s,z) 用 Legendre 连分数（modified Lentz），求积用 Ooura-Mori 的
exp-exp 双指数变换 w = exp(s - exp(-s))（与作者的 exp-sinh 不同）。

核心新结论（复核者推导，见报告）：
  K(x) = Γ(-λ) · [1 + λ x^5 ∫_0^∞ w e^{-w} (1 + x^3 w)^{λ-1} dw]，
因此 1 < K/Γ(-λ) < 1 + (1-x)/(1+x^2)^2 < 2（λ>=1）或 < 1 + (1-x)x^2（λ<1），K ≠ 0。
"""
import sys
import time
from fractions import Fraction as Fr
from decimal import Decimal as D, getcontext
from math import comb, factorial

T0 = time.time()
RES = []


def rep(cid, ok, desc):
    RES.append(bool(ok))
    print(('PASS' if ok else 'FAIL'), cid, desc, flush=True)


def dec(fr):
    return D(fr.numerator) / D(fr.denominator)


def agm_pi():
    getcontext().prec += 15
    a, b, t, p = D(1), D(1) / D(2).sqrt(), D(1) / 4, D(1)
    for _ in range(10):
        an = (a + b) / 2
        b = (a * b).sqrt()
        t -= p * (a - an) ** 2
        a = an
        p *= 2
    r = (a + b) ** 2 / (4 * t)
    getcontext().prec -= 15
    return +r


def dsin(x, PI):
    getcontext().prec += 15
    x = x - 2 * PI * (x / (2 * PI)).to_integral_value()
    s, term, k = D(0), x, 1
    eps = D(10) ** (-(getcontext().prec + 3))
    while abs(term) > eps:
        s += term
        term = -term * x * x / ((2 * k) * (2 * k + 1))
        k += 1
    getcontext().prec -= 15
    return +s


def bernoulli_AT(n):
    A = [Fr(0)] * (n + 1)
    B = []
    for m in range(n + 1):
        A[m] = Fr(1, m + 1)
        for j in range(m, 0, -1):
            A[j - 1] = j * (A[j - 1] - A[j])
        B.append(A[0])
    return B


BER = bernoulli_AT(160)


def lngamma(z, PI):
    getcontext().prec += 20
    z0 = getcontext().prec + 10
    acc = D(0)
    while z < z0:
        acc += z.ln()
        z += 1
    s = (z - D('0.5')) * z.ln() - z + (2 * PI).ln() / 2
    zp, z2 = z, z * z
    for k in range(1, 75):
        s += D(BER[2 * k].numerator) / D(BER[2 * k].denominator) / (D(2 * k) * D(2 * k - 1) * zp)
        zp *= z2
    r = s - acc
    getcontext().prec -= 20
    return +r


def gamma_neg_reflect(lam, PI):
    """Γ(-λ) = -π / (sin(πλ) Γ(1+λ))。"""
    return -PI / (dsin(PI * lam, PI) * lngamma(1 + lam, PI).exp())


def upper_gamma_cf(s, z):
    """Γ(s,z), z>0：Legendre 连分数（modified Lentz）。"""
    getcontext().prec += 20
    tiny = D(10) ** (-(getcontext().prec * 3))
    eps = D(10) ** (-(getcontext().prec - 5))
    b = z + 1 - s
    c = 1 / tiny
    d = 1 / b
    h = d
    i = 1
    while True:
        an = -i * (i - s)
        b += 2
        d = an * d + b
        if abs(d) < tiny:
            d = tiny
        c = b + an / c
        if abs(c) < tiny:
            c = tiny
        d = 1 / d
        delta = d * c
        h *= delta
        if abs(delta - 1) < eps:
            break
        i += 1
        if i > 200000:
            raise RuntimeError('cf')
    r = (-z + s * z.ln()).exp() * h
    getcontext().prec -= 20
    return +r


def de_quad(f, digits, smin=-7, smax=8):
    """∫_0^∞ f(w) dw，w = exp(s - exp(-s))，梯形法则逐级加密（只加奇数节点）。"""
    def node(s):
        es = (-s).exp()
        w = (s - es).exp()
        return f(w) * w * (1 + es)
    h = D(1) / 4
    n = int(D(smax - smin) / h)
    tot = sum(node(D(smin) + h * i) for i in range(n + 1))
    est = tot * h
    for level in range(14):
        h2 = h / 2
        add = sum(node(D(smin) + h2 * (2 * i + 1)) for i in range(n))
        new = est / 2 + h2 * add
        n *= 2
        h = h2
        if abs(new - est) < D(10) ** (-digits):
            return new, abs(new - est)
        est = new
    return est, D(1)


def I_quad(x, t, with_g=True):
    """I(x,t) = x^{-3} ∫_0^∞ exp(-λσ + (t/x^3)(e^σ-1)) g(t e^σ) dσ。"""
    xd, td = dec(x), dec(t)
    lam = (1 - xd) / xd ** 3
    c = td / xd ** 3
    x2 = xd * xd
    lim = -(getcontext().prec * 3)

    def f(sig):
        if sig > 2000:
            return D(0)
        e = sig.exp()
        ex = -lam * sig + c * (e - 1)
        if ex < lim:
            return D(0)
        v = ex.exp()
        if with_g:
            w = td * e
            v *= 1 + x2 * w / (1 - w) ** 2
        return v
    val, err = de_quad(f, getcontext().prec - 6)
    return val / xd ** 3, err


def S_exact(x, t, with_g, M):
    G, P, tot, tp = Fr(1), Fr(1), Fr(0), Fr(1)
    for m in range(M + 1):
        b = 1 - x - m * x ** 3
        P *= b
        G = (G + m * x * x) / b if with_g else 1 / P
        tot += tp * G
        tp *= t
    return tot, G


def S_dec(x, t, with_g):
    """S 到当前精度：部分和 + 我自己的严格尾项界（同 r1）。"""
    M = int((1 - x) / x ** 3) + 30
    while True:
        tot, GM = S_exact(x, t, with_g, M)
        if x ** 3 * (M + 1) > 2 - x:
            C = max(abs(GM), (M + 1) * x * x / (x ** 3 * (M + 1) - 2 + x)) if with_g else abs(GM)
            tb = C * abs(t) ** (M + 1) / (1 - abs(t))
            if tb < Fr(1, 10 ** (getcontext().prec + 8)):
                return dec(tot)
        M += 40


def J_mine(x):
    """J(x) := ∫_0^∞ w e^{-w} (1 + x^3 w)^{λ-1} dw。"""
    xd = dec(x)
    lam = (1 - xd) / xd ** 3
    x3 = xd ** 3
    lim = -(getcontext().prec * 3)

    def f(w):
        ex = -w + (lam - 1) * (1 + x3 * w).ln()
        if ex < lim:
            return D(0)
        return w * ex.exp()
    v, e = de_quad(f, getcontext().prec - 6, smax=10)    # x 小时衰减率仅 ~x+x^3，需要 w 到 ~1e4
    return v


def ratio_formula(x):
    xd = dec(x)
    lam = (1 - xd) / xd ** 3
    return 1 + lam * xd ** 5 * J_mine(x)


def K_author_def(x, with_g=True):
    """作者的定义：K = Σ φ_n/(n-λ) + ∫_1^∞ τ^{-λ-1} φ(τ) dτ（不带 g 时就是 Γ(-λ) 的 Prym 分解）。
    级数用 Fraction 精确求和；尾积分用 DE 求积（w = τ-1）。"""
    lam = (1 - x) / x ** 3
    tol = Fr(1, 10 ** (getcontext().prec + 8))
    ser, n, small = Fr(0), 0, 0
    fac = 1
    while True:
        if n > 0:
            fac *= n
        if with_g:
            ph = sum(Fr((-1) ** (n - j), factorial(n - j)) * (1 if j == 0 else j * x * x * (-x ** 3) ** j) for j in range(n + 1))
        else:
            ph = Fr((-1) ** n, fac)
        term = ph / (n - lam)
        ser += term
        if abs(term) < tol and n > lam + 3:
            small += 1
            if small > 4:
                break
        else:
            small = 0
        n += 1
    xd = dec(x)
    lamd = dec(lam)
    x3, x2 = xd ** 3, xd * xd
    lim = -(getcontext().prec * 3)

    def f(w):
        tau = 1 + w
        ex = -(lamd + 1) * tau.ln() - tau
        if ex < lim:
            return D(0)
        v = ex.exp()
        if with_g:
            z = -x3 * tau
            v *= 1 + x2 * z / (1 - z) ** 2
        return v
    tail, e = de_quad(f, getcontext().prec - 6)
    return dec(ser) + tail


# ============================================================ 1. Γ(-λ) 两种独立算法 + K 闭式
getcontext().prec = 100      # x=3/10 时 Prym 级数与尾积分抵消约 27 位
PI = agm_pi()
ok_g, ok_K, ok_b = True, True, True
lines = []
worstK = D(0)
for x in (Fr(3, 5), Fr(2, 5), Fr(3, 10), Fr(7, 10), Fr(11, 20), Fr(9, 20), Fr(13, 20)):
    lam = (1 - x) / x ** 3
    lamd = dec(lam)
    g1 = gamma_neg_reflect(lamd, PI)
    # Prym + 连分数：Γ(-λ) = Σ (-1)^n/(n!(n-λ)) + Γ(-λ,1)
    ser, n, fac = Fr(0), 0, 1
    while True:
        if n > 0:
            fac *= n
        term = Fr((-1) ** n, fac) / (n - lam)
        ser += term
        if n > lam + 5 and abs(term) < Fr(1, 10 ** 110):
            break
        n += 1
    g2 = dec(ser) + upper_gamma_cf(-lamd, D(1))
    ok_g &= abs(g1 - g2) <= D(10) ** -60 * abs(g1)
    Kg = K_author_def(x, True)
    r_def = Kg / g2
    r_form = ratio_formula(x)
    dev = abs(r_def - r_form)
    worstK = max(worstK, dev)
    ok_K &= dev < D(10) ** -45
    xd = dec(x)
    ub = 1 + (1 - xd) / (1 + xd * xd) ** 2 if lam >= 1 else 1 + (1 - xd) * xd * xd
    ok_b &= 1 < r_form < ub < 2
    lines.append('#   x=%s lam=%.6f  K/Gamma(-lam): author-def %.15f  closed-form %.15f  upper bound %.6f' % (x, float(lam), r_def, r_form, ub))
rep('r2-gamma2', ok_g, '[NUM] Gamma(-lam): reflection+Stirling(AGM pi, Akiyama-Tanigawa Bernoulli) == Prym series + Legendre continued fraction, '
    '7 values of lam, rel 1e-48 (60 digits)')
for L in lines:
    print(L)
rep('r2-K-closed-form', ok_K, '[NUM] NEW: K(x) (author definition: series + tail integral) == Gamma(-lam)[1 + lam x^5 int_0^inf w e^{-w}(1+x^3w)^{lam-1}dw] '
    'at 7 x in [0.3,0.7]; worst abs dev of K/Gamma %.1E (tol 1e-40)' % worstK)
rep('r2-K-bounds', ok_b, '[NUM] 1 < K/Gamma(-lam) < 1+(1-x)/(1+x^2)^2 (lam>=1) or < 1+(1-x)x^2 (lam<1) < 2 at the same 7 points (proved analytically in the report)')

# 作者报的 4 个 K/Γ 数值，以及 x 小时的极限 2
vals = []
for x in (Fr(3, 5), Fr(2, 5), Fr(3, 10), Fr(21, 100), Fr(1, 10), Fr(1, 20)):
    vals.append((x, ratio_formula(x)))
okv = abs(vals[0][1] - D('1.195')) < D('0.0006') and abs(vals[1][1] - D('1.336')) < D('0.0006') and \
    abs(vals[2][1] - D('1.429')) < D('0.0006') and abs(vals[3][1] - D('1.535')) < D('0.0006')
okv &= all(vals[i][1] < vals[i + 1][1] < 2 for i in range(len(vals) - 1))
rep('r2-K-author-values', okv, '[NUM] closed form reproduces the author\'s K/Gamma(-lam) ~ 1.195, 1.336, 1.429, 1.535 (x=3/5,2/5,3/10,21/100) and increases to 2 as x->0: '
    + ', '.join('x=%s:%.6f' % (x, v) for x, v in vals))

# ============================================================ 2. 端到端：I - S 与 I0 - S0（I 用我的 DE 求积，I0 另用连分数）
ok_e, ok_c, ok_q = True, True, True
worst_e, worst_c = D(0), D(0)
for (x, t) in [(Fr(3, 5), Fr(-1, 2)), (Fr(2, 5), Fr(-3, 10)), (Fr(3, 10), Fr(-1, 10))]:
    xd, td = dec(x), dec(t)
    lamd = (1 - xd) / xd ** 3
    a = -td / xd ** 3
    I1, e1 = I_quad(x, t, True)
    S1 = S_dec(x, t, True)
    I0q, e0 = I_quad(x, t, False)
    I0cf = (a).exp() * (lamd * a.ln()).exp() * upper_gamma_cf(-lamd, a) / xd ** 3     # x^{-3} e^a a^λ Γ(-λ,a) = x^{-3} e^a E_{λ+1}(a)
    ok_q &= abs(I0q - I0cf) < D(10) ** -50
    S0 = S_dec(x, t, False)
    g = gamma_neg_reflect(lamd, PI)
    pref = (a).exp() * (lamd * a.ln()).exp() / xd ** 3
    gap0 = pref * g
    gap1 = pref * g * ratio_formula(x)
    rc = abs((I0cf - S0) - gap0) / max(D(1), abs(gap0))
    re = abs((I1 - S1) - gap1) / max(D(1), abs(gap1))
    worst_c, worst_e = max(worst_c, rc), max(worst_e, re)
    ok_c &= rc < D(10) ** -45
    ok_e &= re < D(10) ** -40
    print('#   (x,t)=(%s,%s): I=%s  S=%s  I-S=%s' % (x, t, str(+I1)[:30], str(+S1)[:30], str(+(I1 - S1))[:30]))
rep('r2-I0-quad-vs-cf', ok_q, '[NUM] my DE quadrature of I0 == x^{-3} e^a a^lam Gamma(-lam,a) from the continued fraction (3 points, 1e-50)')
rep('r2-gap-const', ok_c, '[NUM] C3A-19 const part: I0 - sum t^m/P_m == x^{-3} Gamma(-lam) e^a a^lam at (3/5,-1/2),(2/5,-3/10),(3/10,-1/10); worst %.1E' % worst_c)
rep('r2-gap-full-closed', ok_e, '[NUM] C3A-19 full: I - S == x^{-3} e^a a^lam Gamma(-lam)[1+lam x^5 J] (reviewer closed form for K, no Prym series needed); worst %.1E' % worst_e)

# 作者表格里的具体数字（(3/5,-1/2)）
x, t = Fr(3, 5), Fr(-1, 2)
I1, _ = I_quad(x, t, True)
S1 = S_dec(x, t, True)
okn = str(I1).startswith('0.901813020695061353') and str(S1).startswith('-1057.810872563562058') and str(I1 - S1).startswith('1058.712685584257119')
rep('r2-author-table', okn, '[NUM] author table row (3/5,-1/2): I=0.90181302069506135393.., S=-1057.81087256356205855.., I-S=1058.71268558425711990.. reproduced')

# ============================================================ 3. 差值 ~1e-62 的点（21/100,-1/20）：用闭式 K 直接预测，无需 170 位
getcontext().prec = 110
PI = agm_pi()
x, t = Fr(21, 100), Fr(-1, 20)
xd, td = dec(x), dec(t)
lamd = (1 - xd) / xd ** 3
a = -td / xd ** 3
I1, e1 = I_quad(x, t, True)
S1 = S_dec(x, t, True)
g = gamma_neg_reflect(lamd, PI)
gap = (a).exp() * (lamd * a.ln()).exp() / xd ** 3 * g * ratio_formula(x)
rel = abs((I1 - S1 - gap) / gap)
print('#   sec3: prec=%d I=%s' % (getcontext().prec, str(I1)[:80]))
print('#   sec3: S=%s' % str(S1)[:80])
print('#   sec3: I-S=%s  gap(pred)=%s  quad_err=%s' % (str(I1 - S1), str(gap), e1))
# 注意：作者笔记表格的 3.8140177655303737080E-62 是把 Decimal 经 '%E' 转成 float 后打印的，只有前 ~17 位有效。
auth = D('3.8140177655303737080E-62')
rel_auth = abs((I1 - S1 - auth) / auth)
rep('r2-small-t', rel < D(10) ** -30 and rel_auth < D(10) ** -16,
    '[NUM] (21/100,-1/20): I - S = %s (110 digits; agrees with author 3.8140177655303737080E-62 only to rel %.1E, i.e. 17 digits: '
    'author\'s last 3 digits are a float-conversion artifact); reviewer closed-form prediction rel err %.1E'
    % (str(+(I1 - S1))[:26] + 'E-62', rel_auth, rel))

# 作者表格 (21/100,-1/2) 处的 I = 0.76544566082619491152...
getcontext().prec = 60
I2, _ = I_quad(Fr(21, 100), Fr(-1, 2), True)
rep('r2-author-I-21', str(I2).startswith('0.7654456608261949115'), '[NUM] author table: I(21/100,-1/2) = 0.76544566082619491152.. reproduced (%s)' % str(I2)[:24])

# ============================================================ 4. 定理 5.5（C3A-21）显式误差界的数值抽查
getcontext().prec = 50
PI = agm_pi()


def h_polys(K):
    def trim(p):
        p = list(p)
        while p and p[-1] == 0:
            p.pop()
        return p

    def padd(p, q):
        n = max(len(p), len(q))
        return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]

    def pmul(p, q):
        r = [0] * (len(p) + len(q) - 1)
        for i, a_ in enumerate(p):
            for j, b_ in enumerate(q):
                r[i + j] += a_ * b_
        return r

    def pder(p):
        return [i * p[i] for i in range(1, len(p))] or [0]
    hr = [[1], [1], [1, 1]]
    for k in range(3, K + 1):
        a_ = hr[k - 3]
        term = padd(pmul([1, -1], pder(a_)), [(k - 2) * c for c in a_])
        hr.append(trim(padd(hr[k - 1], pmul([0, 1, -1], term))))
    return hr


HP = h_polys(40)


def f_and_df(k, tau):
    h = HP[k]
    hv = sum(c * tau ** i for i, c in enumerate(h))
    dh = sum(i * c * tau ** (i - 1) for i, c in enumerate(h) if i >= 1)
    f = hv / (1 - tau) ** (k + 1)
    df = dh / (1 - tau) ** (k + 1) + (k + 1) * hv / (1 - tau) ** (k + 2)
    return f, df


ok = True
msgs = []
for (x, t, Kk) in [(Fr(3, 10), Fr(-1, 2), 6), (Fr(3, 10), Fr(-1, 2), 9), (Fr(1, 4), Fr(-1, 3), 12), (Fr(2, 5), Fr(-2), 7)]:
    I1, _ = I_quad(x, t, True)
    YK = sum(f_and_df(k, t)[0] * x ** k for k in range(Kk))
    err = abs(I1 - dec(YK))
    sup = D(0)
    xd_, td_ = dec(x), dec(t)
    for i in range(0, 3001):
        u = D(10) ** (D(i - 1500) / 300) if i > 0 else D(0)     # τ = t - u，u 从 1e-5 到 1e5（对数网格）+ u=0
        tau = td_ - u
        f1, _ = f_and_df(Kk - 1, tau)
        _, d3 = f_and_df(Kk - 3, tau)
        _, d2 = f_and_df(Kk - 2, tau)
        _, d1 = f_and_df(Kk - 1, tau)
        rho = f1 + tau * (d3 + xd_ * d2 + xd_ * xd_ * d1)
        sup = max(sup, abs(rho))
    bound = xd_ ** Kk / abs(td_) * sup
    ok &= err <= bound
    msgs.append('(%s,%s,K=%d): |I-Y_K|=%.3E <= bound %.3E' % (x, t, Kk, err, bound))
rep('r2-thm55-bound', ok, '[NUM] C3A-21 explicit error bound |I - sum_{k<K} f_k x^k| <= (x^K/|t|) sup_{tau<=t}|rho_K| (sup on a log grid): ' + '; '.join(msgs))

npass = sum(RES)
print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY r2 pass=%d fail=%d' % (npass, len(RES) - npass))
sys.exit(0 if npass == len(RES) else 1)
