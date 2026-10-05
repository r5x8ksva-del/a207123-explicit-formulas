# -*- coding: utf-8 -*-
"""审计 a1-formulas：报告 C-3 部分（T3.1–T3.6）中能做有限项展开核对的恒等式。

做法：
  * Q(x)[[t]] 中的恒等式：取若干个有理数 x（避开 b_i 的根），两边都按 t 展开到 t^TT，逐系数精确比较
    （每个 t^m 系数是 x 的有理函数，取 >次数 个点即可判定；这里是抽查，不是证明）。
  * T3.2 / T3.5(3) 的形式 Laplace 表示：在 Q[[x,t]][[s]] 中真正展开（x 截断 KX、t 截断 MT），逐系数取 N!·[s^N] 求和。
  * T3.5(1)(2)、T3.6：直接用定义 DP 得到的 U、N、h 表做二元级数比较。
"""
import time
from fractions import Fraction
from math import comb, factorial
from common import *  # noqa

t0 = time.time()
TT = 10
XS = [Fraction(2, 7), Fraction(3, 10), Fraction(-2, 5), Fraction(5, 3), Fraction(7, 11)]

# ---------- t 级数工具（固定有理 x） ----------
def s_add(a, b):
    return [a[i] + b[i] for i in range(len(a))]
def s_scale(a, c):
    return [c * v for v in a]
def s_mul(a, b):
    n = len(a)
    r = [Fraction(0)] * n
    for i in range(n):
        if a[i] == 0:
            continue
        for j in range(n - i):
            r[i + j] += a[i] * b[j]
    return r
def s_exp(a):
    """exp(a)，a[0]=0。"""
    n = len(a)
    e = [Fraction(0)] * n
    e[0] = Fraction(1)
    for k in range(1, n):
        e[k] = sum(j * a[j] * e[k - j] for j in range(1, k + 1)) / k
    return e
def s_inv(a):
    n = len(a)
    r = [Fraction(0)] * n
    r[0] = 1 / Fraction(a[0])
    for k in range(1, n):
        r[k] = -sum(a[j] * r[k - j] for j in range(1, k + 1)) * r[0]
    return r
def s_pow_one_minus_t(e, n):
    """(1-t)^{-e}，e 为非负整数。"""
    return [Fraction(comb(e + r - 1, r)) if e > 0 else Fraction(1 if r == 0 else 0) for r in range(n)]
def bval(i, x):
    return 1 - x - i * x ** 3
def poch(a, n):
    r = Fraction(1)
    for i in range(n):
        r *= (a + i)
    return r
def GW(m, x):
    """G_m(x)=W_m/P_m 在有理 x 处的值；G_{-1}=1。"""
    if m == -1:
        return Fraction(1)
    return Fraction(peval(W_poly(m), x)) / Fraction(peval(P_poly(m), x))
def Pval(m, x):
    return Fraction(peval(P_poly(m), x)) if m >= 0 else Fraction(1)

n = TT + 1
ok_poch = True
ok_31 = ok_kum = ok_gam = True
ok_331 = ok_kumF = ok_hum = ok_Y = True
for x in XS:
    lam = (1 - x) / x ** 3
    # 关键恒等式 (j+1-λ)_n = (-1)^n x^{-3n} prod_{i=j+1}^{j+n} b_i
    for j in range(-1, 6):
        for nn in range(0, 8):
            lhs = poch(j + 1 - lam, nn)
            rhs = Fraction((-1) ** nn) * x ** (-3 * nn)
            for i in range(j + 1, j + nn + 1):
                rhs *= bval(i, x)
            if lhs != rhs:
                ok_poch = False
    a_ser = [Fraction(0), -1 / x ** 3] + [Fraction(0)] * (n - 2)          # a = -t/x^3
    ea = s_exp(a_ser)
    # T3.1：sum_m t^m/P_m = 1F1(1;1-λ;a)/(1-x)
    target = [1 / Pval(m, x) for m in range(n)]
    f11 = [poch(1, k) * (-1 / x ** 3) ** k / (poch(1 - lam, k) * factorial(k)) for k in range(n)]
    if s_scale(f11, 1 / (1 - x)) != target:
        ok_31 = False
    # Kummer：e^a 1F1(-λ;1-λ;-a)/(1-x)
    f11b = [poch(-lam, k) * (1 / x ** 3) ** k / (poch(1 - lam, k) * factorial(k)) for k in range(n)]
    if s_scale(s_mul(ea, f11b), 1 / (1 - x)) != target:
        ok_kum = False
    # 下不完全 Gamma：-x^{-3} e^a sum_n (-a)^n/(n!(n-λ))
    g = [(1 / x ** 3) ** k / (factorial(k) * (k - lam)) for k in range(n)]
    if s_scale(s_mul(ea, g), -1 / x ** 3) != target:
        ok_gam = False
    # T3.3(1)：F = sum_j c_j t^j/b_j 1F1(1;j+1-λ;a)
    targetF = [GW(m, x) for m in range(n)]
    tot = [Fraction(0)] * n
    for j in range(0, n):
        cj = Fraction(1) if j == 0 else j * x ** 2
        f = [poch(1, k) * (-1 / x ** 3) ** k / (poch(j + 1 - lam, k) * factorial(k)) for k in range(n)]
        term = [Fraction(0)] * n
        for k in range(n - j):
            term[k + j] = cj * f[k] / bval(j, x)
        tot = s_add(tot, term)
    if tot != targetF:
        ok_331 = False
    # Kummer 单级数：F = x^{-3} e^a sum_n φ_n a^n/(λ-n)，φ(τ)=e^{-τ}(1-x^5τ/(1+x^3τ)^2)
    emt = [Fraction((-1) ** k, factorial(k)) for k in range(n)]
    gpoly = [Fraction(1)] + [Fraction(r * (-1) ** r) * x ** (3 * r + 2) for r in range(1, n)]
    phi = s_mul(emt, gpoly)
    sm = [phi[k] * (-1 / x ** 3) ** k / (lam - k) for k in range(n)]
    if s_scale(s_mul(ea, sm), 1 / x ** 3) != targetF:
        ok_kumF = False
    # Humbert：F=(1/(1-x))[1F1(1;1-λ;a)+x^2((1-t)^{-2}Φ1(1,2;1-λ;X,a)-(1-t)^{-1}Φ1(1,1;1-λ;X,a))]，X=-t/(1-t)
    def Phi1(alpha, beta, gam, Xser, Yser):
        out = [Fraction(0)] * n
        Xp = [Fraction(1)] + [Fraction(0)] * (n - 1)
        for mm in range(0, n):
            Yp = [Fraction(1)] + [Fraction(0)] * (n - 1)
            for nn_ in range(0, n - mm):
                c = poch(alpha, mm + nn_) * poch(beta, mm) / (poch(gam, mm + nn_) * factorial(mm) * factorial(nn_))
                out = s_add(out, s_scale(s_mul(Xp, Yp), c))
                Yp = s_mul(Yp, Yser)
            Xp = s_mul(Xp, Xser)
        return out
    Xser = s_mul([Fraction(0), Fraction(-1)] + [Fraction(0)] * (n - 2), s_pow_one_minus_t(1, n))
    P2 = Phi1(1, 2, 1 - lam, Xser, a_ser)
    P1 = Phi1(1, 1, 1 - lam, Xser, a_ser)
    inner = s_add(s_mul(s_pow_one_minus_t(2, n), P2), s_scale(s_mul(s_pow_one_minus_t(1, n), P1), -1))
    hum = s_scale(s_add(f11, s_scale(inner, x ** 2)), 1 / (1 - x))
    if hum != targetF:
        ok_hum = False
    # Y_β：L_A[Y_β]=(1-t)^{-β}（A=1-x），Y_β=(1-t)^{-β} sum_N t^N/(A prod_{i<=N} b_i) sum_{m<=N} C(N,m)(β)_m (x^3/(1-t))^m
    A_ = 1 - x
    for beta in (1, 2, 3):
        Ys = [Fraction(0)] * n
        for N in range(0, n):
            pr = A_
            for i in range(1, N + 1):
                pr *= bval(i, x)
            for mm in range(0, N + 1):
                c = Fraction(comb(N, mm)) * poch(beta, mm) * x ** (3 * mm) / pr
                term = [Fraction(0)] * n
                term[N] = c
                term = s_mul(term, s_pow_one_minus_t(mm + beta, n))
                Ys = s_add(Ys, term)
        # (A - t)Y - x^3 t Y'
        lhs = [A_ * Ys[k] - (Ys[k - 1] if k >= 1 else 0) - x ** 3 * k * Ys[k] for k in range(n)]
        if lhs != s_pow_one_minus_t(beta, n):
            ok_Y = False
report(ok_poch, 'C3.poch', '(j+1-λ)_n=(-1)^n x^{-3n} prod_{i=j+1}^{j+n} b_i（5 个有理 x，-1<=j<=5，n<=7）')
report(ok_31, 'T3.1.1F1', 'sum_m t^m/P_m=1F1(1;1-λ;-t/x^3)/(1-x)，t^0..t^10 逐系数（5 个有理 x）')
report(ok_kum, 'T3.1.kummer', 'Kummer 形式 e^a 1F1(-λ;1-λ;-a)/(1-x) 同上')
report(ok_gam, 'T3.1.gamma', '不完全 Gamma 形式 -x^{-3}e^a sum_n(-a)^n/(n!(n-λ)) 同上')
report(ok_331, 'T3.3.1-sum', 'F=sum_j c_j(t^j/b_j)1F1(1;j+1-λ;-t/x^3)，c_0=1,c_j=j x^2：t^m 系数 = W_m/P_m（m<=10，5 个 x）')
report(ok_kumF, 'T3.3.1-kummer', 'F=x^{-3}e^a sum_n φ_n a^n/(λ-n)，φ=e^{-τ}(1-x^5τ/(1+x^3τ)^2)：t^m 系数 = W_m/P_m')
report(ok_hum, 'T3.3.2-humbert', 'Humbert Φ_1 有限闭式：t^m 系数 = W_m/P_m（m<=10，5 个 x）')
report(ok_Y, 'T3.3.2-Ybeta', 'Y_β 满足 (A-t)Y-x^3tY_t=(1-t)^{-β}（A=1-x，β=1,2,3，到 t^10）')

# ---------- T3.2 / T3.5(3)：形式 Laplace 表示的真正展开 ----------
KX, MT = 15, 6
NS = KX // 3 + MT + 1
UT = own_U_table(KX, MT + 1)

def z2():
    return [[Fraction(0)] * (MT + 1) for _ in range(KX + 1)]
def m2(a, b):
    r = z2()
    for i in range(KX + 1):
        for j in range(MT + 1):
            v = a[i][j]
            if v == 0:
                continue
            for i2 in range(KX + 1 - i):
                bi = b[i2]
                for j2 in range(MT + 1 - j):
                    if bi[j2]:
                        r[i + i2][j + j2] += v * bi[j2]
    return r
def a2(a, b, c=1):
    return [[a[i][j] + c * b[i][j] for j in range(MT + 1)] for i in range(KX + 1)]
def xser_to2(xs, tpow=0, coef=1):
    r = z2()
    for i in range(min(len(xs), KX + 1)):
        r[i][tpow] += coef * xs[i]
    return r

def laplace_solve(Aser, gamma_terms):
    """Y = A^{-1} L_s[ exp((t/x^3)(e^{vs}-1)) * Σ_r g_r(x) t^r e^{r v s} ]，v=x^3/A。
    Aser: x 级数；gamma_terms: dict r -> x 级数 g_r（γ(x,t)=Σ_r g_r t^r）。返回二维数组 [x^i t^j]。"""
    Ainv = sinv(Aser, KX + 4)
    v = [Fraction(0)] * 3 + Ainv[:KX + 1]                       # v = x^3/A，保留到 x^{KX+3}
    vpow = [[Fraction(1)] + [Fraction(0)] * (KX + 3)]
    for _ in range(NS + 1):
        vpow.append(smul(vpow[-1], v, KX + 4))
    # A_N = t * (v^N/x^3)/N!，v^N/x^3 = x^{3N-3}/A^N
    Aterm = [None]
    for N in range(1, NS + 1):
        vn_over_x3 = vpow[N][3:3 + KX + 1]
        Aterm.append(xser_to2([c / factorial(N) for c in vn_over_x3], 1))
    E = [None] * (NS + 1)
    E[0] = z2()
    E[0][0][0] = Fraction(1)
    for N in range(1, NS + 1):
        acc = z2()
        for j in range(1, N + 1):
            acc = a2(acc, m2(Aterm[j], E[N - j]), j)
        E[N] = [[c / N for c in row] for row in acc]
    B = []
    for N in range(0, NS + 1):
        b = z2()
        for r, g in gamma_terms.items():
            if r > MT:
                continue
            coefx = smul(g, vpow[N], KX + 1)
            for i in range(KX + 1):
                b[i][r] += Fraction(r ** N, factorial(N)) * coefx[i] if (r > 0 or N == 0) else 0
        B.append(b)
    Psi = []
    for N in range(0, NS + 1):
        acc = z2()
        for a_ in range(0, N + 1):
            acc = a2(acc, m2(E[a_], B[N - a_]))
        Psi.append(acc)
    tot = z2()
    for N in range(0, NS + 1):
        tot = a2(tot, Psi[N], factorial(N))
    Y = m2(xser_to2(Ainv[:KX + 1]), tot)
    return Y, Psi

# 特例：A=1-x，γ=1+x^2 t/(1-t)^2 = 1 + Σ_{r>=1} r x^2 t^r
g1 = {0: [Fraction(1)]}
for r in range(1, MT + 1):
    g1[r] = [Fraction(0), Fraction(0), Fraction(r)]
Y, Psi = laplace_solve([Fraction(1), Fraction(-1)], g1)
ok = all(Y[k][m] == UT[k][m] for k in range(KX + 1) for m in range(MT + 1))
report(ok, 'T3.2.laplace-F', 'F=(1/(1-x))L_s[exp((t/x^3)(e^{us}-1))(1+x^2te^{us}/(1-te^{us})^2)] 在 Q[[x,t]][[s]] 中展开，k<=15, m<=6 与定义 DP 一致')
# 赋值界：[s^N t^m]Ψ 的 x-赋值 >= 3N-3m
ok = True
for N in range(NS + 1):
    for m in range(MT + 1):
        lo = 3 * N - 3 * m
        for i in range(0, min(lo, KX + 1)):
            if Psi[N][i][m] != 0:
                ok = False
report(ok, 'T3.2.valuation', '[s^N t^m]Ψ 的 x-赋值 >= 3N-3m（N<=%d, m<=6, x^15 截断内）' % NS)
# T3.5(3)：A=1-x+x^3，γ=A+x^2t^2/(1-t)^2 → 1+tF
g2 = {0: [Fraction(1), Fraction(-1), Fraction(0), Fraction(1)]}
for r in range(2, MT + 1):
    g2[r] = [Fraction(0), Fraction(0), Fraction(r - 1)]
Y2, _ = laplace_solve([Fraction(1), Fraction(-1), Fraction(0), Fraction(1)], g2)
ok = all(Y2[k][m] == ((1 if (k == 0 and m == 0) else 0) + (UT[k][m - 1] if m >= 1 else 0)) for k in range(KX + 1) for m in range(MT + 1))
report(ok, 'T3.5.3-laplace', '1+tF=A^{-1}L_s[exp((t/x^3)(e^{vs}-1))(A+x^2t^2e^{2vs}/(1-te^{vs})^2)]，A=1-x+x^3：k<=15, m<=6 展开一致')

# ---------- T3.5 (1)(2)：代换关系与 PDE ----------
KQ = 30
TU = core.U_fast_table(KQ, KQ + 1)
NT = N_table_from_U(TU, KQ)
def Nv(k, q):
    if k < 0 or q < 0 or k > KQ or q > KQ:
        return 0
    return NT[k][q]
# 𝒩(x,y)=Σ N(k,q)x^k y^q；检查 1+tF = 𝒩(x,t/(1-t))/(1-t)：系数 [x^k t^m]
ok = True
TM = 16
for k in range(0, KQ + 1):
    # 𝒩_k(t/(1-t))/(1-t) = Σ_q N(k,q) t^q (1-t)^{-q-1}
    ser = [0] * TM
    for q in range(0, k + 1):
        for r in range(0, TM - q):
            ser[q + r] += NT[k][q] * comb(q + r, r)
    for m in range(TM):
        want = (1 if (k == 0 and m == 0) else 0) + (TU[k][m - 1] if m >= 1 else 0)
        if ser[m] != want:
            ok = False
report(ok, 'T3.5.1-subst', '1+tF(x,t)=𝒩(x,t/(1-t))/(1-t) 逐系数, k<=30, m<=15')
# 等价形式 𝒩=1/(1+y)+y F(x,y/(1+y))/(1+y)^2：系数 [x^k y^q]
ok = True
for k in range(0, KQ + 1):
    ser = [0] * (KQ + 1)
    if k == 0:
        for q in range(KQ + 1):
            ser[q] += (-1) ** q
    # y F(x, y/(1+y))/(1+y)^2 = Σ_m U_k(m) y^{m+1} (1+y)^{-m-2}
    for m in range(0, KQ):
        for r in range(0, KQ - m):
            ser[m + 1 + r] += TU[k][m] * (-1) ** r * comb(m + 1 + r, r)
    if any(ser[q] != Nv(k, q) for q in range(KQ + 1)):
        ok = False
report(ok, 'T3.5.1-subst2', '𝒩(x,y)=1/(1+y)+y F(x,y/(1+y))/(1+y)^2 逐系数, k,q<=30')
# PDE：(1-x(1+y)+x^3(1-y^2))𝒩 - x^3 y(1+y)^2 ∂_y𝒩 = 1-x+x^3+x^2y^2
ok = True
for k in range(0, KQ + 1):
    for q in range(0, KQ + 1):
        lhs = Nv(k, q) - Nv(k - 1, q) - Nv(k - 1, q - 1) + Nv(k - 3, q) - Nv(k - 3, q - 2)
        # - x^3 y (1+2y+y^2) ∂_y：[x^k y^q] = -( (q)N(k-3,q) + 2(q-1)N(k-3,q-1) + (q-2)N(k-3,q-2) )
        lhs -= q * Nv(k - 3, q) + 2 * (q - 1) * Nv(k - 3, q - 1) + (q - 2) * Nv(k - 3, q - 2)
        rhs = {(0, 0): 1, (1, 0): -1, (3, 0): 1, (2, 2): 1}.get((k, q), 0)
        if lhs != rhs:
            ok = False
report(ok, 'T3.5.2-pde', '𝒩 的 PDE 逐系数, k,q<=30（右端 4 个单项 = 4 个边界修正）')
# [y^q]𝒩 = Σ_i (-1)^{q-i}C(q,i)G_{i-1}
ok = True
for q in range(0, 12):
    ser = [0] * (KQ + 1)
    for i in range(0, q + 1):
        if i == 0:
            g = [1] + [0] * KQ
        else:
            g = series_of_rational(W_poly(i - 1), P_poly(i - 1), KQ + 1)
        for k in range(KQ + 1):
            ser[k] += (-1) ** (q - i) * comb(q, i) * g[k]
    if any(ser[k] != Nv(k, q) for k in range(KQ + 1)):
        ok = False
report(ok, 'T3.5.3-yq', '[y^q]𝒩=sum_i(-1)^{q-i}C(q,i)G_{i-1}, q<=11, k<=30')
# 𝒩 的 Humbert 闭式（有理 x，y 级数）
ok = True
for x in XS:
    lam = (1 - x) / x ** 3
    A_ = 1 - x + x ** 3
    yser = [Fraction(0), Fraction(1)] + [Fraction(0)] * (n - 2)
    inv1py = [Fraction((-1) ** r) for r in range(n)]                       # 1/(1+y)
    yhat = s_scale(s_mul(yser, inv1py), -1 / x ** 3)
    negy = s_scale(yser, -1)
    def F11(b, z):
        out = [Fraction(0)] * n
        zp = [Fraction(1)] + [Fraction(0)] * (n - 1)
        for kk in range(n):
            out = s_add(out, s_scale(zp, poch(1, kk) / (poch(b, kk) * factorial(kk))))
            zp = s_mul(zp, z)
        return out
    def Phi1(alpha, beta, gam, Xs, Ys):
        out = [Fraction(0)] * n
        Xp = [Fraction(1)] + [Fraction(0)] * (n - 1)
        for mm in range(0, n):
            Yp = [Fraction(1)] + [Fraction(0)] * (n - 1)
            for nn_ in range(0, n - mm):
                c = poch(alpha, mm + nn_) * poch(beta, mm) / (poch(gam, mm + nn_) * factorial(mm) * factorial(nn_))
                out = s_add(out, s_scale(s_mul(Xp, Yp), c))
                Yp = s_mul(Yp, Ys)
            Xp = s_mul(Xp, Xs)
        return out
    onepy = [Fraction(1), Fraction(1)] + [Fraction(0)] * (n - 2)
    t1 = s_scale(F11(-lam, yhat), A_ + x ** 2)
    t2 = s_scale(s_mul(onepy, Phi1(1, 1, -lam, negy, yhat)), -2 * x ** 2)
    t3 = s_scale(s_mul(s_mul(onepy, onepy), Phi1(1, 2, -lam, negy, yhat)), x ** 2)
    tot = s_scale(s_mul(s_add(s_add(t1, t2), t3), inv1py), 1 / A_)
    want = []
    for q in range(n):
        want.append(sum(Fraction((-1) ** (q - i) * comb(q, i)) * GW(i - 1, x) for i in range(q + 1)))
    if tot != want:
        ok = False
report(ok, 'T3.5.3-humbert', '𝒩 的 Humbert 闭式：y^q 系数 = sum_i(-1)^{q-i}C(q,i)G_{i-1}(x)（q<=10，5 个有理 x）')

# ---------- T3.6 ----------
def hpoly(k):
    return trim([sum((-1) ** (i - j) * comb(k + 1, i - j) * TU[k][j] for j in range(0, i + 1)) for i in range(0, k + 1)])
HP = {k: hpoly(k) for k in range(0, KQ + 1)}
ok1 = True
ok2 = True
for k in range(0, KQ + 1):
    # (1-t)F(z(1-t),t) 的 z^k 系数 = (1-t)^{k+1} Σ_m U_k(m) t^m（截断到 t^KQ）
    f = [TU[k][m] for m in range(KQ + 1)]
    pr = ppow([1, -1], k + 1)
    ser = smul(pr, f, KQ + 1)
    hk = HP[k] + [0] * (KQ + 1 - len(HP[k]))
    if any(ser[i] != hk[i] for i in range(KQ + 1)):
        ok1 = False
    # 1+(𝒩(z(1-t),t/(1-t))-1)/t 的 z^k 系数
    if k == 0:
        poly = [1]
    else:
        poly = []
        for q in range(1, k + 1):
            poly = padd(poly, pscale(pmul(pshift([1], q - 1), ppow([1, -1], k - q)), NT[k][q]))
    if trim(psub(poly, HP[k])):
        ok2 = False
report(ok1 and ok2, 'T3.6.subst', 'H(z,t)=Σh_k z^k=(1-t)F(z(1-t),t)=1+(𝒩(z(1-t),t/(1-t))-1)/t（逐 z^k，k<=30）')
# PDE：(1-z-z^3t(1-t))H - z^4 t(1-t)∂_zH - z^3 t(1-t)^2 ∂_tH = 1+z^2 t
ok = True
def hk_(k):
    return HP[k] if 0 <= k <= KQ else []
for k in range(0, KQ + 1):
    acc = hk_(k)
    acc = psub(acc, hk_(k - 1))
    acc = psub(acc, pmul([0, 1, -1], hk_(k - 3)))
    acc = psub(acc, pscale(pmul([0, 1, -1], hk_(k - 3)), k - 3))           # z^4 t(1-t)∂_z：[z^k] = (k-3) t(1-t) h_{k-3}
    acc = psub(acc, pmul([0, 1, -2, 1], pderiv(hk_(k - 3))))
    rhs = [1] if k == 0 else ([0, 1] if k == 2 else [])
    if trim(psub(acc, rhs)):
        ok = False
report(ok, 'T3.6.pde', 'H 的 PDE 逐 z^k 系数成立, k<=30')

summary('audit_c3')
print('elapsed %.1fs' % (time.time() - t0))
