# -*- coding: utf-8 -*-
"""s15-b13 / A：(0.1) f_k(t)=Σ_{3n+j=k} n!·H_{n,j} 的独立精确核对（不导入项目代码）。

方法（与作者的 FFT/Newton 和 s9-b7 的展开都不同）：
  Lagrange–Bürmann：H(w,x)dw=g_x(-τe^σ)dσ，所以 [w^n]H=[σ^n] g·(σ/ψ_x(σ))^{n+1}。
  令 λ=1/(1+τ)=1/(1-t)，E(σ)=(e^σ-1-σ)/σ，Γ(σ)=τe^σ/(1+τe^σ)^2，则
    σ/ψ_x(σ)=λ/(1-λx-(λ-1)E)，  g=1-x²Γ，  Γ=Y-Y²，Y=λ/(1+(1-λ)(e^σ-1))，
    [σ^n]E^c = c!·S≥2(n+c,c)/(n+c)!（S≥2：每块至少 2 个元素的 Stirling 数），
    [σ^d]Y = λ Σ_i (λ-1)^i i! S2(d,i)/d!。
  于是 n!·A(n,m)=λ^{n+1+m}/m!·Σ_c S≥2(n+c,c)·(n+m+c)!/(n+c)!·(λ-1)^c，
       n!·B(n,m)=λ^{n+1+m}/m!·Σ_c (n+m+c)!/c!·(λ-1)^c·[σ^n](E^cΓ)，
       H_{n,j}=A(n,j)-B(n,j-2)，a_k:=Σ_{3n+j=k} n!H_{n,j} 是 λ 的多项式（有理系数）。
  另一边 f_k(t)=Σ_q N(k,q)t^{q-1}/(1-t)^{q+1}=λ²Σ_q N(k,q)(λ-1)^{q-1}（k>=1），f_0=λ，也是 λ 的多项式。
  所以对每个固定的 k，(0.1) 是 Q[λ] 中的多项式恒等式；逐个 k 精确比较两边，就对一切 τ≠-1 同时证明了这个 k。

检查：
  a-truth    原始定义：枚举 = 朴素 DP = 压缩 DP（小范围）；压缩 DP = 引理 1 的三项递推（k<=30,m<=10）；
             (C3) 的 N 递推 = 由定义容斥得到的 N（k<=14）；= 由引理 1 表容斥得到的 N（k<=60）
  a-fk       f_k(λ) 两条路线一致：λ²ΣN(k,q)(λ-1)^{q-1} 与 Σ_i h_{k,i}(λ-1)^iλ^{k+1-i}（h_k 由 U 表乘 (1-t)^{k+1} 得到），
             并核对 deg h_k<=⌊2k/3⌋（k<=K_SYM）
  a-sym      (0.1) 作为 Q[λ] 中的恒等式：k<=K_SYM 全部精确成立（与 T3.4(4) 无关的独立证明，逐个 k）
  a-pde      Lagrange 一侧的 a_k 满足 a_k=λa_{k-1}+λ²(λ-1)a'_{k-3}（k>=3），a_0=λ，a_1=λ²，a_2=2λ³-λ²
             （即 (1-t-x)F-tx³F_t=1+tx²/(1-t)²，引理 1 的母函数形式）
  a-rev-ser  闭式的单个系数 H_{n,j} 与直接的级数反演（精确有理）逐项相等（τ=1、1/3，n<=6，j<=9）
  a-points   具体的 t：t=-1、-1/3、-5 到 k<=K_PT，另 5 个 t 到 k<=K_PT2，精确有理相等
  a-rev      反向检查：去掉 g 的 x² 项、改一个 S≥2、τ 取错、指数 n+1 改成 n+2，都应在小 k 处不等
用法：py -3.14 code/review/s15-b13/a_lagrange_exact.py [K_SYM] [K_PT]
"""
import sys
import time
from fractions import Fraction as Fr
from math import comb

from s15_common import (Reporter, setup_stdout, U_brute, U_dp_naive, U_dp_fast, U_table_lemma1,
                        N_from_U, N_rows, padd, pscale, pmul, pshift, ptrim, pderiv,
                        lam_minus_1_powers, stirling2_table, stirling2_ge2_table, fact)

setup_stdout()
K_SYM = int(sys.argv[1]) if len(sys.argv) > 1 else 120
K_PT = int(sys.argv[2]) if len(sys.argv) > 2 else 300
K_PT2 = 120

PROMPT_TABLE = {   # 原始任务说明 §2 的校验数据（只作额外对照）
    1: [1, 2, 3, 4, 5, 6, 7], 2: [1, 4, 9, 16, 25, 36, 49], 3: [1, 6, 17, 36, 65, 106, 161],
    4: [1, 9, 32, 80, 165, 301, 504], 5: [1, 14, 64, 192, 457, 938, 1736],
    6: [1, 21, 119, 419, 1136, 2604, 5306], 7: [1, 31, 214, 873, 2669, 6778, 15108],
    8: [1, 46, 388, 1837, 6334, 17802, 43326], 9: [1, 68, 694, 3788, 14666, 45488, 120650],
    10: [1, 100, 1222, 7629, 32971, 112349, 323647]}


# ------------------------------------------------------------------ 符号（λ 的整系数多项式，乘 k!）
class LagrangeSym:
    """k!·a_k(λ) 的整系数多项式。可选的“改坏”开关用于反向检查。"""

    def __init__(self, K, drop_g=False, bump_s2g=None):
        self.K = K
        N = K // 3 + 2
        self.N = N
        self.drop_g = drop_g
        self.S2 = stirling2_table(N + 2)
        self.S2g = stirling2_ge2_table(2 * N + 4)
        if bump_s2g is not None:
            a, b = bump_s2g
            self.S2g[a][b] += 1
        self.L = lam_minus_1_powers(2 * N + 4)
        # y_d = d!·Y_d = λ Σ_i (λ-1)^i i! S2(d,i)
        y = []
        for d in range(N + 1):
            acc = []
            for i in range(d + 1):
                if self.S2[d][i]:
                    acc = padd(acc, pscale(self.L[i], fact(i) * self.S2[d][i]))
            y.append(pshift(acc, 1))
        # γ_d = d!·Γ_d = y_d - Σ_e C(d,e) y_e y_{d-e}
        gam = []
        for d in range(N + 1):
            acc = list(y[d])
            for e in range(d + 1):
                acc = padd(acc, pscale(pmul(y[e], y[d - e]), -comb(d, e)))
            gam.append(acc)
        self.gam = gam
        # RQ[c][n] = (λ-1)^c · iq[c][n]，iq[c][n]=(n+c)!·[σ^n](E^cΓ)=Σ_d c!·S≥2(n-d+c,c)·C(n+c,d)·γ_d
        self.RQ = {}
        for n in range(N + 1):
            for c in range(n + 1):
                acc = []
                for d in range(0, n - c + 1):
                    s = self.S2g[n - d + c][c]
                    if s:
                        acc = padd(acc, pscale(gam[d], fact(c) * s * comb(n + c, d)))
                self.RQ[(c, n)] = pmul(self.L[c], acc)

    def kfact_nA(self, k, n, m):
        """k!·n!·A(n,m)（整系数多项式）与 λ 的移位指数 n+1+m。"""
        e = n + 1 + m
        acc = []
        for c in range(n + 1):
            s = self.S2g[n + c][c]
            if s:
                acc = padd(acc, pscale(self.L[c], s * (fact(n + m + c) // fact(n + c))))
        return pscale(acc, fact(k) // fact(m)), e

    def kfact_nB(self, k, n, m):
        """k!·n!·B(n,m)（整系数多项式）。"""
        e = n + 1 + m
        acc = []
        for c in range(n + 1):
            w = (fact(n + m + c) // fact(n + c)) * (fact(n) // fact(c))
            acc = padd(acc, pscale(self.RQ[(c, n)], w))
        mult = fact(k) // (fact(m) * fact(n))
        assert fact(k) % (fact(m) * fact(n)) == 0
        return pscale(acc, mult), e

    def kfact_a(self, k):
        tot = []
        for n in range(k // 3 + 1):
            m = k - 3 * n
            pa, e = self.kfact_nA(k, n, m)
            tot = padd(tot, pshift(pa, e))
            if m >= 2 and not self.drop_g:
                pb, e2 = self.kfact_nB(k, n, m - 2)
                tot = padd(tot, pscale(pshift(pb, e2), -1))
        return ptrim(tot)


def kfact_f_from_N(k, row):
    """k!·f_k(λ) = k!·λ²Σ_q N(k,q)(λ-1)^{q-1}（k>=1），k=0 时 λ。"""
    if k == 0:
        return [0, 1]
    acc = []
    L = [1]                       # (λ-1)^{q-1}
    for q in range(1, len(row)):
        if q >= 2:
            L = pmul(L, [-1, 1])
        if row[q]:
            acc = padd(acc, pscale(L, row[q]))
    return ptrim(pscale(pshift(acc, 2), fact(k)))


def h_from_U(k, Ucol):
    """h_k(t)=(1-t)^{k+1}Σ_m U_k(m)t^m mod t^{k+1}；Ucol[m]=U_k(m)，m=0..k。返回系数列表（长度 k+1）。"""
    binom = [(-1) ** i * comb(k + 1, i) for i in range(k + 2)]
    h = [0] * (k + 1)
    for i in range(k + 1):
        s = 0
        for m in range(i + 1):
            s += Ucol[m] * binom[i - m]
        h[i] = s
    return h


def kfact_f_from_h(k, h):
    acc = []
    L = lam_minus_1_powers(len(h))
    for i, c in enumerate(h):
        if c:
            acc = padd(acc, pscale(pshift(L[i], k + 1 - i), c))
    return ptrim(pscale(acc, fact(k)))


# ------------------------------------------------------------------ 具体 λ=p/q（整数内积，最后才做分数）
class LagrangePoint:
    def __init__(self, K, p, q, drop_g=False):
        self.K, self.p, self.q = K, p, q
        N = K // 3 + 2
        self.N = N
        self.drop_g = drop_g
        S2 = stirling2_table(N + 2)
        self.S2g = stirling2_ge2_table(2 * N + 4)
        r = p - q
        yint = [sum((r ** i) * (q ** (d - i)) * fact(i) * S2[d][i] for i in range(d + 1)) for d in range(N + 1)]
        # Γ_d = G_d/(q^{d+2} d!)
        G = [p * q * yint[d] - p * p * sum(comb(d, e) * yint[e] * yint[d - e] for e in range(d + 1))
             for d in range(N + 1)]
        # Q[c][n] = IQ[c][n]/(q^{n+2}(n+c)!)
        self.IQ = {}
        for n in range(N + 1):
            for c in range(n + 1):
                s = 0
                for d in range(n - c + 1):
                    sg = self.S2g[n - d + c][c]
                    if sg:
                        s += fact(c) * sg * comb(n + c, d) * G[d] * q ** (n - d)
                self.IQ[(c, n)] = s

    def a(self, k):
        p, q = self.p, self.q
        r = p - q
        tot = Fr(0)
        for n in range(k // 3 + 1):
            m = k - 3 * n
            IA = 0
            for c in range(n + 1):
                sg = self.S2g[n + c][c]
                if sg:
                    IA += sg * (fact(n + m + c) // fact(n + c)) * r ** c * q ** (n - c)
            tot += Fr(p ** (n + 1 + m) * IA, q ** (2 * n + 1 + m) * fact(m))
            if m >= 2 and not self.drop_g:
                mm = m - 2
                IB = 0
                for c in range(n + 1):
                    IB += (fact(n + mm + c) // fact(n + c)) * (fact(n) // fact(c)) * r ** c * q ** (n - c) * self.IQ[(c, n)]
                tot -= Fr(p ** (n + 1 + mm) * IB, q ** (3 * n + 3 + mm) * fact(mm) * fact(n))
        return tot


def f_point(k, row, p, q):
    if k == 0:
        return Fr(p, q)
    r = p - q
    s = sum(row[j] * r ** (j - 1) * q ** (k - j) for j in range(1, len(row)) if row[j])
    return Fr(p * p * s, q ** (k + 1))


# ------------------------------------------------------------------ 直接级数反演（小范围，精确）
def series_reversion_H(tau, NW, NX):
    """直接算 H(w,x)=g(-τe^{σ(w)})σ'(w) 的系数 H[n][j]（n<=NW，j<=NX），精确有理。
    σ(w,x) 由 ψ_x(σ)=w 迭代反演；二元截断级数用 dict。"""
    tau = Fr(tau)

    def mul(a, b):
        out = {}
        for (i1, j1), v1 in a.items():
            for (i2, j2), v2 in b.items():
                i, j = i1 + i2, j1 + j2
                if i <= NW + 1 and j <= NX:
                    out[(i, j)] = out.get((i, j), 0) + v1 * v2
        return {k: v for k, v in out.items() if v != 0}

    def add(a, b, cb=1):
        out = dict(a)
        for k, v in b.items():
            out[k] = out.get(k, 0) + cb * v
        return {k: v for k, v in out.items() if v != 0}

    def exp_noconst(s):   # e^s - 1，s 无常数项（关于 w）
        out = {}
        term = {(0, 0): Fr(1)}
        for m in range(1, NW + 2):
            term = mul(term, s)
            term = {k: v / m for k, v in term.items()}
            out = add(out, term)
        return out
    lam = 1 / (1 + tau)
    inv = {(0, j): lam ** (j + 1) for j in range(NX + 1)}      # 1/(1-x+τ)=Σ λ^{j+1}x^j
    W = {(1, 0): Fr(1)}
    sig = {}
    for _ in range(NW + 2):
        e1 = exp_noconst(sig)                       # e^σ-1
        rest = add(e1, sig, -1)                     # e^σ-1-σ
        sig = mul(inv, add(W, {k: tau * v for k, v in rest.items()}, -1))
    # σ'(w)
    dsig = {(i - 1, j): i * v for (i, j), v in sig.items() if i >= 1}
    e1 = exp_noconst(sig)
    # 1/(1+T)，T=τe^σ：1+T=(1+τ)(1+μ(e^σ-1))，μ=τλ
    mu = tau * lam
    Yinv = {(0, 0): Fr(1)}
    term = {(0, 0): Fr(1)}
    for _ in range(NW + 2):
        term = mul(term, {k: -mu * v for k, v in e1.items()})
        Yinv = add(Yinv, term)
    Y = {k: lam * v for k, v in Yinv.items()}
    Gam = add(Y, mul(Y, Y), -1)                     # T/(1+T)^2 = Y - Y^2
    g = add({(0, 0): Fr(1)}, {(i, j + 2): v for (i, j), v in Gam.items() if j + 2 <= NX}, -1)
    H = mul(g, dsig)
    return {(i, j): v for (i, j), v in H.items() if i <= NW and j <= NX}


def H_closed(nj, lam):
    """闭式的单个 H_{n,j}（精确有理，λ 给定）。"""
    n, j = nj
    lam = Fr(lam)
    tau = 1 / lam - 1
    S2 = stirling2_table(n + 3)
    S2g = stirling2_ge2_table(2 * n + 4)
    # A(n,j)
    A = Fr(0)
    for c in range(n + 1):
        A += comb(n + j + c, n) * comb(j + c, c) * (lam - 1) ** c * Fr(fact(c) * S2g[n + c][c], fact(n + c))
    A *= lam ** (n + 1 + j)
    if j < 2:
        return A
    m = j - 2
    Yd = [lam * sum((lam - 1) ** i * fact(i) * S2[d][i] for i in range(d + 1)) / fact(d) for d in range(n + 1)]
    Gd = [Yd[d] - sum(Yd[e] * Yd[d - e] for e in range(d + 1)) for d in range(n + 1)]
    B = Fr(0)
    for c in range(n + 1):
        Q = sum(Fr(fact(c) * S2g[n - d + c][c], fact(n - d + c)) * Gd[d] for d in range(n - c + 1))
        B += comb(n + m + c, n) * comb(m + c, c) * (lam - 1) ** c * Q
    B *= lam ** (n + 1 + m)
    return A - B


def main():
    rep = Reporter('s15_a_lagrange')
    t0 = time.time()

    # ---- a-truth
    ok_b = all(U_dp_naive(k, m)[k] == U_brute(k, m) for k in range(0, 8) for m in range(0, 4))
    ok_f = all(U_dp_naive(14, m) == U_dp_fast(14, m) for m in range(0, 9))
    T = U_table_lemma1(30, 10)
    ok_l1 = all(U_dp_fast(30, m)[k] == T[k][m] for m in range(0, 11) for k in range(31))
    ok_pt = all(T[k][:7] == PROMPT_TABLE[k] for k in PROMPT_TABLE)
    Nrec = {k: list(row) for k, row in N_rows(60)}
    ok_n1 = True
    for k in range(1, 15):
        Ndef = N_from_U([U_dp_fast(k, m)[k] for m in range(k + 1)])
        ok_n1 &= Ndef[:k + 1] == Nrec[k] and all(v == 0 for v in Ndef[k + 1:])
    T60 = U_table_lemma1(60, 61)
    ok_n2 = True
    for k in range(1, 61):
        Nl = N_from_U([T60[k][m] for m in range(k + 1)])
        ok_n2 &= Nl[:k + 1] == Nrec[k]
    rep.check('a-truth', ok_b and ok_f and ok_l1 and ok_pt and ok_n1 and ok_n2,
              '枚举=朴素DP(k<=7,m<=3) %s；朴素DP=压缩DP(k<=14,m<=8) %s；压缩DP=引理1递推(k<=30,m<=10) %s；'
              '与任务说明 §2 的表一致 %s；(C3) 的 N 递推=定义容斥(k<=14) %s；=引理1表容斥(k<=60) %s'
              % (ok_b, ok_f, ok_l1, ok_pt, ok_n1, ok_n2))

    # ---- a-fk：f_k(λ) 两条路线
    t1 = time.time()
    Ksym = K_SYM
    TT = U_table_lemma1(Ksym, Ksym)
    rowsN = {k: list(row) for k, row in N_rows(max(Ksym, K_PT, K_PT2))}
    fN, ok_fk, ok_deg = {}, True, True
    for k in range(Ksym + 1):
        fN[k] = kfact_f_from_N(k, rowsN[k])
        h = h_from_U(k, [TT[k][m] for m in range(k + 1)])
        dmax = (2 * k) // 3
        ok_deg &= all(v == 0 for v in h[dmax + 1:]) and (k < 2 or h[dmax] != 0)
        ok_fk &= kfact_f_from_h(k, h) == fN[k]
    rep.check('a-fk', ok_fk and ok_deg, 'f_k(λ) 的两条路线（N 三角形 / U 表乘 (1-t)^{k+1}）逐个 k 相等（k<=%d）%s；deg h_k=⌊2k/3⌋ %s（%.1f s）'
              % (Ksym, ok_fk, ok_deg, time.time() - t1))

    # ---- a-sym：(0.1) 作为 Q[λ] 中的恒等式
    t1 = time.time()
    LS = LagrangeSym(Ksym)
    bad = []
    akf = {}
    for k in range(Ksym + 1):
        akf[k] = LS.kfact_a(k)
        if akf[k] != fN[k]:
            bad.append(k)
    rep.check('a-sym', not bad, '(0.1) 在 Q[λ] 中逐个 k 精确成立（k<=%d，λ=1/(1-t)，对一切 t≠1 同时成立）；不符的 k：%s（%.1f s）'
              % (Ksym, bad[:5], time.time() - t1))
    rep.info('例：k!a_k 在 k=3：%s（应为 3!·(2λ⁴-λ²)=[0,0,-6,0,12]）；k=6 的次数 %d'
             % (akf[3], len(akf[6]) - 1))

    # ---- a-pde：a_k=λa_{k-1}+λ²(λ-1)a'_{k-3}（乘 k!）
    ok_pde = akf[0] == [0, 1] and akf[1] == [0, 0, 1] and akf[2] == ptrim(pscale([0, 0, -1, 2], 2))
    for k in range(3, Ksym + 1):
        lhs = akf[k]
        rhs = padd(pscale(pshift(akf[k - 1], 1), k),
                   pscale(pmul([0, 0, -1, 1], pderiv(akf[k - 3])), k * (k - 1) * (k - 2)))
        ok_pde &= ptrim(rhs) == lhs
    rep.check('a-pde', ok_pde, 'Lagrange 一侧的 a_k 满足 a_k=λa_{k-1}+λ²(λ-1)a\'_{k-3}（k<=%d），初值 λ、λ²、2λ³-λ² %s'
              % (Ksym, ok_pde))

    # ---- a-rev-ser：单个系数 H_{n,j} 与直接级数反演
    t1 = time.time()
    ok_ser = True
    cnt = 0
    for tau in (Fr(1), Fr(1, 3)):
        Hs = series_reversion_H(tau, 6, 9)
        lam = 1 / (1 + tau)
        for n in range(7):
            for j in range(10):
                v1 = Hs.get((n, j), Fr(0))
                v2 = H_closed((n, j), lam)
                ok_ser &= v1 == v2
                cnt += 1
    rep.check('a-rev-ser', ok_ser, '闭式 H_{n,j} = 直接级数反演的系数（τ=1、1/3；n<=6，j<=9，共 %d 个，精确）%s（%.1f s）'
              % (cnt, ok_ser, time.time() - t1))

    # ---- a-points：具体 t
    t1 = time.time()
    pts_main = [(Fr(-1), K_PT), (Fr(-1, 3), K_PT), (Fr(-5), K_PT)]
    pts_more = [(Fr(-1, 2), K_PT2), (Fr(-3), K_PT2), (Fr(-1, 10), K_PT2), (Fr(-100), K_PT2), (Fr(-557, 2000), K_PT2)]
    msgs, ok_pts = [], True
    for t, KK in pts_main + pts_more:
        lam = 1 / (1 - t)
        LP = LagrangePoint(KK, lam.numerator, lam.denominator)
        badk = [k for k in range(KK + 1) if LP.a(k) != f_point(k, rowsN[k], lam.numerator, lam.denominator)]
        ok_pts &= not badk
        msgs.append('t=%s:k<=%d %s' % (t, KK, '全等' if not badk else '不符 %s' % badk[:3]))
    ex = LagrangePoint(30, 1, 2)
    rep.check('a-points', ok_pts, '；'.join(msgs) + '（例 t=-1：a_24=%s）（%.1f s）' % (ex.a(24), time.time() - t1))

    # ---- a-rev
    t1 = time.time()
    r1 = LagrangeSym(12, drop_g=True)
    first1 = next((k for k in range(13) if r1.kfact_a(k) != fN[k]), None)
    r2 = LagrangeSym(15, bump_s2g=(6, 2))
    first2 = next((k for k in range(16) if r2.kfact_a(k) != fN[k]), None)
    lamb = Fr(1, 2) + Fr(1, 100)
    r3 = LagrangePoint(12, lamb.numerator, lamb.denominator)
    first3 = next((k for k in range(13) if r3.a(k) != f_point(k, rowsN[k], 1, 2)), None)
    # 指数 n+1 改成 n+2：直接用 H_closed 的变体在 λ=1/2 上比较 a_k
    def a_bad(k, lam=Fr(3, 4)):
        tot = Fr(0)
        S2g = stirling2_ge2_table(2 * k + 4)
        for n in range(k // 3 + 1):
            j = k - 3 * n
            A = Fr(0)
            for c in range(n + 1):
                A += comb(n + 1 + j + c, n + 1) * comb(j + c, c) * (lam - 1) ** c * Fr(fact(c) * S2g[n + c][c], fact(n + c))
            A *= lam ** (n + 2 + j)
            tot += fact(n) * A
        return tot
    first4 = next((k for k in range(0, 2) if a_bad(k) != f_point(k, rowsN[k], 3, 4)), None)   # k<=1 时 g 的 x² 项不起作用
    ok_rev = all(v is not None for v in (first1, first2, first3, first4))
    rep.check('a-rev', ok_rev, '反向检查（都应出现不等）：去掉 g 的 x² 项→首个不符 k=%s；S≥2(6,2) 加 1→k=%s；λ 取 1/2+1/100→k=%s；'
              '(σ/ψ)^{n+1} 改成 ^{n+2}（t=-1/3，只看 k<=1）→k=%s（%.1f s）' % (first1, first2, first3, first4, time.time() - t1))

    print('（总用时 %.1f s）' % (time.time() - t0))
    return rep.summary()


if __name__ == '__main__':
    sys.exit(main())
