# -*- coding: utf-8 -*-
"""s12-b4t3：notes/13 注 5.2「每个 i 两个原子」一段的复核。
  N1 按定义的 N(k,q)（值域恰为 {1..q}）DP 与全枚举；
  N2 容斥 N(k,q)=sum_M (-1)^{q-1-M} C(q,M+1) U_k(M)（k>=1）与 F_q=(-1)^q+sum_M ... G_M；
  N3 E_{q,i} 的公式与 F_q 直接部分分式（Num_q (P_{q-1}/b_i)^{-1} mod b_i）比较，x=1 处的留数；
  N4/N5 q=2、q=3 的式子（按定义的 N，1<=k<=300），c 与 c~，递推窗口；
  N6 q=4：E_{4,3}=x^{-9}W~_3/3!；N7 q>=5 的纤维元素；
  N8（附带）q=5..QMAX：纤维 3 的元素 x^{-3(q-1)} W~_3 L_q(x^3) 在同一个 K_3 上，用同一套筛法 + l 进证书逐个判定。
不导入项目的任何模块。
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial, gcd

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_common import (setup_utf8, Reporter, U_dp, N_dp, N_brute, P_poly, W_poly, Wt_dict, series_div,
                       c_seq, CBar, KField, in_span2, pmul, padd, pscale, b_poly, det3cols)

setup_utf8()
R = Reporter('s12-b4t3-notes13')
t00 = time.time()
QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 30

# ---- N1
okb = all(N_dp(q, 8)[k] == N_brute(q, k) for q in range(1, 5) for k in range(0, 9))
R.check('N1-dp-brute', okb, 'N(k,q) 的 DP 与全枚举一致（1<=q<=4，0<=k<=8）')

Ndef = {q: N_dp(q, 60) for q in range(1, 7)}
Ndef[2] = N_dp(2, 300)
Ndef[3] = N_dp(3, 300)
U = {m: U_dp(m, 300) for m in range(0, 7)}


def cM(q, M):
    return (-1) ** (q - 1 - M) * comb(q, M + 1)


# ---- N2 容斥与 F_q
ok2 = True
for q in range(1, 7):
    K = len(Ndef[q]) - 1
    for k in range(1, K + 1):
        ok2 &= (Ndef[q][k] == sum(cM(q, M) * U[M][k] for M in range(q)))
k0 = {q: sum(cM(q, M) * U[M][0] for M in range(q)) for q in range(1, 7)}
R.check('N2-incl-excl', ok2 and all(k0[q] == -(-1) ** q for q in k0),
        '容斥对 1<=q<=6、1<=k<=60（q=2,3 到 300）成立；k=0 时右边 = -(-1)^q：%s，而 N(0,q)=0，所以 F_q 要加常数 (-1)^q' % k0)


def Num(q):
    """F_q = Num_q / P_{q-1}，Num_q = (-1)^q P_{q-1} + sum_M c_M W_M prod_{v=M+1}^{q-1} b_v。"""
    acc = pscale(P_poly(q - 1), (-1) ** q)
    for M in range(q):
        t = W_poly(M)
        for v in range(M + 1, q):
            t = pmul(t, b_poly(v))
        acc = padd(acc, pscale(t, cM(q, M)))
    while len(acc) > 1 and acc[-1] == 0:
        acc.pop()
    return acc


okF = True
degs = {}
for q in range(1, 7):
    Nq = Num(q)
    degs[q] = len(Nq) - 1
    s = series_div(Nq, P_poly(q - 1), 60)
    okF &= all(s[k] == Ndef[q][k] for k in range(61))
R.check('N2-Fq', okF, 'F_q=(-1)^q+sum_M c_M G_M 的展开 = 按定义的 N(k,q)（含 k=0，1<=q<=6，k<=60）；deg Num_q（分母 P_{q-1} 的次数 3q-2）：%s' % degs)


def kappa(M, i):
    return Fr((-1) ** (M - i), factorial(i) * factorial(M - i))


def E_formula(q, i, Ki):
    acc = (Fr(0), Fr(0), Fr(0))
    Wti = Ki.from_dict(Wt_dict(i))
    for M in range(i, q):
        t = Ki.mul(Ki.xpow(-3 * M), Wti)
        acc = tuple(acc[r] + cM(q, M) * kappa(M, i) * t[r] for r in range(3))
    return acc


# ---- N3 E_{q,i}：公式 vs 直接部分分式；x=1 的留数
ok3 = True
n3 = 0
gam = {}
for q in range(2, 9):
    Nq = Num(q)
    for i in range(1, q):
        Ki = KField(i)
        other = [1]
        for v in range(q):
            if v != i:
                other = pmul(other, b_poly(v))
        direct = Ki.mul(Ki.reduce_poly(Nq), Ki.inv(Ki.reduce_poly(other)))
        ok3 &= (direct == E_formula(q, i, Ki))
        n3 += 1
    r0 = Fr(sum(Nq))
    for v in range(1, q):
        r0 /= -v
    g = sum(cM(q, M) * Fr((-1) ** M, factorial(M)) for M in range(q))
    ok3 &= (r0 == g)
    gam[q] = g
R.check('N3-Eqi', ok3, 'E_{q,i}=sum_{M=i}^{q-1} c_M (-1)^{M-i}/(i!(M-i)!) x^{-3M} W~_i 与 F_q 的直接部分分式一致（%d 对 (q,i)，2<=q<=8）；x=1 处 gamma_q：%s' % (n3, {q: str(gam[q]) for q in gam}))

cs = {i: c_seq(i, 360) for i in range(0, 4)}
cb = {i: CBar(i, 360, 40) for i in range(1, 4)}


def c(i, n):
    return cs[i][n] if n >= 0 else 0


# ---- N4 q=2
bad = [k for k in range(1, 301) if c(1, k + 3) + c(1, k - 2) - 3 != Ndef[2][k]]
K1, K2, K3 = KField(1), KField(2), KField(3)
E21 = E_formula(2, 1, K1)
ok, co = in_span2(K1, E21, -3, 2)
R.check('N4-q2', bad == [] and ok and co == (1, 1) and gam[2] == -3,
        'N(k,2)=c_1(k+3)+c_1(k-2)-3 对 1<=k<=300 成立（不符：%s）；E_{2,1}=x^-3+x^2；gamma=-3' % bad)

# ---- N5 q=3
def rhs3(k, f1, f2):
    return Fr(13, 2) - f1(k + 8) - 2 * f1(k - 2) + Fr(5, 2) * f2(k + 3) + 6 * f2(k - 2)


bad3 = [k for k in range(0, 301) if rhs3(k, lambda n: c(1, n), lambda n: c(2, n)) != Ndef[3][k]]
bad3b = [k for k in range(0, 301) if rhs3(k, cb[1], cb[2]) != Ndef[3][k]]
E31, E32 = E_formula(3, 1, K1), E_formula(3, 2, K2)
ok31, co31 = in_span2(K1, E31, -8, 2)
ok32, co32 = in_span2(K2, E32, -3, 2)
R.check('N5-q3', bad3 == [0] and bad3b == [0] and ok31 and co31 == (-1, -2) and ok32 and co32 == (Fr(5, 2), 6) and gam[3] == Fr(13, 2),
        'N(k,3)=13/2-c_1(k+8)-2c_1(k-2)+(5/2)c_2(k+3)+6c_2(k-2)：0<=k<=300 中不符的 k（c 版）%s、（c~ 版）%s（k=0 时 N=0、式子给 %s）；'
        'E_{3,1}=%s x^-8 + %s x^2，E_{3,2}=%s x^-3 + %s x^2；gamma=13/2'
        % (bad3, bad3b, rhs3(0, lambda n: c(1, n), lambda n: c(2, n)), co31[0], co31[1], co32[0], co32[1]))
# 递推窗口：N(k,3) 对哪些 k 满足 P_2 递推；右边（c~）对一切 k 满足
P2 = P_poly(2)
recN = [k for k in range(7, 301) if sum(P2[j] * Ndef[3][k - j] for j in range(8)) != 0]
recR = all(sum(P2[j] * rhs3(k - j, cb[1], cb[2]) for j in range(8)) == 0 for k in range(-20, 301))
negidx = sorted({(k, n) for k in range(1, 8) for n in (k - 2,) if n < 0})
R.check('N5-window', recN == [7] and recR and negidx == [(1, -1)] and cb[1](-1) == 0 and cb[2](-1) == 0,
        'N(k,3) 在 7<=k<=300 中不满足 P_2 递推的只有 k=%s（k=7 用到 N(0,3)=0 而 F_3 含常数 -1），即递推对 k>=8 成立；右边（c~）对 -20<=k<=300 都满足；'
        'k>=1 时用到的负下标只有 %s，且 c~_1(-1)=c~_2(-1)=0——所以 1<=k<=7 一致即推出一切 k>=1' % (recN, negidx))

# ---- N6 q=4
E43 = E_formula(4, 3, K3)
target = tuple(t / 6 for t in K3.mul(K3.xpow(-9), K3.from_dict(Wt_dict(3))))
win43 = [(a, b) for a in range(-60, 61) for b in range(a + 1, 61) if det3cols(E43, K3.xpow(a), K3.xpow(b)) == 0]
E41, E42 = E_formula(4, 1, K1), E_formula(4, 2, K2)
w41 = [(a, b) for a in range(-40, 41) for b in range(a + 1, 41) if det3cols(E41, K1.xpow(a), K1.xpow(b)) == 0]
w42 = [(a, b) for a in range(-40, 41) for b in range(a + 1, 41) if det3cols(E42, K2.xpow(a), K2.xpow(b)) == 0]
R.check('N6-q4', E43 == target and win43 == [],
        'q=4：E_{4,3} = x^-9 W~_3/3!（精确）；|a|,|a\'|<=60 内 E_{4,3}∈span(x^a,x^a\') 无解（一般情形由引理 3.1：E_{4,3}∈span(x^a,x^a\') ⇔ W~_3∈span(x^{a+9},x^{a\'+9})）；'
        '数据：纤维 1、2 在 |a|,|a\'|<=40 内的两原子解 %d、%d 对（纤维 1、2 不是障碍）' % (len(w41), len(w42)))

# ---- N7 q>=5：最高纤维元素是纯的，纤维 3 的元素带 Laguerre 因子
ok7 = True
for q in range(5, 9):
    Kt = KField(q - 1)
    top = E_formula(q, q - 1, Kt)
    ok7 &= (top == tuple(Fr(1, factorial(q - 1)) * t for t in Kt.mul(Kt.xpow(-3 * (q - 1)), Kt.from_dict(Wt_dict(q - 1)))))
E53 = E_formula(5, 3, K3)
f53 = tuple(Fr(-1, 6) * t for t in K3.mul(K3.mul(K3.xpow(-12), K3.from_dict(Wt_dict(3))), K3.from_dict({0: 1, 3: 5})))
R.check('N7-q5', ok7 and E53 == f53,
        'q=5..8：最高纤维 q-1 的元素 = x^{-3(q-1)} W~_{q-1}/(q-1)!；但纤维 3 在 q>=5 时 = 带 Laguerre 因子的元素，例如 E_{5,3} = -(1/6) x^-12 W~_3 (1+5x^3)（精确）')

# ---- N8（附带）：q=5..QMAX，纤维 3 用同一套证书（T=6720，笔记的 8 个素数）判定
CERT = [(5, 20), (13, 84), (31, 480), (71, 70), (97, 96), (193, 96), (449, 448), (673, 672)]
T = 6720


def rec_mod(l, E, mod):
    inv = pow(3, -1, mod)
    V = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
    for e in range(3, E + 1):
        a, b = V[e - 3], V[e - 2]
        V.append(tuple(((a[t] - b[t]) * inv) % mod for t in range(3)))
    return V


Vtab = {l: rec_mod(l, P + 80, l) for (l, P) in CERT}
mus = {}
for (l, P) in CERT:
    y = rec_mod(l, P, l * l)[P]
    assert y[0] % l == 1 and y[1] % l == 0 and y[2] % l == 0
    mus[l] = ((y[1] // l) % l, (y[2] // l) % l)


def fiber3_poly(q):
    """x^{3(q-1)} * E_{q,3} 的多项式（整系数、本原），即 W~_3 * sum_M e_M x^{3(q-1-M)}。"""
    L = {}
    for M in range(3, q):
        L[3 * (q - 1 - M)] = cM(q, M) * kappa(M, 3)
    poly = {}
    for d1, c1 in Wt_dict(3).items():
        for d2, c2 in L.items():
            poly[d1 + d2] = poly.get(d1 + d2, 0) + c1 * c2
    den = 1
    for v in poly.values():
        den = den * Fr(v).denominator // gcd(den, Fr(v).denominator)
    ints = {d: int(v * den) for d, v in poly.items() if v != 0}
    g = 0
    for v in ints.values():
        g = gcd(g, abs(v))
    return {d: v // g for d, v in ints.items()}


def decide(poly):
    nidx = np.arange(T)
    tabs = {}
    for (l, P) in CERT:
        V = Vtab[l]
        if max(poly) + P > len(V) - 1:
            V = rec_mod(l, max(poly) + P + 1, l)
        Wn = np.zeros((P, 3), dtype=np.int64)
        for d, cf in poly.items():
            Wn = (Wn + (cf % l) * np.array(V[d:d + P], dtype=np.int64)) % l
        Vb = np.array(V[:P], dtype=np.int64)
        tabs[l] = (P, Vb, Wn)
    surv = 0
    for b0 in range(0, T, 256):
        bidx = np.arange(b0, min(T, b0 + 256))
        alive = np.ones((len(bidx), T), dtype=bool)
        for (l, P) in CERT:
            _, Vb, Wn = tabs[l]
            alive &= ((Vb[bidx % P, 1][:, None] * Wn[nidx % P, 2][None, :] - Vb[bidx % P, 2][:, None] * Wn[nidx % P, 1][None, :]) % l) == 0
        alive[bidx == 0, :] = False
        surv += int(alive.sum())
    cov = np.zeros(T, dtype=bool)
    for (l, P) in CERT:
        _, Vb, Wn = tabs[l]
        mu = mus[l]
        cov |= ((mu[0] * Wn[nidx % P, 2] - mu[1] * Wn[nidx % P, 1]) % l) != 0
    return surv, int((~cov).sum())


res8 = {}
for q in range(4, QMAX + 1):
    poly = fiber3_poly(q)
    res8[q] = decide(poly)
p4 = fiber3_poly(4)
okp4 = p4 == {0: 1, 5: 3, 8: 12, 11: 18}
undecided = [q for q in res8 if res8[q] != (0, 0)]
R.check('N8-fiber3-q', okp4 and res8[4] == (0, 0),
        '附带：纤维 3 的元素（乘 x^{3(q-1)}、整系数本原化）在 q=4 时就是 W~_3（%s），证书照常成立；q=5..%d 用同一套 T=6720 证书的结果 (b≢0 幸存类数, l 进未解决数)：%s；未判定的 q：%s'
        % (okp4, QMAX, {q: res8[q] for q in res8 if q >= 5}, undecided))
# 负对照：把 q=5 的元素换成 x^3 * x^7（单项式）——l 进步骤必须失败
neg = decide({7: 1})
R.check('N8-negctrl', neg[1] > 0, '负对照：元素换成单项式 x^7 时 l 进步骤未解决 %d 个 n0（应 >0：n=-7 处 W x^n 为常数）' % neg[1])

print('time %.1fs' % (time.time() - t00))
R.finish()
