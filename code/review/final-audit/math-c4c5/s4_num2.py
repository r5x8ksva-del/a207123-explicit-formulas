# -*- coding: utf-8 -*-
"""T4.3(7) 闭式（Q[y][[z]] 符号展开）与 T4.3(8) 既约性各环节（final-audit math-c4c5）。"""
import time
from fractions import Fraction
from math import comb, factorial, isqrt
import cmath

from alib import (say, check, N_tri, ptrim, padd, pmul, pscale, peval, pdivmod, write_log)

t0 = time.time()
F = Fraction
KM = 120
NT = N_tri(KM)


def b(i):
    return ptrim([1, -1, 0, -i])


def P(m):
    p = [1]
    for i in range(m + 1):
        p = pmul(p, b(i))
    return p


def W(m):
    w = [1]
    for j in range(1, m + 1):
        w = padd(w, [0, 0] + pscale(P(j - 1), j))
    return w


def Num(q):
    s = [NT[k][q] if q <= k else 0 for k in range(3 * q - 1)]
    pr = pmul(P(q - 1), s)
    return ptrim(pr[:3 * q - 1])


NUM = {q: Num(q) for q in range(1, 31)}

# ================= T4.3(7)：Σ_q R_q(y) z^q/q! 的闭式，Q[y][[z]] 中符号展开到 z^NZ
NZ = 11


def ya(p, q):      # y 多项式加
    return padd(p, q)


def ym(p, q):
    return pmul(p, q)


def sadd(A, B):
    return [ya(A[i], B[i]) for i in range(NZ)]


def smul(A, B):
    R = [[] for _ in range(NZ)]
    for i in range(NZ):
        if not A[i]:
            continue
        for j in range(NZ - i):
            if B[j]:
                R[i + j] = ya(R[i + j], ym(A[i], B[j]))
    return R


def sexp(S):
    """exp(S)，S[0]=0。n f_n = Σ_{k=1}^n k S_k f_{n-k}。"""
    assert not S[0]
    f = [[] for _ in range(NZ)]
    f[0] = [F(1)]
    for n in range(1, NZ):
        acc = []
        for k in range(1, n + 1):
            if S[k] and f[n - k]:
                acc = ya(acc, pscale(ym(S[k], f[n - k]), k))
        f[n] = pscale(acc, F(1, n))
    return f


y3 = [0, 0, 0, F(1)]
e = [0, 0, F(-1), F(1)]          # y^3 - y^2
# Φ = exp( Σ_{n>=1} (y^3 - e/n) z^n )
Sphi = [[]] + [ptrim(padd(y3, pscale(e, F(-1, n)))) for n in range(1, NZ)]
Phi = sexp(Sphi)
# g(w) = exp( Σ_{n>=1} e(-1)^{n+1}/n w^n - y^3 w )
Sg = [[]] + [ptrim(pscale(e, F((-1) ** (n + 1), n))) for n in range(1, NZ)]
Sg[1] = ptrim(padd(Sg[1], pscale(y3, -1)))
g = sexp(Sg)
# u = z/(1-z) 的幂
u = [[]] + [[F(1)] for _ in range(1, NZ)]
I = [[] for _ in range(NZ)]
upow = u
for n in range(0, NZ - 1):
    # g_n u^{n+1}/(n+1)
    term = [ptrim(pscale(ym(g[n], c), F(1, n + 1))) if c else [] for c in upow]
    I = sadd(I, term)
    upow = smul(upow, u)
# (Φ-1)/y^2
div_ok = True
PhiM1 = [list(Phi[i]) for i in range(NZ)]
PhiM1[0] = ptrim(padd(PhiM1[0], [F(-1)]))
Q = []
for c in PhiM1:
    c = ptrim(c)
    if len(c) >= 1 and c[0] != 0 or len(c) >= 2 and c[1] != 0:
        div_ok = False
    Q.append(ptrim(c[2:]))
A = sadd([ym([F(1), F(1)], c) if c else [] for c in Q], [pscale(ym([0, F(1)], c), -1) if c else [] for c in smul(Phi, I)])
ok = div_ok and not A[0]
bad = []
for q in range(1, NZ):
    R = [F(NUM[q][3 * q - 2 - j]) if 3 * q - 2 - j >= 0 else F(0) for j in range(3 * q - 1)]
    if ptrim(pscale(A[q], factorial(q))) != ptrim(R):
        bad.append(q)
check('T4.3.7-egf-symbolic', ok and not bad,
      '(y+1)(Φ-1)/y^2 - yΦ∫_0^{z/(1-z)}(1+w)^{y^3-y^2}e^{-y^3w}dw 在 Q[y][[z]] 中逐项等于 Σ R_q(y)z^q/q!（q<=%d，y 为符号）；Φ-1 的每个系数被 y^2 整除; bad=%s' % (NZ - 1, bad))
# y=1 特例
okY1 = all(sum(A[q][i] for i in range(len(A[q]))) * factorial(q) == peval(NUM[q], 1) for q in range(1, NZ))
check('T4.3.7-y1', okY1, 'y=1 时系数 = Num_q(1)（即 e^{z/(1-z)}-1 的系数，q<=%d）' % (NZ - 1))

# ================= T4.3(8)
# (a) b_i（i>=1）可约 ⇔ 有有理根 ⇔ i=r^2(r-1)
red = []
for i in range(1, 5001):
    # 有理根只能是 ±1/s，s|i；b_i(-1/s)=1+1/s+i/s^3>0
    roots = [s for s in range(1, i + 1) if i % s == 0 and s ** 3 - s * s - i == 0]
    if roots:
        red.append(i)
want = [r * r * (r - 1) for r in range(2, 30) if r * r * (r - 1) <= 5000]
check('T4.3.8-reducible', red == want, 'b_i（1<=i<=5000）有有理根 ⇔ i=r^2(r-1)：%s' % red)

# (b) 同余 Num_q ≡ W_i·S_{q,i} (mod b_i)，S_{q,i}=Σ_t C(q,t) n^{下降 t} x^{3t}，n=q-1-i
def S(q, i):
    n = q - 1 - i
    s = [0] * (3 * n + 1)
    for t in range(n + 1):
        ff = 1
        for r in range(t):
            ff *= (n - r)
        s[3 * t] = comb(q, t) * ff
    return ptrim(s)


bad = []
for q in range(1, 21):
    for i in range(q):
        diff = padd(NUM[q], pscale(pmul(W(i), S(q, i)), -1))
        if diff and pdivmod(diff, b(i))[1]:
            bad.append((q, i))
# 若把 n^{下降 t} 换成上升阶乘则失败（说明记号重要）
def S_rise(q, i):
    n = q - 1 - i
    s = [0] * (3 * n + 1)
    for t in range(n + 1):
        ff = 1
        for r in range(t):
            ff *= (n + r)
        s[3 * t] = comb(q, t) * ff
    return ptrim(s)


rise_fail = [(q, i) for q in range(2, 8) for i in range(q - 1)
             if pdivmod(padd(NUM[q], pscale(pmul(W(i), S_rise(q, i)), -1)), b(i))[1]]
check('T4.3.8-cong', not bad and rise_fail, 'Num_q ≡ W_i·S_{q,i} (mod b_i)，1<=q<=20、全部 0<=i<q（下降阶乘）；改用上升阶乘则失败，例如 %s' % rise_fail[:3])

# (c) Laguerre：S_{q,i}(x) = n!·v^n·L_n^{(i+1)}(-1/v)，v=x^3。L 用三项递推独立生成
def laguerre(n, al):
    """L_n^{(al)}(X)，升幂 Fraction 系数（三项递推）。"""
    L0 = [F(1)]
    if n == 0:
        return L0
    L1 = [F(1 + al), F(-1)]
    for k in range(1, n):
        Lk1 = padd(pmul([F(2 * k + 1 + al), F(-1)], L1), pscale(L0, -(k + al)))
        Lk1 = pscale(Lk1, F(1, k + 1))
        L0, L1 = L1, Lk1
    return L1


bad = []
for q in range(1, 26):
    for i in range(q):
        n = q - 1 - i
        Ln = laguerre(n, i + 1)
        # n! v^n Σ_k l_k (-1/v)^k = Σ_k n! l_k (-1)^k v^{n-k}
        coeffs_v = [F(0)] * (n + 1)
        for k, lk in enumerate(Ln):
            coeffs_v[n - k] += factorial(n) * lk * (-1) ** k
        Sv = [S(q, i)[3 * t] if 3 * t < len(S(q, i)) else 0 for t in range(n + 1)]
        if [F(x) for x in Sv] != coeffs_v:
            bad.append((q, i))
check('T4.3.8-laguerre', not bad, 'S_{q,i}=n!·v^n·L_n^{(i+1)}(-1/v)（L 由三项递推生成，1<=q<=25 全部 i<q）; bad=%s' % bad[:3])

# (d) gcd(Num_q, P_{q-1}) = 1：模大素数 Euclid（p ∤ 首项系数），q<=30
p = (1 << 61) - 1


def pmod(a):
    return [int(x) % p for x in a]


def ptrim_m(a):
    a = list(a)
    while a and a[-1] % p == 0:
        a.pop()
    return a


def pdivmod_m(a, bb):
    a = ptrim_m(a)
    bb = ptrim_m(bb)
    inv = pow(bb[-1], p - 2, p)
    while len(a) >= len(bb) and a:
        c = a[-1] * inv % p
        dd = len(a) - len(bb)
        for i, x in enumerate(bb):
            a[i + dd] = (a[i + dd] - c * x) % p
        a = ptrim_m(a)
    return a


def gcd_deg_m(a, bb):
    a, bb = ptrim_m(pmod(a)), ptrim_m(pmod(bb))
    while bb:
        a, bb = bb, pdivmod_m(a, bb)
    return len(a) - 1


bad = []
for q in range(1, 31):
    A_, B_ = NUM[q], P(q - 1)
    if A_[-1] % p == 0 or B_[-1] % p == 0:
        bad.append(('lc', q))
    if gcd_deg_m(A_, B_) != 0:
        bad.append(q)
check('T4.3.8-gcd', not bad, 'gcd(Num_q,P_{q-1})=1（模 2^61-1 的 Euclid，p 不整除两者首项系数），1<=q<=30; bad=%s' % bad)

# (e) 数值旁证：b_4、b_18 二次因子的非实根处 Num_q 与 S_{q,i}、W_i 都不为 0
mins = []
for (i, r) in ((4, 2), (18, 3)):
    # 二次因子 1+(r-1)x+r(r-1)x^2
    a2, a1, a0 = r * (r - 1), r - 1, 1
    disc = a1 * a1 - 4 * a2 * a0
    xi = (-a1 + cmath.sqrt(disc)) / (2 * a2)
    assert abs(1 - xi - i * xi ** 3) < 1e-12
    for q in range(i + 1, 31):
        vN = sum(complex(c) * xi ** k for k, c in enumerate(NUM[q]))
        vW = sum(complex(c) * xi ** k for k, c in enumerate(W(i)))
        vS = sum(complex(c) * xi ** k for k, c in enumerate(S(q, i)))
        scale = sum(abs(complex(c) * xi ** k) for k, c in enumerate(NUM[q]))
        mins.append(abs(vN) / scale)
        if abs(vN - vW * vS) > 1e-6 * scale:
            mins.append(-1)
check('T4.3.8-numeric', min(mins) > 0, 'b_4、b_18 二次因子的复根 ξ 处 Num_q(ξ)=W_i(ξ)S_{q,i}(ξ)≠0（q<=30，双精度），min|Num|/Σ|项| = %.3g' % min(mins))

# (f) W_i 与 b_i 互素（T1.3(2) 的特例）
bad = [i for i in range(0, 60) if gcd_deg_m(W(i), b(i)) != 0]
check('T4.3.8-W-coprime', not bad, 'gcd(W_i,b_i)=1（0<=i<60，模 p）; bad=%s' % bad)

say('elapsed %.1fs' % (time.time() - t0))
write_log('final_audit_math-c4c5_s4.log')
