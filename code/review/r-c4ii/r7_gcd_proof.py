# -*- coding: utf-8 -*-
"""r7：复核者对「对一切 q，gcd(Num_q, P_{q-1}) = 1」（C4-23）的一般证明所用各环节的核对。

证明链（详见复核报告）：
 (1) Num_q ≡ W_i·S_{q,i} (mod b_i)（r3 已对 q<=40 精确核对；证明来自容斥式，符号恰好抵消）；
 (2) S_{q,i}(x) = n!·v^n·L_n^{(i+1)}(-1/v)，v = x^3，n = q-1-i，L_n^{(α)} 为广义 Laguerre 多项式；
     α=i+1>-1 时 L_n^{(α)} 的零点全为正实数，而 b_i 的非实根 ξ 处 v=ξ^3=(1-ξ)/i 非实、实根处 v>0，
     故 S_{q,i}(ξ) ≠ 0 对 b_i 的每个根成立；
 (3) W_i 在 b_i 的根处不为零：实根处为正项和；b_i 不可约时由共轭性推出全部根；
     b_i 可约（i=s^2(s-1)）时二次因子 Q_s ≡ 1-x (mod p)，p|s，而 W_i(1)=1，Gauss 引理给出 Q_s ∤ W_i。
"""
import sys
import time
import cmath
from fractions import Fraction
from math import comb, factorial
from rlib import *

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
t0 = time.time()
Lg = Log('r7_gcd_proof')


def S_poly(q, i):
    n = q - 1 - i
    p = [0] * (3 * n + 1)
    for t in range(0, n + 1):
        p[3 * t] = comb(q, t) * falling(n, t)
    return tr(p)


def laguerre(n, alpha):
    """L_n^{(alpha)}(X) 的升幂系数：sum_k (-1)^k C(n+alpha, n-k) X^k / k!（alpha 为非负整数）。"""
    return [Fraction((-1) ** k * comb(n + alpha, n - k), factorial(k)) for k in range(n + 1)]


# ---- (2a) 恒等式 S_{q,i}(x) = n! x^{3n} L_n^{(i+1)}(-x^{-3})，逐系数
ok = True
for q in range(1, 41):
    for i in range(0, q):
        n = q - 1 - i
        Lc = laguerre(n, i + 1)
        # n! x^{3n} * sum_k Lc[k] (-1)^k x^{-3k} = sum_k n! Lc[k] (-1)^k x^{3(n-k)}
        p = [Fraction(0)] * (3 * n + 1)
        for k in range(n + 1):
            p[3 * (n - k)] += factorial(n) * Lc[k] * (-1) ** k
        if tr(p) != [Fraction(c) for c in S_poly(q, i)]:
            ok = False
Lg.check('r7-laguerre-id', ok, 'S_{q,i}(x) == n! x^{3n} L_n^{(i+1)}(-1/x^3) 作为多项式恒等，0<=i<q<=40')

# ---- (2b) Laguerre 零点为正实数（Sturm 序列精确判定：L_n^{(α)} 在 (0,∞) 恰有 n 个不同实根，在 (-∞,0] 没有）
def sturm_count(p, a, b):
    """多项式 p（Fraction 升幂）在 (a,b] 内不同实根个数（Sturm 定理；a,b 为 Fraction 或 None 表示 ±∞）。"""
    def deg(f):
        return len(f) - 1

    def neg(f):
        return [-c for c in f]

    def deriv(f):
        return tr([k * f[k] for k in range(1, len(f))])
    seq = [tr(p), deriv(tr(p))]
    while seq[-1] and deg(seq[-1]) > 0:
        _, r = divmod_poly(seq[-2], seq[-1])
        if not r:
            break
        seq.append(neg(r))

    def sign_at(f, x):
        if x is None:
            return 0
        v = ev(f, x)
        return (v > 0) - (v < 0)

    def sign_inf(f, plus):
        lead = f[-1]
        s = (lead > 0) - (lead < 0)
        if not plus and deg(f) % 2 == 1:
            s = -s
        return s

    def changes(signs):
        s = [x for x in signs if x != 0]
        return sum(1 for u, v in zip(s, s[1:]) if u != v)
    sa = [sign_inf(f, False) if a is None else sign_at(f, a) for f in seq if f]
    sb = [sign_inf(f, True) if b is None else sign_at(f, b) for f in seq if f]
    return changes(sa) - changes(sb)


ok = True
for alpha in (1, 2, 5, 19, 101):
    for n in range(1, 16):
        Lc = laguerre(n, alpha)
        if sturm_count(Lc, Fraction(0), None) != n or sturm_count(Lc, None, Fraction(0)) != 0:
            ok = False
Lg.check('r7-laguerre-zeros', ok, 'Sturm 精确判定：alpha in {1,2,5,19,101}, n<=15 时 L_n^{(alpha)} 在 (0,∞) 恰有 n 个不同实根、在 (-∞,0] 无根（经典事实的旁证）')

# ---- (3a) W_i(1) = 1，且 W_i ≡ Wred_i (mod b_i)（后者 r3 已核对）；Q_s ≡ 1 - x (mod p), p|s
ok = all(ev(W_poly(i), 1) == 1 for i in range(0, 60))
for s in range(2, 60):
    for p in [d for d in range(2, s + 1) if s % d == 0 and all(d % e for e in range(2, d))]:
        if ((s - 1) % p, (s * (s - 1)) % p) != ((p - 1) % p, 0):
            ok = False
Lg.check('r7-W-at-1', ok, 'W_i(1)=1（i<60）；对 2<=s<60 的每个素因子 p|s，1+(s-1)x+s(s-1)x^2 ≡ 1-x (mod p)')

# ---- (数值旁证) b_i 的三个复根处 |S_{q,i}| 与 |W_i| 都远离 0（双精度，仅作旁证）
def roots_cubic(i):
    # -i x^3 - x + 1 = 0：用 numpy 求根
    import numpy as np
    return np.roots([-i, 0, -1, 1])


ok = True
minrel = 1e300
for i in range(1, 40):
    rts = roots_cubic(i)
    Wr = [0] * (3 * i + 3)
    Wr[0] = 1
    for l in range(1, i + 1):
        Wr[3 * l + 2] += l * falling(i, l)
    for xi in rts:
        xi = complex(xi)
        w = sum(complex(c) * xi ** k for k, c in enumerate(Wr) if c)
        scale_w = sum(abs(c) * abs(xi) ** k for k, c in enumerate(Wr) if c)
        minrel = min(minrel, abs(w) / scale_w)
        for q in range(i + 1, min(i + 25, 60)):
            sp = S_poly(q, i)
            sv = sum(complex(c) * xi ** k for k, c in enumerate(sp) if c)
            scale = sum(abs(c) * abs(xi) ** k for k, c in enumerate(sp) if c)
            if abs(sv) / scale < 1e-12:
                ok = False
Lg.check('r7-numeric-roots', ok, '双精度旁证：1<=i<40 的三个根处 |S_{q,i}(ξ)|/Σ|项| > 1e-12（i<q<min(i+25,60)）；|W_i(ξ)|/Σ|项| 最小值 %.2e' % minrel)
Lg.close(t0)
