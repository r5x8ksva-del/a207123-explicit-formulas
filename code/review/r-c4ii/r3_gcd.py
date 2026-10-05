# -*- coding: utf-8 -*-
"""r3：既约性 gcd(Num_q, P_{q-1}) = 1（C4-21/22/23）的独立复核与推广。

复核者的新引理（由容斥式 C4-20 直接得到，见复核报告）：对 0 <= i <= q-1，
    Num_q ≡ W_i(x) · S_{q,i}(x)   (mod b_i)，
    W_i ≡ 1 + sum_{l=1}^{i} l·(i)_l·x^{3l+2}            (mod b_i)，
    S_{q,i}(x) := sum_{t=0}^{q-1-i} C(q,t)·(q-1-i)_t·x^{3t}，  (n)_t 为下降阶乘。
在 b_i 的正实根处两个因子都是正项和，故 Num_q(x_i) > 0。
"""
import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction
from math import comb, factorial
from rlib import *

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
t0 = time.time()
L = Log('r3_gcd')
Num = num_by_recurrence(60)


def S_poly(q, i):
    n = q - 1 - i
    p = [0] * (3 * n + 1)
    for t in range(0, n + 1):
        p[3 * t] = comb(q, t) * falling(n, t)
    return tr(p)


def Wred(i):
    p = [0] * (3 * i + 3)
    p[0] = 1
    for l in range(1, i + 1):
        p[3 * l + 2] += l * falling(i, l)
    return tr(p)


# ---- (a) 新引理：精确多项式同余（有理系数带余除法）
ok_W, ok_N = True, True
for i in range(0, 40):
    b = bpoly(i)
    _, r1 = divmod_poly(sub(W_poly(i), Wred(i)), b)
    if r1:
        ok_W = False
for q in range(1, 41):
    for i in range(0, q):
        b = bpoly(i)
        rhs = mul(Wred(i), S_poly(q, i))
        _, r = divmod_poly(sub(Num[q], rhs), b)
        if r:
            ok_N = False
            L.out('  congruence fails q=%d i=%d' % (q, i))
L.check('r3-W-cong', ok_W, 'W_i ≡ 1 + sum_{l<=i} l (i)_l x^{3l+2} (mod b_i)，0<=i<=39（精确带余除法）')
L.check('r3-Num-cong', ok_N, 'Num_q ≡ W_i·sum_{t=0}^{q-1-i} C(q,t)(q-1-i)_t x^{3t} (mod b_i)，全部 0<=i<q<=40（精确带余除法）')

# ---- (b) 数值旁证：b_i 正根处 Num_q(x_i) 与两因子乘积一致且为正
getcontext().prec = 60


def real_root(i):
    if i == 0:
        return Decimal(1)
    lo, hi = Decimal(0), Decimal(1)
    for _ in range(220):
        mid = (lo + hi) / 2
        if 1 - mid - i * mid ** 3 > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


ok = True
maxrel = Decimal(0)
for q in (5, 12, 25, 40):
    for i in range(0, q):
        x = real_root(i)
        lhs = ev(Num[q], x)
        rhs = ev(Wred(i), x) * ev(S_poly(q, i), x)
        if not (lhs > 0 and rhs > 0):
            ok = False
        rel = abs(lhs - rhs) / rhs
        maxrel = max(maxrel, rel)
ok = ok and maxrel < Decimal('1e-30')
L.check('r3-Num-at-root', ok, 'q in {5,12,25,40}、全部 i<q：Num_q(x_i) > 0 且与 W_i(x_i)S_{q,i}(x_i) 相对误差 %.1e（60 位 Decimal，容差 1e-30）' % maxrel)

# ---- (c) 模 p 证书：对每个 i<q<=QB，Num_q mod (p, f) != 0，f 取 b_i（不可约时）或其因子
QB = 1000
PR = (1000003, 998244353)


def make_ring(f, p):
    """F_p[x]/(f)，f 为系数列表（升幂），首项在 F_p 可逆。返回 mul 函数与次数。"""
    d = len(f) - 1
    inv = pow(f[-1] % p, p - 2, p)
    mon = [(-c * inv) % p for c in f[:-1]]          # x^d = sum mon[j] x^j

    def red(a):
        a = [c % p for c in a]
        for k in range(len(a) - 1, d - 1, -1):
            c = a[k]
            if c:
                a[k] = 0
                for j in range(d):
                    a[k - d + j] = (a[k - d + j] + c * mon[j]) % p
        return (a + [0] * d)[:d]

    def rmul(a, b):
        r = [0] * (2 * d - 1)
        for u in range(d):
            if a[u]:
                for v in range(d):
                    r[u + v] += a[u] * b[v]
        return red(r)
    return d, red, rmul


def num_mod_series(f, p, QM):
    """返回 [Num_1 mod (p,f), ..., Num_QM mod (p,f)]（由三项递推）。"""
    d, red, rmul = make_ring(f, p)
    xx = red([0, 1])
    x3 = red([0, 0, 0, 1])
    N1 = red([0, 1])
    N2 = red([0, 0, 2, 0, 1])
    out = {1: N1, 2: N2}
    a, b = N1, N2
    for q in range(3, QM + 1):
        c1 = red([0, 1, 0, 2 * (q - 1)])
        bq = red([0, 0, 0, (q - 1), -(q - 1), 0, -(q - 1) * (q - 2)])   # (q-1)x^3 b_{q-2}
        new = [(u + v) % p for u, v in zip(rmul(c1, b), rmul(bq, a))]
        out[q] = new
        a, b = b, new
    return out


def reducible_s(i):
    s = 2
    while s * s * (s - 1) < i:
        s += 1
    return s if s * s * (s - 1) == i else None


QB = 1000
bad_irred = []
t1 = time.time()
for i in range(1, QB):
    if reducible_s(i):
        continue
    f = bpoly(i)
    seq1 = num_mod_series(f, PR[0], QB)
    zq = [q for q in range(i + 1, QB + 1) if not any(seq1[q])]
    if zq:
        seq2 = num_mod_series(f, PR[1], QB)
        bad_irred += [(q, i) for q in zq if not any(seq2[q])]
L.check('r3-modcert-irred', not bad_irred,
        '模 p 证书（p=1000003，必要时 998244353）：对全部不可约 b_i（1<=i<%d）与 i<q<=%d，Num_q mod (p,b_i) 非零 ⇒ b_i∤Num_q（%.1fs）' % (QB, QB, time.time() - t1))

bad_red = []
info = []
for s in range(2, 14):
    i = s * s * (s - 1)
    QBs = 3000
    quad = [1, s - 1, s * (s - 1)]
    lin = [1, -s]
    for f, tag in ((quad, 'quad'), (lin, 'lin')):
        seqs = [num_mod_series(f, p, QBs) for p in PR]
        cnt = 0
        for q in range(i + 1, QBs + 1):
            cnt += 1
            if all(not any(seq[q]) for seq in seqs):
                bad_red.append((s, tag, q))
        info.append('s=%d(i=%d,%s,q=%d..%d)' % (s, i, tag, i + 1, QBs))
L.check('r3-modcert-red', not bad_red,
        '模 p 证书：可约 b_{s^2(s-1)}（s=2..13，i=4..2028）的一次因子 1-sx 与二次因子 1+(s-1)x+s(s-1)x^2 都不整除 Num_q，i<q<=3000')

# ---- (d) 二次因子不整除 W_i（不依赖 q 的那一半）
ok = True
for s in range(2, 8):
    i = s * s * (s - 1)
    quad = [1, s - 1, s * (s - 1)]
    for p in PR:
        d, red, rmul = make_ring(quad, p)
        if not any(red(Wred(i))):
            ok = False
L.check('r3-W-quad', ok, 's=2..7：二次因子 1+(s-1)x+s(s-1)x^2 不整除 W_{s^2(s-1)}（模 p 非零）')

# ---- (e) s 偶数时的 mod 2 论证所需事实：二次因子 ≡ 1+x (mod 2)，Num_q(1)=A000262(q) 为奇数（r2 已核对）
ok = all(((s - 1) % 2, (s * (s - 1)) % 2) == (1, 0) for s in range(2, 200, 2))
L.check('r3-mod2', ok, 's 偶数：1+(s-1)x+s(s-1)x^2 ≡ 1+x (mod 2)；配合 A000262 恒为奇数（r2-A000262-odd）给出对一切 q 的证明')

# ---- (f) s=3 的 mod 3 论证覆盖范围：A000262(q) mod 3
a = [1, 1]
for n in range(2, 400):
    a.append((2 * n - 1) * a[n - 1] - (n - 1) * (n - 2) * a[n - 2])
zeros = [q for q in range(1, 400) if a[q] % 3 == 0]
L.out('# A000262(q) ≡ 0 (mod 3) 的 q（<400）前若干：%s；全部 ≡2 (mod 3)：%s' % (zeros[:12], all(q % 3 == 2 for q in zeros)))
L.close(t0)
