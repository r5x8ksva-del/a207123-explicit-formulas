# -*- coding: utf-8 -*-
"""x1-single-sum 复核脚本 r2：两族（两项 u 型）表示的留数必要条件——独立穷举并扩大范围。

背景（c2a §6.3，复核者已逐步重推）：若 V = x^{-N1} A1(u) + x^{-N2} A2(u) + Laurent 多项式（N1 != N2），
则对 V 的每个不可约极点纤维 u = 1/i（i x^3 + x - 1 不可约），留数元 theta_i、x^{-N1}、x^{-N2} 在 K_i 中 Q-线性相关。
由 r1 已核对的闭式 theta_i ∝ x^{-3m-3} * R_i(x)：
   U：R_i = W~_i := 1 + sum_{j=1}^i j i^(j) x^{3j+2}
   E：R_i = W~_i - 1
令 a := 3m+3-N1, b := 3m+3-N2，条件化为与 m 无关的 det(R_i, x^a, x^b) = 0。

本脚本：
  (U) 纤维 1 的解集（|a|,|b|<=NU）及其与纤维 2 的交集；重现 c2a 的「|a|,|b|<=150 内恰 14 组、无公共解」，并扩到 NU。
  (E) 纤维 1、2、3 的公共解（|a|,|b|<=NE）：用于核对 c2b §6.4「E(k,m)（3<=m<=6）两项 u 型盒内无解」，
      并把它推广到「对所有 m>=3、指数在范围内」；对照：m=2 的真实两项表示 (a,b)=(5,8) 必须通过纤维 1、2。
做法：先在两个 ~2^30 的素数下用 numpy 向量化筛 det≡0，再对候选做精确有理数核对（所有结论只依赖精确核对）。
"""
import sys
import time
from fractions import Fraction as F
import numpy as np

T0 = time.time()
FAILS = []


def log(s):
    print(s, flush=True)


def check(name, ok, desc):
    log(('PASS ' if ok else 'FAIL ') + name + ' ' + desc)
    if not ok:
        FAILS.append(name)


NU = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
NE = int(sys.argv[2]) if len(sys.argv) > 2 else 1500
PR = (1000000007, 998244353)


# ---------------- 精确 K_i 运算（Fraction）
class Cubic:
    def __init__(self, i):
        self.i = F(i)

    def red(self, p):
        p = [F(c) for c in p] + [F(0)] * max(0, 3 - len(p))
        for d in range(len(p) - 1, 2, -1):
            c = p[d]
            if c:
                p[d] = F(0)
                p[d - 3] += c / self.i
                p[d - 2] -= c / self.i
        return p[:3]

    def mul(self, a, b):
        r = [F(0)] * 5
        for s in range(3):
            if a[s]:
                for t in range(3):
                    r[s + t] += a[s] * b[t]
        return self.red(r)

    def pw(self, n):
        base = [F(0), F(1), F(0)] if n >= 0 else [F(1), F(0), self.i]   # x^{-1} = 1 + i x^2
        r = [F(1), F(0), F(0)]
        e = abs(n)
        while e:
            if e & 1:
                r = self.mul(r, base)
            base = self.mul(base, base)
            e >>= 1
        return r


def det3(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def Rpoly(i, which):
    W = [0] * (3 * i + 3)
    W[0] = 1
    ff = 1
    for j in range(1, i + 1):
        ff *= (i - j + 1)
        W[3 * j + 2] += j * ff
    if which == 'E':
        W[0] -= 1
    return W


# ---------------- 模 p 的 x^n 坐标表
def powers_modp(i, N, p):
    inv_i = pow(i, -1, p)
    X = np.zeros((2 * N + 1, 3), dtype=np.int64)
    cur = [1, 0, 0]
    X[N] = cur
    for n in range(1, N + 1):          # 乘 x：x*(c0 + c1 x + c2 x^2) = c0 x + c1 x^2 + c2 (1-x)/i
        c0, c1, c2 = cur
        t = c2 * inv_i % p
        cur = [t, (c0 - t) % p, c1]
        X[N + n] = cur
    cur = [1, 0, 0]
    for n in range(1, N + 1):          # 乘 x^{-1} = 1 + i x^2
        c0, c1, c2 = cur
        # (c0 + c1 x + c2 x^2)(1 + i x^2) = c0 + c1 x + (c2 + i c0) x^2 + i c1 x^3 + i c2 x^4
        # x^3 = (1-x)/i, x^4 = (x - x^2)/i
        d0 = c0 + c1
        d1 = c1 - c1 + c2
        d2 = c2 + i * c0 - c2
        cur = [d0 % p, d1 % p, d2 % p]
        X[N - n] = cur
    return X


def red_modp(i, poly, p):
    inv_i = pow(i, -1, p)
    q = [c % p for c in poly] + [0] * 3
    for d in range(len(q) - 1, 2, -1):
        c = q[d]
        if c:
            q[d] = 0
            q[d - 3] = (q[d - 3] + c * inv_i) % p
            q[d - 2] = (q[d - 2] - c * inv_i) % p
    return [int(v) for v in q[:3]]


def solutions(i, which, N, extra_filter=None):
    """返回 |a|,|b|<=N, a<b 且 det(R_i, x^a, x^b) = 0 的全部 (a,b)（模 p 筛 + 精确核对）。"""
    cand = None
    for p in PR:
        X = powers_modp(i, N, p)
        w = red_modp(i, Rpoly(i, which), p)
        found = set()
        for ai in range(2 * N + 1):
            xa = [int(v) for v in X[ai]]
            c = [(w[1] * xa[2] - w[2] * xa[1]) % p, (w[2] * xa[0] - w[0] * xa[2]) % p, (w[0] * xa[1] - w[1] * xa[0]) % p]
            cvec = np.array(c, dtype=np.int64)
            d = (X[ai + 1:] @ cvec) % p
            for off in np.nonzero(d == 0)[0]:
                found.add((ai - N, ai + 1 + int(off) - N))
        cand = found if cand is None else (cand & found)
    K = Cubic(i)
    w = K.red(Rpoly(i, which))
    exact = sorted((a, b) for (a, b) in cand if det3(w, K.pw(a), K.pw(b)) == 0)
    return exact, len(cand)


def holds(i, which, a, b):
    K = Cubic(i)
    return det3(K.red(Rpoly(i, which)), K.pw(a), K.pw(b)) == 0


# ======================= U：纤维 1、2
t = time.time()
solU1, ncand = solutions(1, 'U', NU)
log('U fiber1 solutions |a|,|b|<=%d: %d (mod-p candidates %d), time %.1fs' % (NU, len(solU1), ncand, time.time() - t))
log('    ' + str(solU1))
in150 = [(a, b) for (a, b) in solU1 if abs(a) <= 150 and abs(b) <= 150]
commonU = [(a, b) for (a, b) in solU1 if holds(2, 'U', a, b)]
check('r2.U_fiber1_150', len(in150) == 14,
      'fiber-1 condition det(W~_1, x^a, x^b)=0 has exactly 14 solutions with |a|,|b|<=150 (reproduces c2a two_family_residue)')
check('r2.U_fiber1_ext', len(solU1) == 14,
      'no further fiber-1 solutions up to |a|,|b|<=%d (evidence for the c2a fiber-1 "exactly 14" conjecture)' % NU)
check('r2.U_no_common', commonU == [],
      'none of the fiber-1 solutions satisfies the fiber-2 condition => for every m>=2 no two-family x^{g1}A1(u)+x^{g2}A2(u)+L with |g_i+3m+3|<=%d' % NU)
# 控制：m=1 的 F3 两族表示：g = -7, -3 => a = g+6 = -1, b = 3 必须在纤维 1 的解里
check('r2.U_control_F3', (-1, 3) in solU1,
      'control: the genuine m=1 two-family representation F3 (g1=-7,g2=-3 -> (a,b)=(-1,3)) passes fiber 1')
t = time.time()
solU2, ncand2 = solutions(2, 'U', 400)
log('U fiber2 solutions |a|,|b|<=400: %d, time %.1fs: %s' % (len(solU2), time.time() - t, solU2[:40]))
check('r2.U_fiber2_disjoint', not (set(solU2) & set(in150 + [s for s in solU1])),
      'independently: fiber-2 solution set (|a|,|b|<=400) is disjoint from the fiber-1 solution set')

# ======================= E：纤维 1、2、3
t = time.time()
solE1, nc = solutions(1, 'E', NE)
log('E fiber1 solutions |a|,|b|<=%d: %d (includes the trivial lines a=5 or b=5), time %.1fs' % (NE, len(solE1), time.time() - t))
sporE1 = [(a, b) for (a, b) in solE1 if a != 5 and b != 5]
log('    sporadic (a,b not containing 5): %s' % sporE1)
solE12 = [(a, b) for (a, b) in solE1 if holds(2, 'E', a, b)]
log('E fibers 1&2 common: %s' % solE12)
solE123 = [(a, b) for (a, b) in solE12 if holds(3, 'E', a, b)]
check('r2.E_control_m2', (5, 8) in solE12,
      'control: E(k,2) is genuinely two-term (j=1: N=4, j=2: N=1 -> (a,b)=(5,8)); it passes fibers 1 and 2')
check('r2.E_no_common_123', solE123 == [],
      'E two-term: no (a,b), |a|,|b|<=%d, satisfies fibers 1,2,3 => E(k,m) has no two-term u-representation for ANY m>=3 with |3m+3-N_i|<=%d (covers the c2b box c in [-6,3m+6], d in [-3,2m+4] for every m)' % (NE, NE))

log('# elapsed %.1fs' % (time.time() - T0))
log('SUMMARY r2 fail=%d' % len(FAILS))
sys.exit(1 if FAILS else 0)
