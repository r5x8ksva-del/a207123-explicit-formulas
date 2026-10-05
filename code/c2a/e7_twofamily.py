# -*- coding: utf-8 -*-
"""探索 7：两族单和 x^{g1}A1(u) + x^{g2}A2(u) + Laurent 多项式 能否表示 G_m？
必要条件（留数条件）：对每个不可约 b_v（1<=v<=m），theta_v := Res_xi(G_m) * u'(xi) 必须与 xi^{g1}, xi^{g2} 在 Q(xi) 中 Q-线性相关。
本脚本对 |g1|,|g2| <= G 穷举，报告满足全部纤维条件的 (g1,g2)。"""
import os, sys, time
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c2a_lib  # noqa: F401  (把 code 目录加入 sys.path)
from polylib import P_poly, b_poly, pmul, padd, pshift, pscale, pdiv, pderiv, trim


class Field:
    def __init__(self, v):
        self.f = [Fr(-1, v), Fr(1, v), Fr(0), Fr(1)]   # monic: x^3 + x/v - 1/v  (= -b_v/v)

    def red(self, p):
        p = trim(p)
        if not p:
            return [Fr(0)] * 3
        r = [Fr(c) for c in pdiv(p, self.f)[1]]
        return r + [Fr(0)] * (3 - len(r))

    def mul(self, a, b):
        return self.red(pmul(a, b))

    def inv(self, a):
        r0, r1 = list(self.f), trim(self.red(a))
        s0, s1 = [], [Fr(1)]
        while trim(r1):
            q, r = pdiv(r0, r1)
            r0, r1 = r1, r
            s0, s1 = s1, padd(s0, pscale(pmul(q, s1), -1))
        r0 = trim(r0)
        assert len(r0) == 1
        return self.red(pscale(s0, Fr(1) / r0[0]))


def W_poly(m):
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
    return W


def det3(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0]) + a[2] * (b[0] * c[1] - b[1] * c[0]))


def irreducible_bv(v):
    # 有理根只能是 1/q（q^2(q-1)=v）；±1 不是根
    q = 2
    while q * q * (q - 1) <= v:
        if q * q * (q - 1) == v:
            return False
        q += 1
    return True


G = 45
t0 = time.time()
for m in range(1, 7):
    conds = []
    for v in range(1, m + 1):
        if not irreducible_bv(v):
            continue
        Fd = Field(v)
        xi = [Fr(0), Fr(1), Fr(0)]
        Pm = P_poly(m)
        up = Fd.mul(Fd.mul(pmul(xi, xi), [3, -2]), Fd.inv(pmul([1, -1], [1, -1])))
        theta = Fd.mul(Fd.mul(Fd.red(W_poly(m)), up), Fd.inv(Fd.red(pderiv(Pm))))
        pw = {0: [Fr(1), Fr(0), Fr(0)]}
        xinv = Fd.inv(xi)
        for g in range(1, G + 1):
            pw[g] = Fd.mul(pw[g - 1], xi)
            pw[-g] = Fd.mul(pw[-g + 1], xinv)
        conds.append((v, theta, pw))
    good_pairs = []
    good_single = []
    for g1 in range(-G, G + 1):
        # 单族：theta 与 xi^{g1} 线性相关 <=> theta = c * xi^{g1}
        if all(all(theta[i] * pw[g1][j] == theta[j] * pw[g1][i] for i in range(3) for j in range(3)) for (v, theta, pw) in conds):
            good_single.append(g1)
        for g2 in range(g1 + 1, G + 1):
            if all(det3(theta, pw[g1], pw[g2]) == 0 for (v, theta, pw) in conds):
                good_pairs.append((g1, g2))
    print('m=%d fibers=%s  single-family g passing: %s ; two-family pairs passing (|g|<=%d): %d %s' % (
        m, [c[0] for c in conds], good_single, G, len(good_pairs), good_pairs[:12]))
print('%.1fs' % (time.time() - t0))
