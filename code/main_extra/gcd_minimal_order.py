# -*- coding: utf-8 -*-
"""G_m = W_m/P_m 是否已约分（等价：U_k(m) 关于 k 的最小线性递推阶恰为 3m+1）。

关键约化（已证明）：b_v 无重根；mod b_v 有 1-x ≡ v x^3，故 b_i ≡ (v-i) x^3，
P_{j-1} ≡ (v)_j x^{3j}（j>v 时为 0），从而对任意 m>=v：W_m ≡ W_v ≡ 1 + sum_{j=1}^v j (v)_j x^{3j+2} (mod b_v)。
所以 gcd(W_m, P_m) = 1  <=>  对所有 v<=m：gcd(W_v mod b_v, b_v) = 1（v=0 时 W(1)=1≠0）。
本脚本对 v = 1..VMAX 逐个精确检验，并直接对小 m 做整体 gcd 交叉核对。
"""
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from polylib import pgcd, P_poly, padd, pshift, pscale, b_poly


def residue_W(v):
    """W_v mod b_v，返回 [α, β, γ]（基 1, x, x^2）。"""
    inv_v = Fraction(1, v)

    def mulx(r):
        a, b, c = r
        # c x^3 ≡ c (1-x)/v
        return [c * inv_v, a - c * inv_v, b]

    acc = [Fraction(1), Fraction(0), Fraction(0)]
    # x^5 起，每次乘 x^3
    cur = [Fraction(0), Fraction(0), Fraction(1)]      # x^2
    fall = 1
    for j in range(1, v + 1):
        for _ in range(3):
            cur = mulx(cur)                            # cur = x^{3j+2}
        fall *= (v - j + 1)                            # (v)_j
        coef = j * fall
        acc = [acc[i] + coef * cur[i] for i in range(3)]
    return acc


def main(VMAX=300, MSMALL=10):
    t0 = time.time()
    bad = []
    for v in range(1, VMAX + 1):
        r = residue_W(v)
        while r and r[-1] == 0:
            r.pop()
        if not r:
            bad.append(v)
            continue
        g = pgcd(r, b_poly(v))
        if len(g) > 1:
            bad.append(v)
    print('per-factor check v=1..%d: bad =' % VMAX, bad, '(%.1fs)' % (time.time() - t0))
    # 整体交叉核对（小 m）
    ok_small = True
    for m in range(0, MSMALL + 1):
        W = [1]
        for j in range(1, m + 1):
            W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
        g = pgcd(W, P_poly(m))
        if len(g) > 1:
            ok_small = False
            print('  m=%d: nontrivial gcd' % m, g)
    print('direct gcd(W_m,P_m)=1 for m<=%d:' % MSMALL, ok_small, '(%.1fs)' % (time.time() - t0))
    return not bad and ok_small


if __name__ == '__main__':
    print('RESULT', main())
