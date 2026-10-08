# -*- coding: utf-8 -*-
"""s12-b4t3 探查（附带，超出复核范围）：E 的纤维 3 元素 W~_3 - 1 在两份证书下的幸存类是不是真解；
若是，构造 E_3 的「每个 i 至多两个原子」表示并对照按定义的 E 计数核对。不导入项目的任何模块。"""
import os
import sys
from fractions import Fraction as Fr
from math import factorial

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_common import setup_utf8, Reporter, KField, Wt_dict, in_span2, legal, c_seq

setup_utf8()
R = Reporter('s12-b4t3-probeE')
K3 = KField(3)
CERT1 = (6720, [(5, 20), (13, 84), (31, 480), (71, 70), (97, 96), (193, 96), (449, 448), (673, 672)])
CERT2 = (16640, [(131, 65), (257, 256), (2081, 2080), (3329, 3328)])
WE = {5: 1, 8: 4, 11: 6}           # (W~_3 - 1)/3


def rec_mod(l, E):
    inv = pow(3, -1, l)
    V = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
    for e in range(3, E + 1):
        a, b = V[e - 3], V[e - 2]
        V.append(tuple(((a[t] - b[t]) * inv) % l for t in range(3)))
    return V


def survivors(poly, cert):
    T, primes = cert
    nidx = np.arange(T)
    tb = {}
    for (l, P) in primes:
        V = rec_mod(l, P + max(poly) + 1)
        Wn = np.zeros((P, 3), dtype=np.int64)
        for d, cf in poly.items():
            Wn = (Wn + (cf % l) * np.array(V[d:d + P], dtype=np.int64)) % l
        tb[l] = (np.array(V[:P], dtype=np.int64), Wn)
    order = sorted(primes, key=lambda t: -t[0])
    l0, P0 = order[0]
    Vb0, Wn0 = tb[l0]
    w1, w2 = Wn0[nidx % P0, 1], Wn0[nidx % P0, 2]
    out = []
    chunk = max(1, 2_000_000 // T)
    for b0 in range(1, T, chunk):
        bidx = np.arange(b0, min(T, b0 + chunk))
        m = ((Vb0[bidx % P0, 1][:, None] * w2[None, :] - Vb0[bidx % P0, 2][:, None] * w1[None, :]) % l0) == 0
        rr, cc = np.nonzero(m)
        bb, nn = bidx[rr], cc
        for (l, P) in order[1:]:
            Vb, Wn = tb[l]
            keep = ((Vb[bb % P, 1] * Wn[nn % P, 2] - Vb[bb % P, 2] * Wn[nn % P, 1]) % l) == 0
            bb, nn = bb[keep], nn[keep]
        out.extend(zip(nn.tolist(), bb.tolist()))
    return out


def D_exact(poly, n, b):
    xb = K3.xpow(b)
    w = K3.mul(K3.from_dict(poly), K3.xpow(n))
    return xb[1] * w[2] - xb[2] * w[1]


s2 = survivors(WE, CERT2)
s1 = survivors(WE, CERT1)
true2 = sorted({(n, b) for (n0, b0) in s2 for n in (n0, n0 - CERT2[0]) for b in (b0, b0 - CERT2[0])
                if abs(n) <= 500 and abs(b) <= 500 and D_exact(WE, n, b) == 0})
true1 = sorted({(n, b) for (n0, b0) in s1 for n in (n0, n0 - CERT1[0]) for b in (b0, b0 - CERT1[0])
                if abs(n) <= 500 and abs(b) <= 500 and D_exact(WE, n, b) == 0})
print('INFO T\'=16640 幸存 %s；其中小代表的真解 %s' % (s2, true2))
print('INFO T=6720 幸存 %d 类；小代表的真解 %s' % (len(s1), true1))
R.check('E-true', len(true2) > 0, 'E 的纤维 3 有真解 (n,b)：%s' % true2)

# 若有真解：W_E x^n ∈ span(1, x^b)，即 W~_3 - 1 ∈ span(x^{-n}, x^{b-n})；构造 E_3 的表示并对照按定义的 E 计数
WEfull = K3.from_dict({d: 3 * c for d, c in WE.items()})          # W~_3 - 1
pairs = []
for (n, b) in true2:
    ok, co = in_span2(K3, WEfull, -n, b - n)
    if ok:
        pairs.append((-n, b - n, co))
print('INFO W~_3 - 1 ∈ span(x^a, x^a\')：%s' % pairs)


def E_count(m, K):
    """按定义：长 k、取值 {0..m}、合法、且以上升结尾（h_{k-1} < h_k）的序列数。"""
    out = [0, 0]
    if K < 2:
        return out[:K + 1]
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    out.append(sum(v for (a, b), v in cnt.items() if a < b))
    for _k in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if legal(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
        cnt = new
        out.append(sum(v for (a, b), v in cnt.items() if a < b))
    return out


if pairs:
    m = 3
    E3 = E_count(m, 120)
    K1, K2 = KField(1), KField(2)
    W1m1 = K1.from_dict({d: c for d, c in Wt_dict(1).items() if d > 0})     # W~_1 - 1 = x^5
    W2m1 = K2.from_dict({d: c for d, c in Wt_dict(2).items() if d > 0})     # 2x^5 + 4x^8
    cs = {i: c_seq(i, 200) for i in (1, 2, 3)}

    def cc(i, n):
        return cs[i][n] if n >= 0 else 0

    def kap(i):
        return Fr((-1) ** (m - i), factorial(i) * factorial(m - i))
    a3, a3p, (al, be) = pairs[0]
    # E_m = (W_m - 1)/P_m：x=1 处 (W_m(1)-1)/prod(-v) = 0，所以常数 gamma=0
    def rhs(k):
        s = Fr(0)
        s += kap(1) * cc(1, k + 3 * m - 5)                                   # 纤维 1：x^5，一个原子
        s += kap(2) * (2 * cc(2, k + 3 * m - 5) + 4 * cc(2, k + 3 * m - 8))  # 纤维 2：两个原子
        s += kap(3) * (al * cc(3, k + 3 * m - a3) + be * cc(3, k + 3 * m - a3p))   # 纤维 3：两个原子
        return s
    bad = [k for k in range(0, 121) if rhs(k) != E3[k]]
    R.check('E-m3-rep', all(k < 12 for k in bad),
            'E_k(3) = sum 的「每个 i 至多两个原子」表示（纤维 3 用 x^%d、x^%d，系数 %s、%s）：0<=k<=120 中不符的 k = %s（只在小 k）'
            % (a3, a3p, al, be, bad))
R.finish()
