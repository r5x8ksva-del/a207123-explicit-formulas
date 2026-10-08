# -*- coding: utf-8 -*-
"""s12-b4t3 附带检查：
  X1 负对照里多出的幸存类是不是真解：W=3x^-7-2x^11 的 6 个幸存类的代表在 K_3 中精确为零；Tr(x^9)=0；
  X2 第二份证书（T'=16640）的表用精确有理数抽查（引理 8）；
  X3 notes/13 的 q>=5：纤维 3 元素 W~_3 L_q(x^3) 在 T=6720 证书下剩 60 类的 q，看幸存类、看换成 T'=16640 证书能否判定；
     每个素数下元素是否在 F_l[x]/(b_3) 中为零（为零则该素数失效）。
不导入项目的任何模块。
"""
import os
import sys
import time
import random
from fractions import Fraction as Fr
from math import comb, factorial, gcd

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_common import setup_utf8, Reporter, KField, Wt_dict, frac_mod

setup_utf8()
R = Reporter('s12-b4t3-extra')
t00 = time.time()
K3 = KField(3)
CERT1 = (6720, [(5, 20), (13, 84), (31, 480), (71, 70), (97, 96), (193, 96), (449, 448), (673, 672)])
CERT2 = (16640, [(131, 65), (257, 256), (2081, 2080), (3329, 3328)])


def elem(poly):
    return K3.from_dict(poly)


def D_exact_poly(poly, n, b):
    xb = K3.xpow(b)
    w = K3.mul(elem(poly), K3.xpow(n))
    return xb[1] * w[2] - xb[2] * w[1]


# ---- X1
plant = {-7: 3, 11: -2}
surv6 = [(7, 18), (7, -9), (16, 9), (16, 27), (-11, -27), (-11, -18)]     # t3_cert / t3_cert2 的幸存类取小代表
zs = [D_exact_poly(plant, n, b) for (n, b) in surv6]
tr9 = sum(K3.mulmat(K3.xpow(9))[t][t] for t in range(3))
R.check('X1-plant-true', all(z == 0 for z in zs) and tr9 == 0,
        '负对照 W=3x^-7-2x^11 的 6 个幸存类的代表 %s 都是精确真解（D=0）；原因：Tr(x^9)=%s，所以 1,x^9,x^27 线性相关——两份证书都恰好只保留真解类' % (surv6, tr9))


# ---- 模 l 工具
def rec_mod(l, E, mod=None):
    mod = mod or l
    inv = pow(3, -1, mod)
    V = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
    for e in range(3, E + 1):
        a, b = V[e - 3], V[e - 2]
        V.append(tuple(((a[t] - b[t]) * inv) % mod for t in range(3)))
    return V


def tables(poly, l, P):
    s = P * ((-min(poly)) // P + 1) if min(poly) < 0 else 0
    poly = {d + s: c for d, c in poly.items()}
    V = rec_mod(l, P + max(poly) + 1)
    Wn = np.zeros((P, 3), dtype=np.int64)
    for d, cf in poly.items():
        Wn = (Wn + (cf % l) * np.array(V[d:d + P], dtype=np.int64)) % l
    return np.array(V[:P], dtype=np.int64), Wn


def mu2(l, P):
    y = rec_mod(l, P, l * l)[P]
    assert y[0] % l == 1 and y[1] % l == 0 and y[2] % l == 0
    return ((y[1] // l) % l, (y[2] // l) % l)


def run_cert(poly, cert, want_list=False):
    T, primes = cert
    nidx = np.arange(T)
    tb = {l: tables(poly, l, P) for (l, P) in primes}
    surv = []
    nsurv = 0
    chunk = max(1, 2_000_000 // T)
    order = sorted(primes, key=lambda t: -t[0])
    l0, P0 = order[0]
    Vb0, Wn0 = tb[l0]
    w1, w2 = Wn0[nidx % P0, 1], Wn0[nidx % P0, 2]
    for b0 in range(1, T, chunk):
        bidx = np.arange(b0, min(T, b0 + chunk))
        m = ((Vb0[bidx % P0, 1][:, None] * w2[None, :] - Vb0[bidx % P0, 2][:, None] * w1[None, :]) % l0) == 0
        rr, cc = np.nonzero(m)
        bb, nn = bidx[rr], cc
        for (l, P) in order[1:]:
            if len(bb) == 0:
                break
            Vb, Wn = tb[l]
            keep = ((Vb[bb % P, 1] * Wn[nn % P, 2] - Vb[bb % P, 2] * Wn[nn % P, 1]) % l) == 0
            bb, nn = bb[keep], nn[keep]
        nsurv += len(bb)
        if want_list:
            surv.extend(zip(nn.tolist(), bb.tolist()))
    cov = np.zeros(T, dtype=bool)
    for (l, P) in primes:
        Vb, Wn = tb[l]
        m = mu2(l, P)
        cov |= ((m[0] * Wn[nidx % P, 2] - m[1] * Wn[nidx % P, 1]) % l) != 0
    dead = [l for (l, P) in primes if not tb[l][1].any()]
    return nsurv, int((~cov).sum()), surv, dead


# ---- X2：第二份证书的表的精确抽查
rng = random.Random(7)
ok2 = True
W3 = Wt_dict(3)
tb2 = {l: tables(W3, l, P) for (l, P) in CERT2[1]}
for _ in range(150):
    n, b = rng.randint(-250, 250), rng.randint(-250, 250)
    D = D_exact_poly(W3, n, b)
    for (l, P) in CERT2[1]:
        Vb, Wn = tb2[l]
        ok2 &= frac_mod(D, l) == int((Vb[b % P, 1] * Wn[n % P, 2] - Vb[b % P, 2] * Wn[n % P, 1]) % l)
R.check('X2-cert2-exact', ok2, '第二份证书的周期表与精确 D_3(n,b) 模 l 一致（150 组随机 (n,b)，|n|,|b|<=250，4 个素数）')


# ---- X3：notes/13 的 q>=5，纤维 3
def cM(q, M):
    return (-1) ** (q - 1 - M) * comb(q, M + 1)


def kappa(M, i):
    return Fr((-1) ** (M - i), factorial(i) * factorial(M - i))


def fiber3_poly(q):
    L = {3 * (q - 1 - M): cM(q, M) * kappa(M, 3) for M in range(3, q)}
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


Q_UNDEC = [5, 6, 8, 12, 13, 20, 21, 27]
info = []
decided2 = []
truesol = {}
for q in Q_UNDEC:
    poly = fiber3_poly(q)
    n1, u1, s1, dead1 = run_cert(poly, CERT1, want_list=True)
    # 幸存类的小代表是否精确为零
    zero_reps = []
    for (n0, b0) in s1:
        for n in (n0, n0 - CERT1[0]):
            for b in (b0, b0 - CERT1[0]):
                if abs(n) <= 400 and abs(b) <= 400 and D_exact_poly(poly, n, b) == 0:
                    zero_reps.append((n, b))
    truesol[q] = sorted(set(zero_reps))
    n2, u2, _, dead2 = run_cert(poly, CERT2)
    if n2 == 0 and u2 == 0:
        decided2.append(q)
    info.append('q=%d：T=6720 幸存 %d、失效素数 %s、幸存类的小代表里精确真解 %s；T\'=16640 幸存 %d、l 进未解决 %d、失效素数 %s'
                % (q, n1, dead1, truesol[q][:6], n2, u2, dead2))
    print('INFO ' + info[-1], flush=True)
R.check('X3-q-undecided', all(not truesol[q] for q in Q_UNDEC),
        'T=6720 证书判不了的 q=%s：幸存类的代表都不是真解；改用第二份证书（T\'=16640）可判定的 q：%s' % (Q_UNDEC, decided2))

# ---- X4（附带，笔记注 3.2 第三条说「对 E 也可以做，本文没有做」）：E_m（以上升结尾）纤维 3 的元素 W~_3 - 1 = 3x^5(1+4x^3+6x^6)
# 第一次运行时这里写成了「E 也无解」的断言，结果 FAIL：E 的纤维 3 真的有解（t3_probeE.py）。现改为核对：
# W~_3 - 1 = 33x^8 + 27x^13（K_3 中精确），且 T'=16640 证书的幸存类恰好是这组真解 (n,b)=(-13,-5)、(-8,5) 所在的两类。
WE = {5: 1, 8: 4, 11: 6}
ident = K3.from_dict({5: 3, 8: 12, 11: 18}) == K3.from_dict({8: 33, 13: 27})
nE1, uE1, sE1, _ = run_cert(WE, CERT1, want_list=True)
nE2, uE2, sE2, _ = run_cert(WE, CERT2, want_list=True)
TT2 = CERT2[0]
wantE = {((-13) % TT2, (-5) % TT2), ((-8) % TT2, 5)}
R.check('X4-E-fiber3', ident and set(sE2) == wantE and D_exact_poly(WE, -13, -5) == 0 and D_exact_poly(WE, -8, 5) == 0,
        '附带（超出范围）：E 的纤维 3 元素 W~_3-1 = 33x^8+27x^13（K_3 中精确：%s），所以 E 的纤维 3 有两原子解；T\'=16640 证书的幸存类 %s 恰为真解 (-13,-5)、(-8,5) 所在的类'
        '（T=6720 证书幸存 %d 类）——筛法保留了自然出现的真解，没有误删' % (ident, sorted(sE2), nE1))

print('time %.1fs' % (time.time() - t00))
R.finish()
