# -*- coding: utf-8 -*-
"""s12-b4t3：引理 3.1 的第二份、互不依赖的证书——换模数 T' 与一组完全不在笔记证书表里的素数。
做法：
  1. 对一切素数 5<=l<=LMAX（l!=3），用对素数向量化的快速幂一次性算出 x^{T'} mod l（K_3 中），
     对一批 13-光滑的候选 T' 找出「x 模 l 的阶整除 T'」的素数（排除笔记的 8 个素数）；
  2. 按 sum log l - 2 log T' 排序挑候选，逐个做筛法（分块；第一个素数整块算，其余只在幸存位置上算）与 l 进步骤，
     第一个两步都成功的 T' 就是第二份证书；阶另用逐次乘法复核；mu 用模 l^2 的递推与快速幂两种办法；
  3. 负对照：在选中的证书上人为制造真解；
  4. 附带：验证笔记证书的一个更小的子集（T=3360，5 个素数）也够用（只作观察）。
不导入项目的任何模块。
"""
import os
import sys
import time
import math
from math import gcd

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_common import setup_utf8, Reporter, Wt_dict, factorize, is_prime

setup_utf8()
R = Reporter('s12-b4t3-cert2')
t00 = time.time()
I = 3
WD = Wt_dict(I)
PROJECT = {5, 13, 31, 71, 97, 193, 449, 673}
LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
TMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 45000


def lcm(a, b):
    return a // gcd(a, b) * b


# ------------------------------------------------------------------ 1. 向量化找可用素数
def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return np.nonzero(s)[0]


ps = np.array([int(p) for p in primes_upto(LMAX) if p > 3], dtype=np.int64)
Lv = ps
inv3 = np.array([pow(3, -1, int(p)) for p in ps], dtype=np.int64)


def vmul(a, b):
    a0, a1, a2 = a
    b0, b1, b2 = b
    r0 = (a0 * b0) % Lv
    r1 = (a0 * b1 + a1 * b0) % Lv
    r2 = (a0 * b2 + a1 * b1 + a2 * b0) % Lv
    r3 = (a1 * b2 + a2 * b1) % Lv
    r4 = (a2 * b2) % Lv
    t3 = (inv3 * r3) % Lv
    t4 = (inv3 * r4) % Lv
    return ((r0 + t3) % Lv, (r1 - t3 + t4) % Lv, (r2 - t4) % Lv)


ONE = (np.ones_like(Lv), np.zeros_like(Lv), np.zeros_like(Lv))
X = (np.zeros_like(Lv), np.ones_like(Lv), np.zeros_like(Lv))


def vpow(e):
    res, base = ONE, X
    while e:
        if e & 1:
            res = vmul(res, base)
        base = vmul(base, base)
        e >>= 1
    return res


def is_one(v):
    return (v[0] == 1) & (v[1] == 0) & (v[2] == 0)


cands = set()
for a in range(0, 16):
    for b in range(0, 10):
        for c in range(0, 7):
            for d in range(0, 6):
                for e in range(0, 5):
                    for f in range(0, 5):
                        v = 2 ** a * 3 ** b * 5 ** c * 7 ** d * 11 ** e * 13 ** f
                        if 1000 <= v <= TMAX and v not in (6720, 3360):
                            cands.add(v)
cands = sorted(cands)
usable = {}
for Tc in cands:
    msk = is_one(vpow(Tc))
    usable[Tc] = [int(l) for l in ps[msk] if int(l) not in PROJECT]
print('INFO 素数 5<=l<=%d 共 %d 个；13-光滑候选 T\'（1000..%d，除 6720、3360）共 %d 个；用时 %.1fs' % (LMAX, len(ps), TMAX, len(cands), time.time() - t00), flush=True)


def order_mod(l, Tc):
    """阶：从 Tc 出发逐个素因子约化（x^{Tc}=1 已知）。"""
    P = Tc
    for q in factorize(Tc):
        while P % q == 0 and xpow_scalar(l, P // q) == (1, 0, 0):
            P //= q
    return P


def mulm(a, b, l, inv):
    r = [0] * 5
    for p in range(3):
        for q in range(3):
            r[p + q] += a[p] * b[q]
    t3, t4 = (inv * r[3]) % l, (inv * r[4]) % l
    return ((r[0] + t3) % l, (r[1] - t3 + t4) % l, (r[2] - t4) % l)


def xpow_scalar(l, e, mod=None):
    mod = mod or l
    inv = pow(3, -1, mod)
    res, base = (1, 0, 0), (0, 1, 0)
    while e:
        if e & 1:
            res = mulm(res, base, mod, inv)
        base = mulm(base, base, mod, inv)
        e >>= 1
    return res


def score(Tc):
    return sum(math.log(l) for l in usable[Tc]) - 2 * math.log(Tc)


ranked = sorted([Tc for Tc in cands if score(Tc) >= 4.0], key=lambda t: t)
print('INFO 得分>=4 的候选 %d 个，前 15 个：%s' % (len(ranked), [(t, len(usable[t]), round(score(t), 1)) for t in ranked[:15]]), flush=True)


# ------------------------------------------------------------------ 2. 表、筛法、l 进
def rec_table(l, E, mod=None):
    """x^e 的坐标（e=0..E），线性递推 x^{e+3} = (x^e - x^{e+1})/3，模 mod（默认 l）。"""
    mod = mod or l
    inv = pow(3, -1, mod)
    V = np.zeros((E + 1, 3), dtype=np.int64)
    V[0] = (1, 0, 0)
    V[1] = (0, 1, 0)
    V[2] = (0, 0, 1)
    for e in range(3, E + 1):
        V[e] = ((V[e - 3] - V[e - 2]) * inv) % mod
    return V


def make_prime_data(l, P, Wd):
    s = 0
    if min(Wd) < 0:
        s = P * ((-min(Wd)) // P + 1)
    Wd = {d + s: c for d, c in Wd.items()}
    V = rec_table(l, P + max(Wd) + 1)
    Wn = np.zeros((P, 3), dtype=np.int64)
    for d, cf in Wd.items():
        Wn = (Wn + cf * V[d:d + P]) % l
    return dict(l=l, P=P, Vb=V[:P].copy(), Wn=Wn)


def sieve(pdata, TT, chunk=None, cap=200000):
    """b0∈[1,TT) 的幸存类。第一个素数（l 最大）整块算，其余只在幸存位置上算。幸存超过 cap 时提前放弃（返回 None）。"""
    order = sorted(pdata, key=lambda d: -d['l'])
    chunk = chunk or max(1, 4_000_000 // TT)
    nidx = np.arange(TT, dtype=np.int64)
    pre = []
    for d in order:
        P, l = d['P'], d['l']
        pre.append((l, P, d['Vb'][:, 1], d['Vb'][:, 2], d['Wn'][nidx % P, 1], d['Wn'][nidx % P, 2]))
    surv = []
    for b_start in range(1, TT, chunk):
        if len(surv) > cap:
            return None
        bidx = np.arange(b_start, min(TT, b_start + chunk), dtype=np.int64)
        l, P, v1, v2, w1, w2 = pre[0]
        m = ((v1[bidx % P][:, None] * w2[None, :] - v2[bidx % P][:, None] * w1[None, :]) % l) == 0
        rr, cc = np.nonzero(m)
        bb = bidx[rr]
        nn = cc.astype(np.int64)
        for (l, P, v1, v2, w1, w2) in pre[1:]:
            if len(bb) == 0:
                break
            keep = ((v1[bb % P] * w2[nn] - v2[bb % P] * w1[nn]) % l) == 0
            bb, nn = bb[keep], nn[keep]
        surv.extend(zip(nn.tolist(), bb.tolist()))
    return surv


def rec_point_big(l, P, mod):
    """x^P 的坐标：线性递推逐项算到 P，Python 大整数模 mod（l^2 可达 1e10，numpy int64 会溢出）。"""
    inv = pow(3, -1, mod)
    a, b, c = (1, 0, 0), (0, 1, 0), (0, 0, 1)
    if P <= 2:
        return (a, b, c)[P]
    for _e in range(3, P + 1):
        nxt = tuple(((a[t] - b[t]) * inv) % mod for t in range(3))
        a, b, c = b, c, nxt
    return c


def mu_two_ways(l, P):
    a = rec_point_big(l, P, l * l)               # 递推模 l^2
    b = xpow_scalar(l, P, mod=l * l)             # 快速幂模 l^2
    ok = a == b and a[0] % l == 1 and a[1] % l == 0 and a[2] % l == 0
    mu = (((a[0] - 1) // l) % l, (a[1] // l) % l, (a[2] // l) % l)
    return ok, mu


def padic(pdata, TT, mus):
    n0 = np.arange(TT, dtype=np.int64)
    cov = {}
    for d in pdata:
        l, P = d['l'], d['P']
        mu = mus[l]
        cov[l] = ((mu[1] * d['Wn'][n0 % P, 2] - mu[2] * d['Wn'][n0 % P, 1]) % l) != 0
    union = np.zeros(TT, dtype=bool)
    for l in cov:
        union |= cov[l]
    return union, cov


chosen = None
tried = []
MAXTRY = 12
for Tc in ranked:
    if Tc > TMAX or len(tried) >= MAXTRY:
        break
    prim = usable[Tc]
    orders = {l: order_mod(l, Tc) for l in prim}
    pdata = [make_prime_data(l, orders[l], WD) for l in prim]
    t1 = time.time()
    surv = sieve(pdata, Tc)
    mus = {}
    okmu = True
    for l in prim:
        okm, mu = mu_two_ways(l, orders[l])
        okmu &= okm
        mus[l] = mu
    union, cov = padic(pdata, Tc, mus)
    nsurv = -1 if surv is None else len(surv)
    tried.append((Tc, len(prim), nsurv, int((~union).sum()), round(time.time() - t1, 1)))
    print('INFO 试 T\'=%d：素数 %s；筛法幸存 %s；l 进未解决 %d；用时 %.1fs' % (Tc, [(l, orders[l]) for l in prim],
          nsurv if nsurv >= 0 else '>上限', int((~union).sum()), time.time() - t1), flush=True)
    if surv is not None and not surv and union.all() and okmu:
        chosen = (Tc, prim, orders, pdata, mus, cov)
        break

R.check('C2-found', chosen is not None, '第二份证书：试过的 (T\', 素数个数, 筛法幸存, l 进未解决, 秒)：%s' % tried)
if chosen is None:
    R.finish()
Tc, prim, orders, pdata, mus, cov = chosen
fac = factorize(Tc)

# 阶的逐次乘法复核（递推表里首个 x^e=1 的 e）
okord = True
for l in prim:
    P = orders[l]
    V = rec_table(l, P)
    first = next((e for e in range(1, P + 1) if tuple(V[e]) == (1, 0, 0)), None)
    okord &= (first == P and Tc % P == 0 and is_prime(l) and l % 2 == 1 and l != 3 and l not in PROJECT)
R.check('C2-primes', okord, 'T\'=%d=%s；%d 个素数（与笔记的 8 个不相交），阶逐次求得并整除 T\'：%s' % (
    Tc, '*'.join('%d^%d' % (p, e) for p, e in sorted(fac.items())), len(prim), [(l, orders[l]) for l in prim]))
R.check('C2-sieve', True, 'b0∈{1..%d}、n0∈Z/%d 的 %d 个类全部被某个素数排除（幸存 0）' % (Tc - 1, Tc, Tc * (Tc - 1)))
firsthit = {}
u = np.zeros(Tc, dtype=bool)
for l in prim:
    nw = cov[l] & ~u
    if nw.any():
        firsthit[l] = int(nw.sum())
    u |= cov[l]
R.check('C2-padic', bool(u.all()), '每个 n0∈Z/%d 都有素数使 Delta_l(n0)≢0（mu 由模 l^2 的递推与快速幂两种办法一致）；首中次数 %s' % (Tc, firsthit))

# ------------------------------------------------------------------ 3. 负对照（在选中的证书上）
pdA = [make_prime_data(l, orders[l], {-7: 3, 11: -2}) for l in prim]
survA = sieve(pdA, Tc) or []
wantA = {(7, 18), ((-11) % Tc, (-18) % Tc)}
R.check('C2-plant-a', wantA <= set(survA), '人为制造 W=3x^-7-2x^11：幸存 %d 类 %s，含真解类 (7,18)、(-11,-18)：%s' % (len(survA), sorted(survA)[:10], wantA <= set(survA)))
pdB = [make_prime_data(l, orders[l], {13: 5}) for l in prim]
unB, _ = padic(pdB, Tc, mus)
unres = np.nonzero(~unB)[0].tolist()
R.check('C2-plant-b', ((-13) % Tc) in unres, '人为制造 W=5x^13：l 进步骤未解决的 n0 = %s（必须含 %d）' % (unres[:10], (-13) % Tc))

# ------------------------------------------------------------------ 4. 观察：笔记证书的子集 T=3360、{5,13,71,97,193} 也够用
sub = [(5, 20), (13, 84), (71, 70), (97, 96), (193, 96)]
okord2 = all(order_mod(l, 3360) == P for (l, P) in sub)
pd3 = [make_prime_data(l, P, WD) for (l, P) in sub]
surv3 = sieve(pd3, 3360)
mus3 = {}
for (l, P) in sub:
    _, mus3[l] = mu_two_ways(l, P)
un3, cov3 = padic(pd3, 3360, mus3)
R.check('C2-subset3360', okord2 and surv3 == [] and bool(un3.all()) and bool(cov3[193].all()),
        '观察：T=3360 只用 (5,20)(13,84)(71,70)(97,96)(193,96) 时筛法幸存 %s 类；l 进步骤只用 l=193 就覆盖全部 3360 个 n0：%s' % (len(surv3) if surv3 is not None else '>上限', bool(cov3[193].all())))

print('time %.1fs' % (time.time() - t00))
R.finish()
