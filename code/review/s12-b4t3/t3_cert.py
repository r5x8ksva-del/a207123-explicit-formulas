# -*- coding: utf-8 -*-
"""s12-b4t3：独立重算 notes/12 引理 3.1（纤维 3 的丢番图部分）的证书（T=6720，8 个素数）。
不导入项目的任何模块。与项目实现（check_b2.py：逐个 b0 的 numpy 行筛、乘 x 后约化求表、模 l^2 乘方求 mu）不同的做法：
  * x 的幂的坐标用线性递推 x^{e+3} = (x^e - x^{e+1})/i 求（模 l 与精确两种）；
  * 阶用两种办法：递推逐次求首个 x^e = 1；伴随矩阵快速幂验证 x^P = 1 且 x^{P/q} != 1；
  * 筛法用两种算法：(A) 按 lcm 逐步提升的 CRT 筛（在 (n,b) 对上逐个素数提升、过滤）；(B) 分块的整张 T x T 表；
  * mu 用精确有理数算 x^P（K_3 中）再约化到模 l^2，另用伴随矩阵模 l^2 快速幂复核；
  * 引理 8、9 在 l=5（整除判别式）等素数上用精确有理数 D_3(n,b) 直接检验；
  * |n|,|b|<=300 的精确窗口（整数化的精确算术）；数值 Vandermonde 检查 D_3 就是 det C。
"""
import os
import sys
import time
import random
from fractions import Fraction as Fr
from math import gcd

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t3_common import setup_utf8, Reporter, KField, Wt_dict, is_prime, factorize, vp_frac, vp_int, frac_mod

setup_utf8()
R = Reporter('s12-b4t3-cert')
t00 = time.time()

I = 3
T = 6720
CERT = [(5, 20), (13, 84), (31, 480), (71, 70), (97, 96), (193, 96), (449, 448), (673, 672)]
WD = Wt_dict(I)                      # {0:1, 5:3, 8:12, 11:18}
R.check('C0-W3', WD == {0: 1, 5: 3, 8: 12, 11: 18}, 'W~_3 = 1 + 3x^5 + 12x^8 + 18x^11：%s' % WD)


def lcm(a, b):
    return a // gcd(a, b) * b


# ------------------------------------------------------------------ 模 l 的坐标表（线性递推）
def xpow_mod_table(i, l, E):
    inv = pow(i, -1, l)
    v = [(1 % l, 0, 0), (0, 1 % l, 0), (0, 0, 1 % l)]
    for e in range(3, E + 1):
        a, b = v[e - 3], v[e - 2]
        v.append(tuple(((a[t] - b[t]) * inv) % l for t in range(3)))
    return v


def companion_pow(i, mod, e):
    """x^e 的坐标：伴随矩阵（乘以 x）的快速幂作用在 (1,0,0) 上，模 mod。"""
    inv = pow(i, -1, mod)
    M = [[0, 0, inv % mod], [1, 0, (-inv) % mod], [0, 1, 0]]     # 列：x*1=x，x*x=x^2，x*x^2=(1-x)/i

    def mm(A, B):
        return [[sum(A[r][k] * B[k][c] for k in range(3)) % mod for c in range(3)] for r in range(3)]
    Rm = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    B = M
    while e:
        if e & 1:
            Rm = mm(Rm, B)
        B = mm(B, B)
        e >>= 1
    return (Rm[0][0], Rm[1][0], Rm[2][0])


def build_tables(Wd, l, P):
    V = xpow_mod_table(I, l, P + max(Wd) + 1)
    WV = []
    for e in range(P):
        acc = [0, 0, 0]
        for d, cf in Wd.items():
            v = V[e + d]
            for t in range(3):
                acc[t] += cf * v[t]
        WV.append(tuple(a % l for a in acc))
    Vb = np.array([V[e] for e in range(P)], dtype=np.int64)
    Wn = np.array(WV, dtype=np.int64)
    # Z[b, n] = (D(n,b) == 0 mod l)，D = pi(x^b) ^ pi(W x^n) = Vb1*Wn2 - Vb2*Wn1
    Z = ((Vb[:, 1][:, None] * Wn[:, 2][None, :] - Vb[:, 2][:, None] * Wn[:, 1][None, :]) % l) == 0
    return V, Vb, Wn, Z


# ------------------------------------------------------------------ C1：素数与阶
info = []
okC1 = True
for (l, P) in CERT:
    V = xpow_mod_table(I, l, P)
    first = next((e for e in range(1, P + 1) if V[e] == (1, 0, 0)), None)        # 方法一：逐次（递推）
    m2 = companion_pow(I, l, P) == (1, 0, 0) and all(companion_pow(I, l, P // q) != (1, 0, 0) for q in factorize(P))
    good = is_prime(l) and l % 2 == 1 and l % I != 0 and first == P and m2 and T % P == 0
    okC1 &= good
    info.append('l=%d:P=%s/%s' % (l, first, 'ok' if m2 else 'X'))
R.check('C1-orders', okC1, '8 个 l 都是奇素数、l∤3；x 模 l 的阶（递推逐次求首个 x^e=1 / 伴随矩阵快速幂验证 x^P=1 且 x^{P/q}!=1）都等于所列 P，且 P|6720：%s' % ', '.join(info))
lcmP = 1
for (_, P) in CERT:
    lcmP = lcm(lcmP, P)
R.check('C1-lcm', lcmP == T and 255 % 5 == 0, '各 P 的 lcm = %d（= T）；l=5 整除 disc(b_3)=-255（不要求 l∤disc）' % lcmP)
# l=5 时 b_3 模 5 有重根（F_5[x]/(b_3) 不是约化环）：3x^3+x-1 与其导数 9x^2+1 的公因子
rep =[r for r in range(5) if (3 * r ** 3 + r - 1) % 5 == 0 and (9 * r * r + 1) % 5 == 0]
R.check('C1-l5-ramified', rep != [], 'b_3 模 5 的重根 x≡%s（F_5[x]/(b_3) 非约化，x 的阶 20 含因子 5）' % rep)

tabs = {}
for (l, P) in CERT:
    V, Vb, Wn, Z = build_tables(WD, l, P)
    tabs[l] = dict(P=P, V=V, Vb=Vb, Wn=Wn, Z=Z)
dens = {l: round(float(tabs[l]['Z'].mean()), 4) for (l, _) in CERT}
print('INFO 各素数模 P 的零类比例（含 b≡0 行）：%s' % dens, flush=True)

# ------------------------------------------------------------------ C2：精确的 D_3，检验引理 8、9（含 l=5）
K3 = KField(I)


def W_exact_times_xpow(n):
    acc = [Fr(0)] * 3
    for d, cf in WD.items():
        v = K3.xpow(n + d)
        for t in range(3):
            acc[t] += cf * v[t]
    return acc


def D_exact(n, b):
    xb = K3.xpow(b)
    wn = W_exact_times_xpow(n)
    return xb[1] * wn[2] - xb[2] * wn[1]


rng = random.Random(20261008)
okL8 = True
nt8 = 0
for _ in range(300):
    n, b = rng.randint(-300, 300), rng.randint(-300, 300)
    D = D_exact(n, b)
    for (l, P) in CERT:
        tb = tabs[l]
        val = int((tb['Vb'][b % P][1] * tb['Wn'][n % P][2] - tb['Vb'][b % P][2] * tb['Wn'][n % P][1]) % l)
        okL8 &= (frac_mod(D, l) == val)
        nt8 += 1
R.check('C2-lemma8', okL8, '引理 8：精确 D_3(n,b) 模 l 等于周期表在 (n mod P, b mod P) 处的值（300 组随机 (n,b)，|n|,|b|<=300，8 个素数，共 %d 次，含负数）' % nt8)

# mu：精确 x^P 约化到模 l^2；伴随矩阵模 l^2 快速幂复核
mus = {}
okmu = True
for (l, P) in CERT:
    xP = K3.xpow(P)
    a = [frac_mod(xP[t], l * l) for t in range(3)]
    okmu &= (a[0] % l == 1 and a[1] % l == 0 and a[2] % l == 0)
    mu = (((a[0] - 1) // l) % l, (a[1] // l) % l, (a[2] // l) % l)
    cp = companion_pow(I, l * l, P)
    mu2 = (((cp[0] - 1) // l) % l, (cp[1] // l) % l, (cp[2] // l) % l)
    okmu &= (mu == mu2)
    mus[l] = mu
R.check('C2-mu', okmu, 'x^P ≡ 1 (mod l)，mu=(x^P-1)/l 模 l：精确有理数法与模 l^2 快速幂一致：%s' % {l: mus[l] for l in mus})


def Delta_table(l):
    tb = tabs[l]
    m = mus[l]
    return (m[1] * tb['Wn'][:, 2] - m[2] * tb['Wn'][:, 1]) % l          # 下标 n0 mod P


DT = {l: Delta_table(l) for (l, _) in CERT}

# 引理 9：b = P b'，Delta_l(n) != 0 (mod l) 时 v_l(D) = 1 + v_l(b')；Delta ≡ 0 时 v_l(D) >= 2 + v_l(b')
okL9 = True
cnt9 = {}
for (l, P, bps, nr) in ((5, 20, (-25, -5, -3, -2, -1, 1, 2, 3, 5, 10, 25), range(-25, 26)),
                        (13, 84, (-2, -1, 1, 2, 13), range(-12, 13)),
                        (71, 70, (-1, 1, 2), range(-8, 9)),
                        (31, 480, (-1, 1), range(-4, 5))):
    hit = miss = 0
    for bp in bps:
        for n in nr:
            D = D_exact(n, P * bp)
            v = vp_frac(D, l)
            dl = int(DT[l][n % P])
            if dl != 0:
                okL9 &= (v == 1 + vp_int(abs(bp), l))
                hit += 1
            else:
                okL9 &= (v >= 2 + vp_int(abs(bp), l))
                miss += 1
    cnt9[l] = (hit, miss)
R.check('C2-lemma9', okL9, '引理 9（精确）：b=Pb\'，Delta≢0 时 v_l(D)=1+v_l(b\')、Delta≡0 时 v_l(D)>=2+v_l(b\')；(Delta≢0 次数, Delta≡0 次数)：%s（l=5 含 b\'=±5、±25，即 l|b\'）' % cnt9)

# ------------------------------------------------------------------ C3：筛法，两种算法
t1 = time.time()


def sieve_lift(tabs_, order):
    L = 1
    Sn = np.zeros(1, dtype=np.int64)
    Sb = np.zeros(1, dtype=np.int64)
    trace = []
    for (l, P) in order:
        Z = tabs_[l]['Z']
        L2 = lcm(L, P)
        f = L2 // L
        sh = np.arange(f, dtype=np.int64) * L
        outn, outb = [], []
        CH = max(1, 2_000_000 // (f * f))
        for s0 in range(0, len(Sn), CH):
            nn = Sn[s0:s0 + CH][:, None, None] + sh[None, :, None]
            bb = Sb[s0:s0 + CH][:, None, None] + sh[None, None, :]
            nn, bb = np.broadcast_arrays(nn, bb)
            nn = nn.reshape(-1)
            bb = bb.reshape(-1)
            keep = Z[bb % P, nn % P]
            outn.append(nn[keep])
            outb.append(bb[keep])
        Sn = np.concatenate(outn)
        Sb = np.concatenate(outb)
        L = L2
        trace.append((l, L, len(Sn), int(np.count_nonzero(Sb % L))))
    return L, Sn, Sb, trace


orderA = sorted(CERT, key=lambda t: (t[1], t[0]))
LA, SnA, SbA, trA = sieve_lift(tabs, orderA)
survA = sorted((int(n), int(b)) for n, b in zip(SnA, SbA) if b % LA != 0)
zeroA = sorted(int(n) for n, b in zip(SnA, SbA) if b % LA == 0)
R.check('C3-sieveA', LA == T and survA == [] and zeroA == list(range(T)),
        '(A) CRT 逐步提升（素数按 P 排序）：最终模数 %d，b≢0 的幸存类 %d 个，b≡0 的幸存类恰为全部 %d 个 n0；轨迹 (l, 模数, 幸存对数, 其中 b≢0)：%s' % (LA, len(survA), len(zeroA), trA))


def sieve_grid(tabs_, cert, TT, Wtabs=None, chunk=256):
    """(B) 分块整张表：返回 b0!=0 的幸存类列表与 b0=0 行的幸存 n0 个数。"""
    nidx = np.arange(TT)
    surv = []
    zero_row = 0
    for b_start in range(0, TT, chunk):
        bidx = np.arange(b_start, min(TT, b_start + chunk))
        alive = np.ones((len(bidx), TT), dtype=bool)
        for (l, P) in cert:
            Z = (Wtabs or tabs_)[l]['Z']
            alive &= Z[np.ix_(bidx % P, nidx % P)]
        rows, cols = np.nonzero(alive)
        for r, cidx in zip(rows, cols):
            b0 = int(bidx[r])
            if b0 == 0:
                zero_row += 1
            else:
                surv.append((int(cidx), b0))
    return surv, zero_row


survB, zrB = sieve_grid(tabs, CERT, T)
R.check('C3-sieveB', survB == [] and zrB == T,
        '(B) 分块整张 6720x6720 表：b0∈{1..6719} 的 %d 个类全部排除（幸存 %d），b0=0 行 %d 个类全部保留（D(n,0)=0，需 l 进步骤）' % (T * (T - 1), len(survB), zrB))
print('INFO 筛法用时 %.1fs' % (time.time() - t1), flush=True)

# T=5040 只用 (5,20)(13,84)(71,70) 时的幸存数（笔记说 81,360）
tabs5040 = {l: tabs[l] for l in (5, 13, 71)}
surv5040, _ = sieve_grid(tabs5040, [(5, 20), (13, 84), (71, 70)], 5040)
R.check('C3-T5040', len(surv5040) == 81360, '只用 T=5040 与 (5,20)(13,84)(71,70) 时 b0≢0 的幸存类 %d 个（笔记：81,360）' % len(surv5040))

# ------------------------------------------------------------------ C4：l 进步骤
cover = {}
for (l, P) in CERT:
    cover[l] = (DT[l][np.arange(T) % P] != 0)
union = np.zeros(T, dtype=bool)
first = {}
for (l, P) in CERT:
    newly = cover[l] & ~union
    if newly.any():
        first[l] = int(newly.sum())
    union |= cover[l]
alone = {l: int(cover[l].sum()) for (l, _) in CERT}
essential = [l for (l, _) in CERT if not np.all(np.logical_or.reduce([cover[m] for (m, _) in CERT if m != l]))]
R.check('C4-padic', bool(union.all()) and first == {5: 5040, 13: 1440, 31: 232, 71: 8},
        '每个 n0∈Z/6720 都有素数使 Delta_l(n0)≢0：%s；按所列顺序的首中次数 %s（笔记：5:5040、13:1440、31:232、71:8）；各素数单独覆盖 %s；去掉后会留缺口的素数 %s' % (bool(union.all()), first, alone, essential))

# ------------------------------------------------------------------ C5：负对照（人为制造真解）
def planted_tabs(Wd):
    out = {}
    for (l, P) in CERT:
        V, Vb, Wn, Z = build_tables(Wd, l, P)
        out[l] = dict(P=P, V=V, Vb=Vb, Wn=Wn, Z=Z)
    return out


# (a) W = 3x^{-7} - 2x^{11}：真解 (n,b)=(7,18)、(-11,-18)
Wa = {-7: 3, 11: -2}
# x^{-7} 的模 l 坐标：用 x^{-7} = x^{P-7}（x^P≡1），所以 W 的「指数」统一加上 P 的倍数
def shift_dict(Wd, P):
    s = P * ((-min(Wd)) // P + 1) if min(Wd) < 0 else 0
    return {d + s: c for d, c in Wd.items()}


tabsA = {}
for (l, P) in CERT:
    V, Vb, Wn, Z = build_tables(shift_dict(Wa, P), l, P)
    tabsA[l] = dict(P=P, V=V, Vb=Vb, Wn=Wn, Z=Z)
survPa, zrPa = sieve_grid(tabsA, CERT, T, Wtabs=tabsA)
want = {(7, 18), ((-11) % T, (-18) % T)}
R.check('C5-plant-a', want <= set(survPa), '人为制造 W=3x^-7-2x^11（真解 (7,18)、(-11,-18)）：b0≢0 幸存 %d 类 %s，含两个真解类：%s' % (len(survPa), sorted(survPa)[:12], want <= set(survPa)))
# (b) W = 5x^13：n=-13 时 W x^n = 5 是常数，对一切 b 都 D=0；筛法必须保留整行 n0=-13，l 进步骤必须在 n0=-13 失败
Wb = {13: 5}
tabsB = {}
for (l, P) in CERT:
    V, Vb, Wn, Z = build_tables(Wb, l, P)
    tabsB[l] = dict(P=P, V=V, Vb=Vb, Wn=Wn, Z=Z)
survPb, _ = sieve_grid(tabsB, CERT, T, Wtabs=tabsB)
rowb = sorted(b for (n, b) in survPb if n == (-13) % T)
unres = []
for n0 in range(T):
    if not any(((mus[l][1] * int(tabsB[l]['Wn'][n0 % P][2]) - mus[l][2] * int(tabsB[l]['Wn'][n0 % P][1])) % l) for (l, P) in CERT):
        unres.append(n0)
R.check('C5-plant-b', rowb == list(range(1, T)) and ((-13) % T) in unres,
        '人为制造 W=5x^13：n0=%d 的整行 6719 类都被保留：%s；l 进步骤未解决的 n0 = %s（必须含 %d）' % ((-13) % T, rowb == list(range(1, T)), unres[:10], (-13) % T))

# ------------------------------------------------------------------ C6：精确窗口 |n|,|b|<=300
NW = 300
lo, hi = -NW, NW + max(WD)
K3.xpow(lo)
K3.xpow(hi)
H = max(vp_int(K3.xpow(e)[t].denominator, 3) for e in range(lo, hi + 1) for t in range(3))
okden = all(K3.xpow(e)[t].denominator == 3 ** vp_int(K3.xpow(e)[t].denominator, 3) for e in range(lo, hi + 1) for t in range(3))
S = 3 ** H
XI = {e: tuple(int(K3.xpow(e)[t] * S) for t in range(3)) for e in range(lo, hi + 1)}
WI = {}
for n in range(-NW, NW + 1):
    acc = [0, 0, 0]
    for d, cf in WD.items():
        v = XI[n + d]
        for t in range(3):
            acc[t] += cf * v[t]
    WI[n] = acc
zeros = []
for b in range(-NW, NW + 1):
    if b == 0:
        continue
    xb = XI[b]
    for n in range(-NW, NW + 1):
        w = WI[n]
        if xb[1] * w[2] - xb[2] * w[1] == 0:
            zeros.append((n, b))
zero_b0 = all(XI[0][1] * WI[n][2] - XI[0][2] * WI[n][1] == 0 for n in range(-NW, NW + 1))
R.check('C6-window', okden and zeros == [] and zero_b0,
        '精确（整数化，公分母 3^%d）：|n|,|b|<=%d、b!=0 的 %d 个 (n,b) 中 D_3(n,b)=0 的有 %d 个；b=0 时恒为 0：%s；坐标分母都是 3 的幂：%s' % (H, NW, (2 * NW) * (2 * NW + 1), len(zeros), zero_b0, okden))

# ------------------------------------------------------------------ C7：数值 Vandermonde：det[(1),(eta^b),(W(eta)eta^n)] = det V * D_3(n,b)
roots = np.roots([3, 0, 1, -1])           # 3x^3 + x - 1 的根 = b_3 的根
Vd = np.linalg.det(np.array([[1, r, r * r] for r in roots]))
okV = True
worst = 0.0
for (n, b) in [(0, 1), (2, -3), (-5, 4), (7, 7), (-9, -2), (3, 11)]:
    lhs = np.linalg.det(np.array([[1, r ** b, (1 + 3 * r ** 5 + 12 * r ** 8 + 18 * r ** 11) * r ** n] for r in roots]))
    rhs = Vd * float(D_exact(n, b))
    err = abs(lhs - rhs) / max(1.0, abs(rhs))
    worst = max(worst, err)
    okV &= err < 1e-9
R.check('C7-vandermonde', okV, '数值：det[(1),(eta^b),(W~_3(eta)eta^n)]_t = det V * D_3(n,b)（6 组 (n,b)，最大相对误差 %.1e）' % worst)

print('time %.1fs' % (time.time() - t00))
R.finish()
