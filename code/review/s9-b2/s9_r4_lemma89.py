# -*- coding: utf-8 -*-
"""s9-b2 复核 r4：用大整数精确值直接检验引理 8（模 l 的表）与引理 9（l 进导数），不导入项目代码。

精确表示：y = i*eta 是代数整数，y^3 = -i y + i^2。元素记为 (c0,c1,c2,k)，值 = (c0 + c1 y + c2 y^2)/i^k。
  eta = y/i，eta^{-1} = 1 + i eta^2 = (i + y^2)/i。基 (1,eta,eta^2) 下：pi(元素) = (c1 i, c2 i^2)/i^k。
D_i(n,b) = pi(eta^b) ∧ pi(W eta^n) 精确为有理数（分母是 i 的幂）。

  r4-cross   小范围 (n,b) 上，本表示算出的 D 与「Fraction + 基 (1,eta,eta^2)」的独立写法一致
  r4-L8      引理 8：随机 (n,b)∈[-300,300]^2（含负数），D_i(n,b) mod l 等于用周期表 (n mod P, b mod P) 查到的值
             （notes/08 的 13 个证书素数 + 配置 B 的若干素数；U 与 E）
  r4-L9      引理 9：b = P b'（b' = ±1, ±2, ±3, ±l，|b| 不超过上限），n∈[-12,12]：D/(b' l) 是 l-整的，且 ≡ E_l(n) (mod l)；
             E_l(n) ≢ 0 时 D ≠ 0。特别包括 l=3（纤维 1，P=8）与 b'<0、l | b' 的情形
  r4-E-fiber1 E 只用纤维 1、T=5040 的 l 进步骤：未解决的 n0 恰为 {2515, 5035}（≡ -5 mod 2520，因为纤维 1 的周期 lcm 是 2520）
"""
import sys
import time
import random
from fractions import Fraction as Fr
import numpy as np

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


NOTE_CERT = {
    1: [(3, 8), (11, 60), (13, 168), (29, 840), (2521, 2520)],
    2: [(7, 48), (17, 72), (19, 18), (41, 280), (71, 5040), (127, 126)],
    3: [(13, 84), (71, 70)],
}
# 配置 B（T=83160，r3 找到的、不在 notes/08 表中的素数）中抽一部分
B_CERT = {
    1: [(43, 1848), (67, 33), (199, 3960), (379, 378), (617, 616), (4621, 1540), (18481, 9240)],
    2: [(23, 264), (379, 378), (661, 660), (2377, 2376), (16633, 16632)],
    3: [(5, 20), (43, 1848), (109, 11880), (271, 270), (2311, 2310), (2971, 2970), (7561, 7560), (16633, 16632)],
}


def Wt(i, kind):
    w = [0] * (3 * i + 3)
    w[0] = 1 if kind == 'U' else 0
    for j in range(1, i + 1):
        ff = 1
        for t in range(j):
            ff *= i - t
        w[3 * j + 2] += j * ff
    return w


# ---------------- 精确：Z[y][1/i] ----------------
class Exact:
    def __init__(self, i):
        self.i = i
        self.cache = {}

    def mul(self, A, B):
        i = self.i
        a, b = A[:3], B[:3]
        c0 = a[0] * b[0]
        c1 = a[0] * b[1] + a[1] * b[0]
        c2 = a[0] * b[2] + a[1] * b[1] + a[2] * b[0]
        c3 = a[1] * b[2] + a[2] * b[1]
        c4 = a[2] * b[2]
        return (c0 + i * i * c3, c1 - i * c3 + i * i * c4, c2 - i * c4, A[3] + B[3])

    def pw(self, e):
        if e in self.cache:
            return self.cache[e]
        i = self.i
        base = (0, 1, 0, 1) if e >= 0 else (i, 0, 1, 1)
        k = abs(e)
        r = (1, 0, 0, 0)
        while k:
            if k & 1:
                r = self.mul(r, base)
            base = self.mul(base, base)
            k >>= 1
        self.cache[e] = r
        return r

    def W(self, kind):
        """Wt_i(eta)（或减 1），表示成 (c0,c1,c2,k)。"""
        i = self.i
        poly = Wt(i, kind)
        K = len(poly) - 1                    # 公分母 i^K
        acc = (0, 0, 0, 0)
        tot = [0, 0, 0]
        for d, cf in enumerate(poly):
            if cf:
                yd = self.pw(d)              # y^d / i^d
                s = i ** (K - d)
                tot = [tot[r] + cf * s * yd[r] for r in range(3)]
        return (tot[0], tot[1], tot[2], K)

    def D(self, Wel, n, b):
        """返回 (num, K)，D = num / i^K（不约分，避免对巨大整数做 gcd）。"""
        i = self.i
        v = self.pw(b)
        w = self.mul(Wel, self.pw(n))
        num = i ** 3 * (v[1] * w[2] - v[2] * w[1])
        return num, v[3] + w[3]


# ---------------- 独立写法：Fraction + 基 (1,eta,eta^2) ----------------
def D_frac(i, kind, n, b):
    q = Fr(1, i)

    def mx(v):
        return [v[2] * q, v[0] - v[2] * q, v[1]]

    def ml(a, c):
        acc = [Fr(0)] * 3
        v = list(c)
        for t in range(3):
            if a[t]:
                acc = [acc[r] + a[t] * v[r] for r in range(3)]
            v = mx(v)
        return acc

    def pw(e):
        r = [Fr(1), Fr(0), Fr(0)]
        base = [Fr(0), Fr(1), Fr(0)] if e >= 0 else [Fr(1), Fr(0), Fr(i)]
        for _ in range(abs(e)):
            r = ml(r, base)
        return r
    Wv = [Fr(0)] * 3
    for cf in reversed(Wt(i, kind)):
        Wv = mx(Wv)
        Wv[0] += cf
    v = pw(b)
    w = ml(Wv, pw(n))
    return v[1] * w[2] - v[2] * w[1]


# ---------------- 模 l 的周期表 ----------------
def mulx(v, ii, l):
    return ((v[2] * ii) % l, (v[0] - v[2] * ii) % l, v[1] % l)


def tables(i, kind, l, P):
    ii = pow(i, -1, l)
    W = (0, 0, 0)
    for cf in reversed(Wt(i, kind)):
        W = mulx(W, ii, l)
        W = ((W[0] + cf) % l, W[1], W[2])
    beta = []
    gam = []
    cur, curW = (1, 0, 0), W
    for e in range(P):
        beta.append((cur[1], cur[2]))
        gam.append((curW[1], curW[2]))
        cur = mulx(cur, ii, l)
        curW = mulx(curW, ii, l)
    assert cur == (1, 0, 0)
    return beta, gam


def mu_mod(i, l, P, ex):
    """mu = (eta^P - 1)/l 模 l，用精确的 eta^P。"""
    v = ex.pw(P)
    iP = i ** v[3]
    nums = (v[0] - iP, v[1] * i, v[2] * i * i)
    assert all(x % l == 0 for x in nums)
    inv = pow(iP % l, -1, l)
    return tuple(((x // l) % l) * inv % l for x in nums)


def modl(fr, l):
    assert fr.denominator % l != 0
    return fr.numerator * pow(fr.denominator, -1, l) % l


def vl(fr, l):
    if fr == 0:
        return 10 ** 9
    v = 0
    a, b = fr.numerator, fr.denominator
    while a % l == 0:
        a //= l
        v += 1
    while b % l == 0:
        b //= l
        v -= 1
    return v


def main():
    t0 = time.time()
    rng = random.Random(20261008)
    ex = {i: Exact(i) for i in (1, 2, 3)}
    Wel = {(i, kind): ex[i].W(kind) for i in (1, 2, 3) for kind in ('U', 'E')}

    # r4-cross
    ok = True
    cnt = 0
    for i in (1, 2, 3):
        for kind in ('U', 'E'):
            for _ in range(25):
                n = rng.randint(-15, 15)
                b = rng.randint(-15, 15)
                num, K = ex[i].D(Wel[(i, kind)], n, b)
                if Fr(num, i ** K) != D_frac(i, kind, n, b):
                    ok = False
                cnt += 1
    report('r4-cross', ok, '大整数 y 表示与 Fraction 写法给出相同的 D_i(n,b)（%d 组，|n|,|b|<=15）' % cnt)

    # r4-L8
    ok = True
    cnt = 0
    certs = [(i, l, P, src) for src, CC in (('note', NOTE_CERT), ('B', B_CERT)) for i in CC for (l, P) in CC[i]]
    for (i, l, P, src) in certs:
        for kind in ('U', 'E'):
            beta, gam = tables(i, kind, l, P)
            for _ in range(60):
                n = rng.randint(-300, 300)
                b = rng.randint(-300, 300)
                num, K = ex[i].D(Wel[(i, kind)], n, b)
                bb = beta[b % P]
                gg = gam[n % P]
                Dt = (bb[0] * gg[1] - bb[1] * gg[0]) % l
                if num % l * pow(i ** K % l, -1, l) % l != Dt:
                    ok = False
                cnt += 1
    report('r4-L8', ok, '引理 8：%d 组随机 (n,b)∈[-300,300]^2 上精确 D mod l = 周期表查值（%d 个证书素数，U 与 E）' % (cnt, len(certs)))

    # r4-L9
    ok = True
    cnt = 0
    nz_cnt = 0
    vals = []
    BMAX = 25000
    for (i, l, P, src) in certs:
        mu = mu_mod(i, l, P, ex[i])
        for kind in ('U', 'E'):
            beta, gam = tables(i, kind, l, P)
            for bp in (1, -1, 2, -2, 3, -3, l, -l):
                b = P * bp
                if abs(b) > BMAX:
                    continue
                vb = vl(Fr(bp), l)
                bp0 = bp // l ** vb
                for n in range(-12, 13):
                    num, K = ex[i].D(Wel[(i, kind)], n, b)
                    gg = gam[n % P]
                    E = (mu[1] * gg[1] - mu[2] * gg[0]) % l
                    # q = D/(b' l) = num / (i^K * b' * l)；l-整 ⇔ l^{1+vb} | num
                    lint = num % l ** (1 + vb) == 0
                    good = lint and (num // l ** (1 + vb)) % l * pow(i ** K * bp0 % l, -1, l) % l == E
                    if E != 0:
                        good = good and num != 0 and (num // l ** (1 + vb)) % l != 0   # v_l(D) = 1 + v_l(b') 恰好
                        nz_cnt += 1
                    if not good:
                        ok = False
                        vals.append((i, l, P, kind, bp, n))
                    cnt += 1
    report('r4-L9', ok, '引理 9：%d 组 (证书, b\'∈{±1,±2,±3,±l}, n∈[-12,12], U/E)，|b|<=%d：D/(b\'l) l-整且 ≡ E_l(n) (mod l)；'
           '其中 E_l(n)≢0 的 %d 组都有 D≠0 且 v_l(D)=1+v_l(b\')；失败 %s' % (cnt, BMAX, nz_cnt, vals[:10]))

    # r4-E-fiber1
    unres = []
    tabs = []
    for (l, P) in NOTE_CERT[1]:
        beta, gam = tables(1, 'E', l, P)
        mu = mu_mod(1, l, P, ex[1])
        tabs.append((l, P, gam, mu))
    for n0 in range(5040):
        if all((mu[1] * gam[n0 % P][1] - mu[2] * gam[n0 % P][0]) % l == 0 for (l, P, gam, mu) in tabs):
            unres.append(n0)
    report('r4-E-fiber1', unres == [2515, 5035], 'E 只用纤维 1（T=5040）的 l 进步骤未解决的 n0 = %s' % unres)

    print('time %.1fs' % (time.time() - t0))
    npass = sum(RES)
    print('SUMMARY s9-r4 pass=%d fail=%d' % (npass, len(RES) - npass))
    return 0 if npass == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
