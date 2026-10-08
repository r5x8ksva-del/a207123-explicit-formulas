# -*- coding: utf-8 -*-
"""s11-b6b 复核脚本 2：命题 1（一个 Phi_1）与报告 T3.3(2) / c3a 推论 4.4（两个 Phi_1）逐系数一致。

记号：a = -t/x^3，X = -t/(1-t)，Phi_1(al,be;ga;X,Y) = sum_{p,q} (al)_{p+q}(be)_p/((ga)_{p+q} p! q!) X^p Y^q。
c3a 推论 4.4：
  (未变换) F = (1/(1-x))[ 1F1(1;1-lam;a) + x^2( (1-t)^{-2} Phi_1(1,2;1-lam;X,a) - (1-t)^{-1} Phi_1(1,1;1-lam;X,a) ) ]
  (变换后) F = (e^a/(1-x))[ 1F1(-lam;1-lam;-a) + x^2( Phi_1(-lam,2;1-lam;t,-a) - Phi_1(-lam,1;1-lam;t,-a) ) ]
记 Y_be := (1-t)^{-be} Phi_1(1,be;1-lam;X,a)/(1-x)（c3a 定理 4.3：L[Y_be] = (1-t)^{-be}），Y_0 = M。
做法：固定 m，把 t^m 系数统一写成「多项式 / (x^{3m} P_m)」，只比较分子（Q[x] 中的精确恒等式，x 为未定元）。
Pochhammer 按定义逐因子展开，只用到逐因子的恒等式 i - lam = -b_i/x^3（脚本 1 的 P1-ops 已精确核对）。
  H-untr   未变换形式的 t^m 系数 = G_m = W_m/P_m（m<=MMAX）
  H-tr     变换后形式（e^a 与 Phi_1(-lam,be;1-lam;t,-a) 按定义展开，负幂相消）的 t^m 系数 = G_m
  H-one    z Xi = M - Y_1，即命题 1 等价于 F = M + (M-1/(1-t))/x - Y_1；相邻关系 x^3(Y_2-Y_1) = M - x Y_1 - 1/(1-t)
           （由此 c3a 的两个 Phi_1 化成一个：这是命题 1 的另一条推导）
  H-L      L[Y_1] = 1/(1-t)、L[Y_2] = 1/(1-t)^2（逐系数 b_m Y_m - Y_{m-1}）
  H-rev    反向检查：交换 Y_1、Y_2 的符号，或把 (1-t)^{-2} 换成 (1-t)^{-1}，都使 H-untr 失败
"""
import sys
import time
from fractions import Fraction as Fr
from math import factorial, comb

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')

MMAX = 16
RES = []


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def pmul(a, b):
    if not a or not b:
        return []
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        if u:
            for j, v in enumerate(b):
                if v:
                    r[i + j] += u * v
    return trim(r)


def pscale(a, c):
    return trim([c * u for u in a])


def xpow(k):
    return [Fr(0)] * k + [Fr(1)]


ONE = [Fr(1)]


def bpoly(i):
    return trim([Fr(1), Fr(-1), Fr(0), Fr(-i)])


def rising(a, n):
    r = 1
    for i in range(n):
        r *= (a + i)
    return r


class Level:
    """固定 m：t^m 系数统一写成 num/(x^{3m} P_m)。term(c, k, den) 表示 c * x^k / prod_{i in den} b_i。"""

    def __init__(self, m, B):
        self.m = m
        self.B = B
        self.cache = {}

    def comp(self, den):
        key = tuple(sorted(den))
        if key not in self.cache:
            r = ONE
            cnt = {}
            for i in key:
                cnt[i] = cnt.get(i, 0) + 1
            for i in range(self.m + 1):
                e = 1 - cnt.get(i, 0)
                assert e >= 0, 'denominator not dividing P_m'
                if e:
                    r = pmul(r, self.B[i])
            self.cache[key] = r
        return self.cache[key]

    def term(self, c, k, den):
        assert k + 3 * self.m >= 0
        return pscale(pmul(xpow(k + 3 * self.m), self.comp(den)), Fr(c))


def main():
    t0 = time.time()
    B = [bpoly(i) for i in range(MMAX + 3)]
    P = []
    acc = ONE
    for m in range(MMAX + 2):
        acc = pmul(acc, B[m])
        P.append(acc)
    W = [ONE]
    for m in range(1, MMAX + 2):
        W.append(padd(W[-1], pmul(pscale(xpow(2), Fr(m)), P[m - 1])))

    def G_num(m):
        return pmul(xpow(3 * m), W[m])

    def inv_poch_1ml(N):
        """1/(1-lam)_N = 1/prod_{i=1}^{N}(i-lam) = prod_{i=1}^N (-x^3/b_i)：返回 (符号, x 次数, 分母下标)。"""
        return ((-1) ** N, 3 * N, list(range(1, N + 1)))

    def Ybe(L, be, pw=None):
        """(1-t)^{-pw} Phi_1(1,be;1-lam;X,a)/(1-x) 的 t^m 系数（pw 缺省为 be）。"""
        if pw is None:
            pw = be
        m = L.m
        tot = []
        for p in range(m + 1):
            for q in range(m - p + 1):
                N = p + q
                r = m - N
                s = pw + p
                tr = (1 if r == 0 else 0) if s == 0 else comb(r + s - 1, r)
                bp = rising(be, p)
                if tr == 0 or bp == 0:
                    continue
                sg, xe, den = inv_poch_1ml(N)
                # (1)_N (be)_p/((1-lam)_N p! q!) * X^p a^q，X^p = (-1)^p t^p(1-t)^{-p}，a^q = (-1)^q x^{-3q} t^q
                c = Fr(factorial(N) * bp * sg * (-1) ** p * (-1) ** q * tr, factorial(p) * factorial(q))
                tot = padd(tot, L.term(c, xe - 3 * q, den + [0]))      # 再除以 (1-x) = b_0
        return tot

    def Mcoef(L):
        # 1F1(1;1-lam;a)/(1-x)：t^m 系数 (1)_m/((1-lam)_m m!) (-1)^m x^{-3m} / b_0
        m = L.m
        sg, xe, den = inv_poch_1ml(m)
        return L.term(Fr(sg * (-1) ** m), xe - 3 * m, den + [0])

    def untr(L, variant=None):
        x2 = xpow(2)
        Mn = Mcoef(L)
        y1 = Ybe(L, 1)
        y2 = Ybe(L, 2)
        if variant == 'swap':
            return padd(Mn, pmul(x2, padd(y1, pscale(y2, Fr(-1)))))
        if variant == 'pow':
            y2p = Ybe(L, 2, pw=1)
            return padd(Mn, pmul(x2, padd(y2p, pscale(y1, Fr(-1)))))
        return padd(Mn, pmul(x2, padd(y2, pscale(y1, Fr(-1)))))

    ok_u = True
    levels = {}
    for m in range(MMAX + 1):
        L = Level(m, B)
        levels[m] = L
        if untr(L) != G_num(m):
            ok_u = False
            print('  untr mismatch m=%d' % m)
        if Mcoef(L) != xpow(3 * m):          # M 的系数 = 1/P_m
            ok_u = False
            print('  M mismatch m=%d' % m)
    report('H-untr', ok_u, 'c3a 推论 4.4 未变换形式的 t^m 系数 = G_m（Q(x) 中精确，m<=%d）；M 的系数 = 1/P_m' % MMAX)

    def tr_form(L):
        """(e^a/(1-x))[Phi_1(-lam,0;..) + x^2(Phi_1(-lam,2;..) - Phi_1(-lam,1;..))](t, -a) 的 t^m 系数。
        e^a：t^r 系数 (-1)^r x^{-3r}/r!；(-lam)_N/(1-lam)_N = prod_{i<N}(i-lam)/prod_{i=1}^N(i-lam) = b_0/b_N（逐因子
        i - lam = -b_i/x^3）；(-a)^q = x^{-3q} t^q。"""
        m = L.m
        tot = []
        x2 = xpow(2)
        for r in range(m + 1):
            for p in range(m - r + 1):
                q = m - r - p
                N = p + q

                part0 = Fr(rising(0, p))
                part2 = Fr(rising(2, p))
                part1 = Fr(rising(1, p))
                base = Fr((-1) ** r, factorial(r) * factorial(p) * factorial(q))
                # 乘 b_0/b_N 再除以 (1-x)=b_0：净为 1/b_N
                k = -3 * r - 3 * q
                if part0:
                    tot = padd(tot, L.term(base * part0, k, [N]))
                d = part2 - part1
                if d:
                    tot = padd(tot, pmul(x2, L.term(base * d, k, [N])))
        return tot

    ok_t = True
    for m in range(MMAX + 1):
        if tr_form(levels[m]) != G_num(m):
            ok_t = False
            print('  tr mismatch m=%d' % m)
    report('H-tr', ok_t, 'c3a 推论 4.4 变换后形式（e^a 与 Phi_1(-lam,be;1-lam;t,-a) 按定义展开）的 t^m 系数 = G_m（m<=%d）' % MMAX)

    def zxi(L):
        m = L.m
        tot = []
        for j in range(m):
            n = m - 1 - j
            for k in range(n + 1):
                # z (-z)^j/j! * z^k/k! /(n+1-lam) = (-1)^{j+1} x^{-3(j+k)}/(j! k!) / b_{n+1}
                tot = padd(tot, L.term(Fr((-1) ** (j + 1), factorial(j) * factorial(k)), -3 * (j + k), [n + 1]))
        return tot

    ok_one = True
    Y1n, Y2n = {}, {}
    for m in range(MMAX + 1):
        L = levels[m]
        y1 = Ybe(L, 1)
        y2 = Ybe(L, 2)
        Y1n[m], Y2n[m] = y1, y2
        Mn = Mcoef(L)
        if zxi(L) != padd(Mn, pscale(y1, Fr(-1))):
            ok_one = False
            print('  zXi != M - Y1 at m=%d' % m)
        lhs = pmul(xpow(3), padd(y2, pscale(y1, Fr(-1))))
        rhs = padd(padd(Mn, pscale(pmul(xpow(1), y1), Fr(-1))), pscale(pmul(xpow(3 * m), P[m]), Fr(-1)))
        if lhs != rhs:
            ok_one = False
            print('  contiguity fails m=%d' % m)
        # F = M + (M - 1/(1-t))/x - Y_1：乘 x 比较
        alt_x = padd(padd(pmul(xpow(1), Mn), padd(Mn, pscale(pmul(xpow(3 * m), P[m]), Fr(-1)))),
                     pscale(pmul(xpow(1), y1), Fr(-1)))
        if alt_x != pmul(xpow(1), G_num(m)):
            ok_one = False
    report('H-one', ok_one, 'z Xi = M - Y_1；x^3(Y_2-Y_1) = M - x Y_1 - 1/(1-t)；F = M + (M-1/(1-t))/x - Y_1（m<=%d，精确）' % MMAX)

    ok_L = True
    for m in range(MMAX + 1):
        for Yn, rhs_c in ((Y1n, 1), (Y2n, m + 1)):
            lhs = pmul(B[m], Yn[m])
            if m >= 1:
                lhs = padd(lhs, pscale(pmul(pmul(xpow(3), B[m]), Yn[m - 1]), Fr(-1)))
            # b_m Y_m - Y_{m-1} = rhs_c：分母 x^{3m} P_m，b_m*num_m/(x^{3m}P_m) ... 统一乘 x^{3m} P_m：
            # b_m Y_m = b_m num_m/(x^{3m}P_m)；Y_{m-1} = num_{m-1}/(x^{3m-3}P_{m-1}) = x^3 b_m num_{m-1}/(x^{3m}P_m)
            if lhs != pscale(pmul(xpow(3 * m), P[m]), Fr(rhs_c)):
                ok_L = False
    report('H-L', ok_L, 'L[Y_1]=1/(1-t)、L[Y_2]=1/(1-t)^2 逐系数成立（m<=%d）' % MMAX)

    rev = []
    for m in (4, 7):
        L = levels[m]
        rev.append(untr(L) == G_num(m))                  # 对照
        rev.append(untr(L, 'swap') != G_num(m))
        rev.append(untr(L, 'pow') != G_num(m))
        rev.append(tr_form(L) == G_num(m))               # 对照
    report('H-rev', all(rev), '反向检查（m=4,7；第 1、4 项是未改动的对照）：交换 Y_1/Y_2 的符号、把 (1-t)^{-2} 换成 (1-t)^{-1} 都失败：%s' % rev)
    print('time %.1fs' % (time.time() - t0))
    print('SUMMARY s11-b6b humbert_compare pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
    return 0 if all(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
