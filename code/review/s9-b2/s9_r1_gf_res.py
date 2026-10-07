# -*- coding: utf-8 -*-
"""s9-b2 复核 r1：母函数、u 型族的母函数、留数闭式（引理 5）。独立实现，不导入项目里的任何代码。

  r1-dp        自写 DP（按最后两项转移）与暴力枚举一致（k<=8, m<=3）
  r1-gf        G_m = W_m/P_m、E_m = (W_m-1)/P_m 的幂级数与自写 DP 一致（m<=6, k<=45）
  r1-E1        E_1 = x^2/b_1（= x^{-1} u/(1-u)），而不是 notes/08 §3 写的 x^2/(b_0 b_1)
  r1-E2        E_2 的显式两族表示：E(k,2) = sum_s (2^{s+1}-1) C(k-1-2s, s+1) + sum_s 2^{s+1} C(k-2-2s, s)（k<=60）
               ⇒ E 在 m=2 时最少恰为 2 族（单族由 T2.6(ii) 排除）
  r1-Em        一般 m：E_m = sum_j j x^{3j-3m-1} u^{m-j+1} / prod_{v=j}^m (1 - v u)（m 族表示），m<=6、k<=45
  r1-utype     sum_k C(k+c-2s, m+s+d) x^k = x^g u^{s+m+d+1}，g = -2(m+d)-c-3（逐项精确相等，k 从 -10 到 60，若干参数）
  r1-irr       b_1, b_2, b_3 无有理根（不可约）；判别式 = -i(4+27i)
  r1-WmWt      W_m ≡ Wt_i (mod b_i)（多项式带余除法，余式为 0；1<=i<=6, i<=m<=i+10）
  r1-res       引理 5：u'(eta) Res_eta G_m = (-1)^{m-i+1} Wt_i(eta) eta^{-3m-3}/(i!(m-i)! i^2)，E 同理（Wt_i - 1），
               在 Q[x]/(b_i) 中精确成立（1<=i<=6，含可约的 b_4；i<=m<=i+12）；用乘法矩阵实现
  r1-res-float 在 b_i 的复根上用数值围道积分直接算留数（不用 W/P' 公式），与闭式比较（i=1,2,3；若干 m）
"""
import sys
import time
import itertools
import cmath
from fractions import Fraction as Fr
from math import comb, factorial
import numpy as np

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def C(a, b):
    """组合约定：0<=b<=a 时为二项式系数，否则 0。"""
    if b < 0 or a < 0 or b > a:
        return 0
    return comb(a, b)


# ---------------- 定义与 DP ----------------
def good(a, b, c):
    return b == c or a >= max(b, c)


def brute(k, m):
    U = E = 0
    for h in itertools.product(range(m + 1), repeat=k):
        if all(good(h[t], h[t + 1], h[t + 2]) for t in range(k - 2)):
            U += 1
            if k >= 2 and h[-2] < h[-1]:
                E += 1
    return U, E


def dp(K, m):
    U = [0] * (K + 1)
    E = [0] * (K + 1)
    U[0] = 1
    if K >= 1:
        U[1] = m + 1
    st = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    if K >= 2:
        U[2] = len(st)
        E[2] = sum(1 for (a, b) in st if a < b)
    for k in range(3, K + 1):
        new = {}
        for (a, b), v in st.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
        st = new
        U[k] = sum(st.values())
        E[k] = sum(v for (a, b), v in st.items() if a < b)
    return U, E


# ---------------- 整系数多项式（列表，下标=次数） ----------------
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[t] if t < len(a) else 0) + (b[t] if t < len(b) else 0) for t in range(n)]


def bpol(v):
    return [1, -1, 0, -v]


def Ppol(m):
    p = [1]
    for v in range(m + 1):
        p = pmul(p, bpol(v))
    return p


def Wpol(m):
    w = [1]
    for j in range(1, m + 1):
        w = padd(w, [0, 0] + [j * c for c in Ppol(j - 1)])
    return w


def Wt(i, kind):
    w = [1 if kind == 'U' else 0]
    for j in range(1, i + 1):
        ff = 1
        for t in range(j):
            ff *= i - t
        w = padd(w, [0] * (3 * j + 2) + [j * ff])
    return w


def series(num, den, K):
    """num/den 的幂级数（den[0] = ±1 时整数运算），到 x^K。"""
    assert den[0] in (1, -1)
    num = list(num) + [0] * (K + 1)
    out = []
    for k in range(K + 1):
        v = num[k] - sum(den[j] * out[k - j] for j in range(1, min(k, len(den) - 1) + 1))
        out.append(v * den[0])
    return out


# ---------------- 检查 ----------------
def check_dp():
    ok = True
    for m in range(0, 4):
        U, E = dp(8, m)
        for k in range(0, 9):
            bu, be = brute(k, m)
            if (bu, be) != (U[k], E[k]):
                ok = False
    report('r1-dp', ok, '自写 DP 与暴力枚举一致（k<=8, m<=3）')


def check_gf():
    K = 45
    ok = True
    for m in range(0, 7):
        U, E = dp(K, m)
        sU = series(Wpol(m), Ppol(m), K)
        sE = series(padd(Wpol(m), [-1]), Ppol(m), K)
        if sU != U or sE != E:
            ok = False
    report('r1-gf', ok, 'G_m=W_m/P_m 与 E_m=(W_m-1)/P_m 的展开与自写 DP 一致（0<=m<=6, k<=45）')


def check_E1_E2_Em():
    K = 60
    U1, E1 = dp(K, 1)
    s_good = series([0, 0, 1], bpol(1), K)             # x^2/b_1
    s_note = series([0, 0, 1], pmul(bpol(0), bpol(1)), K)  # x^2/(b_0 b_1)
    # x^{-1} u/(1-u) = x^{-1} sum_{s>=1} u^s ；x^{-1}u^s 的 x^k 系数 = C(k-2s+1+... ) 直接用 u 型公式
    # u^s x^g：sum_k C(k+c-2s', m+s'+d) ... 这里直接按 x^{-1} u^s = x^{3s-1} (1-x)^{-s} 展开
    s_u = [0] * (K + 1)
    for s in range(1, K + 1):
        for k in range(K + 1):
            j = k - (3 * s - 1)
            if j >= 0:
                s_u[k] += C(j + s - 1, s - 1)
    ok1 = (s_good == E1) and (s_u == E1) and (s_note != E1)
    first_diff = next(k for k in range(K + 1) if s_note[k] != E1[k])
    report('r1-E1', ok1, 'E_1 = x^2/b_1 = x^{-1}u/(1-u) 与 DP 一致（k<=60）：%s；notes/08 §3 的 x^2/(b_0 b_1) 与 DP 不一致，'
           '首个差异在 k=%d（DP %d，x^2/(b_0b_1) 给 %d）' % (s_good == E1 and s_u == E1, first_diff, E1[first_diff], s_note[first_diff]))
    # E_2 的两族表示
    U2, E2 = dp(K, 2)
    ok2 = True
    for k in range(K + 1):
        v = sum((2 ** (s + 1) - 1) * C(k - 1 - 2 * s, s + 1) for s in range(0, k + 1)) \
            + sum(2 ** (s + 1) * C(k - 2 - 2 * s, s) for s in range(0, k + 1))
        if v != E2[k]:
            ok2 = False
    report('r1-E2', ok2, 'E(k,2) = sum_s (2^{s+1}-1)C(k-1-2s,s+1) + sum_s 2^{s+1}C(k-2-2s,s) 对 0<=k<=60 精确成立；'
           '两族 (c,d)=(-1,-1)、(-2,-2)，g=(-4,-1)，即 notes/08 记号下 (n,b)=(-5,3) 或 (-8,-3)')
    # 一般 m 的 m 族表示：E_m = sum_j j x^{3j-3m-1} u^{m-j+1}/prod_{v=j}^m(1-vu)
    K2 = 45
    ok3 = True
    for m in range(1, 7):
        U, E = dp(K2, m)
        tot = [0] * (K2 + 1)
        for j in range(1, m + 1):
            # 1/prod_{v=j}^m (1 - v u) = sum_s h_s(j..m) u^s
            hs = [1]
            for v in range(j, m + 1):
                # 乘 1/(1-vu)
                new = []
                acc = 0
                for s in range(K2 + 1):
                    acc = acc * v + (hs[s] if s < len(hs) else 0)
                    new.append(acc)
                hs = new
            e0 = m - j + 1
            g = 3 * j - 3 * m - 1
            for s in range(K2 + 1):
                if hs[s] == 0:
                    continue
                e = e0 + s
                # x^g u^e = x^{g+3e} (1-x)^{-e}
                base = g + 3 * e
                if base > K2:
                    break
                for k in range(max(base, 0), K2 + 1):
                    tot[k] += j * hs[s] * C(k - base + e - 1, e - 1)
        if tot != E:
            ok3 = False
    report('r1-Em', ok3, 'E_m = sum_j j x^{3j-3m-1}u^{m-j+1}/prod_{v=j}^m(1-vu)（m 族 u 型表示）与 DP 一致（1<=m<=6, k<=45）')


def check_utype():
    ok = True
    cnt = 0
    for m in range(0, 4):
        for c in range(-6, 7):
            for d in range(-4, 4):
                for s in range(-(m + d), 5):
                    if m + s + d < 0:
                        continue
                    e = s + m + d + 1
                    g = -2 * (m + d) - c - 3
                    base = g + 3 * e
                    for k in range(-10, 61):
                        lhs = C(k + c - 2 * s, m + s + d)
                        rhs = C(k - base + e - 1, e - 1) if k >= base else 0
                        if lhs != rhs:
                            ok = False
                    cnt += 1
    report('r1-utype', ok, 'sum_k C(k+c-2s,m+s+d)x^k = x^g u^{s+m+d+1}（g=-2(m+d)-c-3）逐项精确成立（%d 组参数，k=-10..60）' % cnt)


def disc_cubic(a, b, c, d):
    return b * b * c * c - 4 * a * c ** 3 - 4 * b ** 3 * d - 27 * a * a * d * d + 18 * a * b * c * d


def check_irr():
    ok = True
    info = []
    for i in (1, 2, 3):
        cands = set()
        for p in (1, -1):
            for q in range(1, i + 1):
                if i % q == 0:
                    cands.add(Fr(p, q))
        roots = [r for r in cands if 1 - r - i * r ** 3 == 0]
        D = disc_cubic(-i, 0, -1, 1)
        ok = ok and not roots and D == -i * (4 + 27 * i)
        info.append('i=%d 有理根 %s 判别式 %d' % (i, roots, D))
    # b_4 有有理根 1/2（对照）
    r4 = 1 - Fr(1, 2) - 4 * Fr(1, 8)
    ok = ok and r4 == 0
    report('r1-irr', ok, '；'.join(info) + '；对照：b_4(1/2)=0')


# ---------------- Q[x]/(b_i)：用乘法矩阵 ----------------
class Alg:
    """Q[x]/(b_i)，基 (1, x, x^2)；x 的乘法矩阵 M：x*1=x, x*x=x^2, x*x^2 = (1-x)/i。"""

    def __init__(self, i):
        self.i = i
        q = Fr(1, i)
        self.M = [[Fr(0), Fr(0), q], [Fr(1), Fr(0), -q], [Fr(0), Fr(1), Fr(0)]]

    def mulx(self, v):
        M = self.M
        return [sum(M[r][c] * v[c] for c in range(3)) for r in range(3)]

    def mat(self, a):
        """元素 a 的乘法矩阵 a0 I + a1 M + a2 M^2（按列 = a*1, a*x, a*x^2）。"""
        cols = []
        v = list(a)
        for _ in range(3):
            cols.append(v)
            v = self.mulx(v)
        return [[cols[c][r] for c in range(3)] for r in range(3)]

    def mul(self, a, b):
        A = self.mat(a)
        return [sum(A[r][c] * b[c] for c in range(3)) for r in range(3)]

    def inv(self, a):
        A = self.mat(a)
        # 解 A v = e0（高斯消元）
        Mx = [A[r][:] + [Fr(1 if r == 0 else 0)] for r in range(3)]
        for c in range(3):
            p = next(r for r in range(c, 3) if Mx[r][c] != 0)
            Mx[c], Mx[p] = Mx[p], Mx[c]
            pv = Mx[c][c]
            Mx[c] = [t / pv for t in Mx[c]]
            for r in range(3):
                if r != c and Mx[r][c] != 0:
                    f = Mx[r][c]
                    Mx[r] = [Mx[r][t] - f * Mx[c][t] for t in range(4)]
        return [Mx[r][3] for r in range(3)]

    def ev(self, poly):
        """多项式在 eta 处的值（Horner）。"""
        acc = [Fr(0), Fr(0), Fr(0)]
        for cf in reversed(poly):
            acc = self.mulx(acc)
            acc[0] += cf
        return acc

    def pw(self, e):
        base = [Fr(0), Fr(1), Fr(0)]
        if e < 0:
            base = self.inv(base)
            e = -e
        r = [Fr(1), Fr(0), Fr(0)]
        while e:
            if e & 1:
                r = self.mul(r, base)
            base = self.mul(base, base)
            e >>= 1
        return r


def polydivrem(num, den):
    """有理系数带余除法，返回余式。"""
    num = [Fr(c) for c in num]
    den = [Fr(c) for c in den]
    while len(den) > 1 and den[-1] == 0:
        den.pop()
    while len(num) >= len(den):
        if num[-1] == 0:
            num.pop()
            continue
        f = num[-1] / den[-1]
        sh = len(num) - len(den)
        for t in range(len(den)):
            num[sh + t] -= f * den[t]
        num.pop()
    return num


def check_WmWt():
    ok = True
    cnt = 0
    for i in range(1, 7):
        for m in range(i, i + 11):
            r = polydivrem(padd(Wpol(m), [-c for c in Wt(i, 'U')]), bpol(i))
            if any(r):
                ok = False
            cnt += 1
    report('r1-WmWt', ok, 'W_m - Wt_i 被 b_i 整除（1<=i<=6, i<=m<=i+10，共 %d 例）' % cnt)


def deriv(p):
    return [t * p[t] for t in range(1, len(p))]


def check_res():
    ok = True
    cnt = 0
    for i in range(1, 7):
        A = Alg(i)
        eta = [Fr(0), Fr(1), Fr(0)]
        one_m_eta = [Fr(1), Fr(-1), Fr(0)]
        up = A.mul(A.mul(A.mul(eta, eta), [Fr(3), Fr(-2), Fr(0)]), A.inv(A.mul(one_m_eta, one_m_eta)))
        # 另一种写法：u'(eta) = (3-2eta)/(i^2 eta^4)
        up2 = A.mul([Fr(3, i * i), Fr(-2, i * i), Fr(0)], A.pw(-4))
        if up != up2:
            ok = False
        for kind in ('U', 'E'):
            Wt_e = A.ev(Wt(i, kind))
            for m in range(i, i + 13):
                Pm = Ppol(m)
                if any(A.ev(Pm)):
                    ok = False
                Wm = Wpol(m) if kind == 'U' else padd(Wpol(m), [-1])
                res = A.mul(A.ev(Wm), A.inv(A.ev(deriv(Pm))))
                lhs = A.mul(up, res)
                const = Fr((-1) ** (m - i + 1), factorial(i) * factorial(m - i) * i * i)
                rhs = [const * t for t in A.mul(Wt_e, A.pw(-3 * m - 3))]
                if lhs != rhs:
                    ok = False
                cnt += 1
    report('r1-res', ok, '引理 5 的留数闭式在 Q[x]/(b_i) 中精确成立（1<=i<=6、i<=m<=i+12，U 与 E，共 %d 例）；'
           'u\'(eta) 两种写法一致' % cnt)


def peval(p, z):
    acc = 0j
    for cf in reversed(p):
        acc = acc * z + cf
    return acc


def check_res_float():
    ok = True
    worst = 0.0
    cnt = 0
    for i in (1, 2, 3):
        # b_i 的根：-i x^3 - x + 1 = 0
        roots = np.roots([-i, 0, -1, 1])
        for m in (i, i + 1, i + 3, i + 6):
            Pm = Ppol(m)
            # P_m 的全部根 = 各 b_v 的根（v=0..m），比直接对高次多项式求根稳定
            allroots = [1.0 + 0j] + [complex(r) for v in range(1, m + 1) for r in np.roots([-v, 0, -1, 1])]
            for kind in ('U', 'E'):
                Wm = Wpol(m) if kind == 'U' else padd(Wpol(m), [-1])
                Wt_p = Wt(i, kind)
                for eta in roots:
                    # 围道半径：到其他极点距离的 1/3
                    dmin = min(abs(eta - r) for r in allroots if abs(eta - r) > 1e-8)
                    rad = dmin / 3
                    Np = 400
                    s = 0j
                    for t in range(Np):
                        th = 2 * cmath.pi * t / Np
                        z = eta + rad * cmath.exp(1j * th)
                        s += peval(Wm, z) / peval(Pm, z) * (1j * rad * cmath.exp(1j * th))
                    res = s * (2 * cmath.pi / Np) / (2j * cmath.pi)
                    upv = eta ** 2 * (3 - 2 * eta) / (1 - eta) ** 2
                    lhs = upv * res
                    rhs = (-1) ** (m - i + 1) * peval(Wt_p, eta) * eta ** (-3 * m - 3) / (factorial(i) * factorial(m - i) * i * i)
                    err = abs(lhs - rhs) / max(abs(rhs), 1e-300)
                    worst = max(worst, err)
                    if err > 1e-8:
                        ok = False
                    cnt += 1
    report('r1-res-float', ok, '数值围道积分（400 点梯形）算出的留数乘 u\'(eta) 与闭式一致（%d 个根/参数组合，最大相对误差 %.1e）' % (cnt, worst))


def main():
    t0 = time.time()
    check_dp()
    check_gf()
    check_E1_E2_Em()
    check_utype()
    check_irr()
    check_WmWt()
    check_res()
    check_res_float()
    print('time %.1fs' % (time.time() - t0))
    npass = sum(RES)
    print('SUMMARY s9-r1 pass=%d fail=%d' % (npass, len(RES) - npass))
    return 0 if npass == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
