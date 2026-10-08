# -*- coding: utf-8 -*-
"""s11-b6b 复核脚本 1：命题 1（结构定理）的精确核对，独立实现，不导入 check_b6.py。

核对内容（x 当作未定元，Q[x] 上的多项式恒等式，不是在有理点上取值）：
  P1-closed   T1.3(1) 的 G_m = W_m/P_m：W_m 由 W_m = W_{m-1} + m x^2 P_{m-1} 递推，
              并核对 x W_m = 1 - P_m - x sum_{j<m} P_j（m<=MMAX）
  P1-dp       G_m 的 x 幂级数 = core.U_fast_table（原始定义的高度 DP）的第 m 列（k<=KMAX, m<=MDP）
  P1-ident    命题 1 的 t^m 系数：(1/P_m - 1)/x + [t^m] z Xi 乘以 x^{3(m-1)} P_m 后是多项式，
              与 x^{3(m-1)} W_m 逐项相等（Q[x] 中的恒等式，m<=MMAX）
  P1-simple   [t^m] z Xi = - sum_{j=1}^m 1/(b_j ... b_m)（审稿人推出的简式；由它 z Xi 属于 Z[[x,t]] 立得）
  P1-ops      (i) L[M]=1；(ii) L[(M-1/(1-t))/x] = gamma + t/(1-t)；(iii) L[Xi] = -x^3 t/(1-t)，
              都按 [t^m]L[Y] = b_m Y_m - Y_{m-1} 在 Q(x) 中精确核对；另核 1-x-x^3 = x^3(lam-1)、
              n+1-lam = -b_{n+1}/x^3、z/(1-lam) = -1/b_1、z-lam = x^{-2}
  P1-int      (M-1/(1-t))/x 与 z Xi 的 t^m 系数都在 Z[[x]] 中（Laurent 展开无负幂、系数为整数），k<=KMAX
  P1-phi1     Phi_1(1-lam,1;2-lam;t,zt) 的 t^N 系数 = (1-lam) e_N(z)/(N+1-lam)：
              (a) 把 lam、z 当作独立的有理数（20 组随机值）按 Pochhammer 二重和精确核对；
              (b) 在 Q(x) 中（lam=(1-x)/x^3, z=x^{-3}）核对，N<=NPHI
  P1-rev      反向检查：把 e_{m-1-j} 换成 e_{m-j}、把 b_{m-j} 换成 b_{m-j+1}、把 z Xi 的系数 z 换成 z(1+x)、
              把 -1/b_1 换成 -1/b_2，各自都应使恒等式失败
输出 PASS/FAIL 行与 SUMMARY 行。
"""
import os
import random
import sys
import time
from fractions import Fraction as Fr
from math import factorial

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_table  # noqa: E402  原始定义的真值

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')

MMAX = 22      # 多项式恒等式的 m 范围
MDP = 14       # 与 DP 对照的 m 范围
KMAX = 60      # 与 DP 对照的 x 次数
NPHI = 30

RES = []


def report(cid, ok, msg):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, msg), flush=True)


# ---------------- Q[x] 多项式（系数 Fraction，下标 = 次数） ----------------
def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def pneg(a):
    return [-c for c in a]


def psub(a, b):
    return padd(a, pneg(b))


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


def pshift_down(a, k):
    """a / x^k，要求低 k 项为 0。"""
    assert all(c == 0 for c in a[:k]), 'not divisible'
    return trim(a[k:])


def series_inv(p, n):
    """1/p 的 x 幂级数前 n+1 项（p(0)=1）。"""
    assert p[0] == 1
    inv = [Fr(0)] * (n + 1)
    inv[0] = Fr(1)
    for k in range(1, n + 1):
        s = Fr(0)
        for i in range(1, min(k, len(p) - 1) + 1):
            s += p[i] * inv[k - i]
        inv[k] = -s
    return inv


def series_mul(a, b, n):
    r = [Fr(0)] * (n + 1)
    for i in range(min(n, len(a) - 1) + 1):
        if a[i]:
            for j in range(min(n - i, len(b) - 1) + 1):
                r[i + j] += a[i] * b[j]
    return r


def b(i):
    return trim([Fr(1), Fr(-1), Fr(0), Fr(-i)])


ONE = [Fr(1)]


def prod(polys):
    r = ONE
    for p in polys:
        r = pmul(r, p)
    return r


def main():
    t0 = time.time()
    B = [b(i) for i in range(MMAX + 3)]
    P = []
    acc = ONE
    for m in range(MMAX + 2):
        acc = pmul(acc, B[m])
        P.append(acc)
    # W_m
    W = [ONE]
    for m in range(1, MMAX + 2):
        W.append(padd(W[-1], pmul(pscale(xpow(2), Fr(m)), P[m - 1])))
    ok_closed = True
    for m in range(MMAX + 1):
        lhs = pmul(xpow(1), W[m])
        rhs = psub(ONE, P[m])
        for j in range(m):
            rhs = psub(rhs, pmul(xpow(1), P[j]))
        if lhs != rhs:
            ok_closed = False
    # 递推 b_m G_m = G_{m-1} + m x^2（作为 Q(x) 中的等式：b_m W_m P_{m-1} = (W_{m-1} + m x^2 P_{m-1}) P_m）
    for m in range(1, MMAX + 1):
        lhs = pmul(pmul(B[m], W[m]), P[m - 1])
        rhs = pmul(padd(W[m - 1], pmul(pscale(xpow(2), Fr(m)), P[m - 1])), P[m])
        if lhs != rhs:
            ok_closed = False
    report('P1-closed', ok_closed, 'T1.3(1)：x W_m = 1-P_m-x sum_{j<m}P_j 与 b_m G_m = G_{m-1}+m x^2，Q[x] 中精确，m<=%d' % MMAX)

    # 与 DP 对照
    T = U_fast_table(KMAX, MDP)
    ok_dp = True
    for m in range(MDP + 1):
        g = series_mul(W[m], series_inv(P[m], KMAX), KMAX)
        if any(g[k] != T[k][m] for k in range(KMAX + 1)):
            ok_dp = False
            print('  dp mismatch m=%d' % m)
    report('P1-dp', ok_dp, 'G_m=W_m/P_m 的 x 幂级数 = U_fast_table（k<=%d, m<=%d）' % (KMAX, MDP))

    # 命题 1 的 t^m 系数
    def e_poly_in_xinv(n):
        """e_n(z) = sum_{k<=n} z^k/k!，z = x^{-3}：返回 (系数列表 c_k)，代表 sum_k c_k x^{-3k}。"""
        return [Fr(1, factorial(k)) for k in range(n + 1)]

    def zxi_numer(m):
        """x^{3(m-1)} P_m [t^m] z Xi 的多项式（m>=1）。
        [t^m] z Xi = sum_{j=0}^{m-1} (-1)^{j+1} z^j/j! * e_{m-1-j}(z) / b_{m-j}（由 z/(n+1-lam) = -1/b_{n+1}）。"""
        tot = []
        for j in range(m):
            n = m - 1 - j
            idx = m - j
            ec = e_poly_in_xinv(n)
            # z^j * e_n(z) = sum_k x^{-3(j+k)}/k!；乘 x^{3(m-1)} 后为 x^{3(m-1-j-k)}，指数 >= 0
            poly_part = []
            for k, c in enumerate(ec):
                poly_part = padd(poly_part, pscale(xpow(3 * (m - 1 - j - k)), c))
            others = prod([B[i] for i in range(m + 1) if i != idx])
            term = pmul(poly_part, others)
            sign = Fr((-1) ** (j + 1), factorial(j))
            tot = padd(tot, pscale(term, sign))
        return tot

    ok_ident = True
    ok_simple = True
    for m in range(0, MMAX + 1):
        if m == 0:
            # (1/P_0 - 1)/x = 1/(1-x) = G_0；z Xi 的 t^0 系数为 0
            ok_ident &= (W[0] == ONE)
            continue
        A = pmul(xpow(3 * (m - 1)), pshift_down(psub(ONE, P[m]), 1))   # x^{3(m-1)} P_m (1/P_m - 1)/x
        Bn = zxi_numer(m)
        lhs = padd(A, Bn)
        rhs = pmul(xpow(3 * (m - 1)), W[m])
        if lhs != rhs:
            ok_ident = False
            print('  ident mismatch m=%d' % m)
        # 简式：[t^m] z Xi = - sum_{j=1}^m 1/(b_j...b_m)，乘 P_m：- sum_j b_0...b_{j-1}
        simple = []
        for j in range(1, m + 1):
            simple = psub(simple, P[j - 1])
        if pmul(xpow(3 * (m - 1)), simple) != Bn:
            ok_simple = False
            print('  simple mismatch m=%d' % m)
    report('P1-ident', ok_ident, '命题 1：(1/P_m-1)/x + [t^m]zXi = W_m/P_m，乘 x^{3(m-1)}P_m 后 Q[x] 中逐项相等，m<=%d' % MMAX)
    report('P1-simple', ok_simple, '[t^m] z Xi = -sum_{j=1}^m 1/(b_j...b_m)（Q[x] 中精确，m<=%d）' % MMAX)

    # P1-ops：(i)-(iii)，[t^m]L[Y] = b_m Y_m - Y_{m-1}
    # 用「乘 x^{3(m-1)} P_m 后的分子」表示 [t^m] z Xi；Xi_m = x^3 [t^m] z Xi。
    # (iii) L[Xi] = -x^3 t/(1-t) <=> b_m Xi_m - Xi_{m-1} = -x^3 (m>=1), Xi_0 = 0
    #     <=> b_m Z_m - Z_{m-1} = -1，其中 Z_m = [t^m] z Xi。
    # 用 Z_m = N_m/(x^{3(m-1)} P_m) 交叉相乘：b_m N_m x^3 P_{m-1} - N_{m-1} P_m ... 统一分母 x^{3(m-1)} P_m
    ok_ops = True
    Nn = {m: zxi_numer(m) for m in range(1, MMAX + 1)}
    for m in range(1, MMAX + 1):
        # b_m Z_m = b_m N_m / (x^{3(m-1)} P_m) = N_m / (x^{3(m-1)} P_{m-1})
        # Z_{m-1} = N_{m-1}/(x^{3(m-2)} P_{m-1})（m>=2），Z_0 = 0
        # 乘 x^{3(m-1)} P_{m-1}：N_m - x^3 N_{m-1} = - x^{3(m-1)} P_{m-1}
        lhs = Nn[m] if m == 1 else psub(Nn[m], pmul(xpow(3), Nn[m - 1]))
        rhs = pneg(pmul(xpow(3 * (m - 1)), P[m - 1]))
        if lhs != rhs:
            ok_ops = False
            print('  (iii) mismatch m=%d' % m)
    # (i) L[M]=1：b_m/P_m - 1/P_{m-1} = 0 (m>=1)，b_0/P_0 = 1
    for m in range(1, MMAX + 1):
        if pmul(B[m], P[m - 1]) != P[m]:
            ok_ops = False
    # (ii) L[(M-1/(1-t))/x] = gamma + t/(1-t)：t^0 系数 (1-b_0)/x = 1；t^m 系数 (1-b_m)/x = 1 + m x^2
    if pshift_down(psub(ONE, B[0]), 1) != ONE:
        ok_ops = False
    for m in range(1, MMAX + 1):
        if pshift_down(psub(ONE, B[m]), 1) != trim([Fr(1), Fr(0), Fr(m)]):
            ok_ops = False
    # 记号恒等式（乘 x^3 后比较多项式）：lam = (1-x)/x^3, z = x^{-3}
    lam_num = trim([Fr(1), Fr(-1)])                 # x^3 lam
    # 1-x-x^3 = x^3(lam-1)  <=>  1-x-x^3 = lam_num - x^3
    ok_ops &= (trim([Fr(1), Fr(-1), Fr(0), Fr(-1)]) == psub(lam_num, xpow(3)))
    # n+1-lam = -b_{n+1}/x^3  <=>  (n+1)x^3 - lam_num = -b_{n+1}
    for n in range(0, 30):
        ok_ops &= (psub(pscale(xpow(3), Fr(n + 1)), lam_num) == pneg(B[n + 1] if n + 1 < len(B) else b(n + 1)))
    # z/(1-lam) = -1/b_1  <=>  1/(x^3 - lam_num) = -1/b_1  <=>  x^3 - lam_num = -b_1
    ok_ops &= (psub(xpow(3), lam_num) == pneg(B[1]))
    # z - lam = x^{-2}  <=>  (1 - lam_num)/x^3 = 1/x^2  <=>  1 - lam_num = x
    ok_ops &= (psub(ONE, lam_num) == xpow(1))
    report('P1-ops', ok_ops, '(i) L[M]=1；(ii) L[(M-1/(1-t))/x]=gamma+t/(1-t)；(iii) L[Xi]=-x^3t/(1-t)（m<=%d，Q(x) 中精确）；'
           '1-x-x^3=x^3(lam-1)、n+1-lam=-b_{n+1}/x^3、z/(1-lam)=-1/b_1、z-lam=x^{-2}' % MMAX)

    # P1-int：两部分的 x 展开无负幂、整系数
    ok_int = True
    for m in range(1, MDP + 1):
        A_m_series = series_mul(pshift_down(psub(ONE, P[m]), 1), series_inv(P[m], KMAX), KMAX)   # (1-P_m)/(x P_m) = (1/P_m - 1)/x
        # z Xi：N_m/(x^{3(m-1)} P_m)，N_m 的低 3(m-1) 项必须为 0
        Nm = Nn[m]
        low = 3 * (m - 1)
        if any(c != 0 for c in Nm[:low]):
            ok_int = False
            print('  negative powers in zXi m=%d' % m)
            continue
        Zs = series_mul(trim(Nm[low:]), series_inv(P[m], KMAX), KMAX)
        if not all(Fr(c).denominator == 1 for c in A_m_series + Zs):
            ok_int = False
        # 和 = G_m 的级数（再与 DP 对照一次）
        if any(A_m_series[k] + Zs[k] != T[k][m] for k in range(KMAX + 1)):
            ok_int = False
            print('  sum != DP m=%d' % m)
        # 符号：z Xi 系数非正，(M-1/(1-t))/x 系数非负
        if any(c > 0 for c in Zs) or any(c < 0 for c in A_m_series):
            ok_int = False
            print('  sign pattern fails m=%d' % m)
    report('P1-int', ok_int, '(M-1/(1-t))/x 与 z Xi 的 t^m 系数都在 Z[[x]]（无负幂、整系数，k<=%d, 1<=m<=%d），'
           '两者之和等于 U_k(m)；附带：z Xi 的系数全非正、(M-1/(1-t))/x 的全非负' % (KMAX, MDP))

    # P1-phi1
    def poch(a, n):
        r = Fr(1)
        for i in range(n):
            r *= (a + i)
        return r
    rng = random.Random(20261008)
    ok_phi = True
    for _ in range(20):
        lam = Fr(rng.randint(-40, 40), rng.randint(1, 13))
        if lam.denominator == 1:
            lam += Fr(1, 7)
        z = Fr(rng.randint(-30, 30), rng.randint(1, 11))
        for N in range(NPHI + 1):
            s = Fr(0)
            for n in range(N + 1):
                mm = N - n
                s += poch(1 - lam, N) * poch(Fr(1), mm) / (poch(2 - lam, N) * factorial(mm) * factorial(n)) * z ** n
            eN = sum(z ** k / factorial(k) for k in range(N + 1))
            if s != (1 - lam) * eN / (N + 1 - lam):
                ok_phi = False
    # 在 Q(x) 中：t^N 系数 (1-lam) e_N(z)/(N+1-lam) 乘 t e^{-zt}/(1-lam) * z 应还原 [t^m] z Xi；
    # 这里直接核对 z Xi = -(t e^{-zt}/b_1) Phi_1 的 t^m 系数（乘 x^{3(m-1)} P_m 后）与 Nn[m] 相同
    for m in range(1, min(MMAX, NPHI) + 1):
        # [t^m] -(t e^{-zt}/b_1) Phi_1 = -(1/b_1) sum_{j+N=m-1} (-z)^j/j! * c_N，c_N = (1-lam) e_N/(N+1-lam)
        # (1-lam)/(N+1-lam) = (x^3 - lam_num)/((N+1)x^3 - lam_num) = (-b_1)/(-b_{N+1}) = b_1/b_{N+1}
        # 所以 = -sum (-z)^j/j! e_N(z)/b_{N+1}，与 zxi_numer 的公式相同（再按定义重新展开一遍）
        tot = []
        for j in range(m):
            N = m - 1 - j
            ec = [Fr(1, factorial(k)) for k in range(N + 1)]
            poly_part = []
            for k, c in enumerate(ec):
                poly_part = padd(poly_part, pscale(xpow(3 * (m - 1 - j - k)), c))
            # -(1/b_1) * (-1)^j/j! * (b_1/b_{N+1}) = -(-1)^j/(j! b_{N+1})
            others = prod([B[i] for i in range(m + 1) if i != N + 1])
            tot = padd(tot, pscale(pmul(poly_part, others), Fr(-((-1) ** j), factorial(j))))
        if tot != Nn[m]:
            ok_phi = False
            print('  phi1 Q(x) mismatch m=%d' % m)
    report('P1-phi1', ok_phi, 'Phi_1(1-lam,1;2-lam;t,zt) = (1-lam)K：20 组独立的 (lam,z) 有理值、N<=%d 精确；'
           'Q(x) 中 -(t e^{-zt}/b_1)Phi_1 的 t^m 系数 = [t^m]zXi（m<=%d）' % (NPHI, min(MMAX, NPHI)))

    # 反向检查：用一般的有理函数 (num, den) 表示，交叉相乘比较，不依赖上面的规范化
    def rf_add(p, q):
        return (padd(pmul(p[0], q[1]), pmul(q[0], p[1])), pmul(p[1], q[1]))

    def zxi_rf(m, variant=None):
        tot = ([], ONE)
        for j in range(m):
            n = m - j if variant == 'e_shift' else m - 1 - j
            idx = m - j + 1 if variant == 'b_shift' else m - j
            for k in range(n + 1):
                c = Fr((-1) ** (j + 1), factorial(j) * factorial(k))
                if variant == 'z_scale':          # 整体系数 z -> z(1+x)
                    num = pscale(trim([Fr(1), Fr(1)]), c)
                else:
                    num = [c]
                term = (num, pmul(xpow(3 * (j + k)), B[idx] if idx < len(B) else b(idx)))
                tot = rf_add(tot, term)
        return tot

    def check_rf(m, zrf, b1_to_b2=False):
        A = (pshift_down(psub(ONE, P[m]), 1), P[m])           # (1/P_m - 1)/x
        if b1_to_b2:
            zrf = (pmul(zrf[0], B[1]), pmul(zrf[1], B[2]))     # -1/b_1 -> -1/b_2
        s = rf_add(A, zrf)
        return pmul(s[0], P[m]) == pmul(W[m], s[1])

    rev = []
    for m in (3, 6):
        base_ok = check_rf(m, zxi_rf(m))
        rev.append(base_ok)                                   # 未改动时应成立（对照组）
        rev.append(not check_rf(m, zxi_rf(m, 'e_shift')))
        rev.append(not check_rf(m, zxi_rf(m, 'b_shift')))
        rev.append(not check_rf(m, zxi_rf(m, 'z_scale')))
        rev.append(not check_rf(m, zxi_rf(m), b1_to_b2=True))
    report('P1-rev', all(rev), '反向检查（m=3,6；每组第 1 项是未改动的对照，应成立）：e_{m-1-j}->e_{m-j}、b_{m-j}->b_{m-j+1}、'
           'z->z(1+x)、-1/b_1->-1/b_2 都使恒等式失败：%s' % rev)

    print('time %.1fs' % (time.time() - t0))
    print('SUMMARY s11-b6b p1_exact pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
    return 0 if all(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
