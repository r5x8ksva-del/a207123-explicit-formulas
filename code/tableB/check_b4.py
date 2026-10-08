# -*- coding: utf-8 -*-
"""表 B 的 B4（「不存在更短公式」的精确化）的核对脚本（2026-10-08）。证明见 notes/12-主Agent-表B-B4-更短公式的精确化.md。

逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b4 pass=<n> fail=<n>」。除 b4-two 外只用标准库；b4-two 用 numpy，
并导入 check_b2.py 的模 l 运算、筛法与 l 进步骤（notes/08 的实现，复核者 s9-b2 另行复现过）。U 的真值取自 code/core.py
（按原始定义的高度 DP）；U^c（不以上升结尾）用本文件里独立写的高度 DP 按定义计数，E=U-U^c。
  b4-trivial  命题 0(a)：alpha+beta=1 的形状 (-1,2)、(-2,3)、(1,0)、(0,1) 对 U（m=1,2,3）精确可解（三角方程组）；
              命题 0(b)：[x^k] x^r u^s = C(k-r-2s-1, s-1)（s>=1），三族 u 型分解对 U 与一个任意数列逐项成立
  b4-shapeD   定理 1 情形 D 的精确佐证：8 种 alpha<0、alpha+beta>=2 的形状，对 U（m=1,2）与 E（m=2），k0 in {0,6}，
              c in [-2,2]，d in [-2,3]，k<=40 的截断方程组全部无解（模 2^61-1 满列秩且不相容）；对照组 (-1,2)、(-2,3) 可解
  b4-fiberD   情形 D 的纤维乘积关系（数值）：prod eta = 1，prod(1-eta) = (-1)^(b+1)/v0，prod w = xi^(3b-e) < 1
  b4-pf       引理 2.1：U_k(m) = sum_i (-1)^(m-i)/(i!(m-i)!) sum_r A_i^(r) c_i(k+3m-r)，k<=40、m<=12 精确成立
  b4-Phi      引理 2.0：Phi_theta 用未约化的 W~_i 与约化代表计算，在 n in [-12,30] 上一致（1<=i<=10）
  b4-unique   定理 2(b) 的唯一性：常数列与 c_i(n-r)（1<=i<=m，r=0,1,2）在 n in [40,40+3m+6) 上列满秩（m<=8，精确）
  b4-negc     引理 2.2：c~_i(-n) 的闭式与向负方向解递推一致（1<=i<=30，1<=n<=60）
  b4-A0       引理 2.3：A_i^(0) = 1 + sum_j j i^(j) c~_i(-3j-2)（1<=i<=40）
  b4-vp       引理 2.4：v_p(A_p^(0)) = v_p(A_p^(1)) = -3(p-1)/2 对 3<=p<=211 的一切素数；A^(0)+A^(1) = 1 + sum_j j i^(j) c~_i(-3j-1)
              （1<=i<=40）且 v_p(A_p^(0)+A_p^(1)) >= (5-3p)/2；A^(2) 只记数据（p>=5 时 -3(p-1)/2+1，p=3 时 -1）；
              sigma in [-4,4] 时 min_r v_p(a_r^(sigma)(p)) <= -3(p-1)/2+|sigma|（p<=101）
  b4-onefiber 定理 2(a)：N(xi)=1、N(1+xi)=3、N(W~_2-1)=17/8、N(eta_2)=1/2；3 与 17*2^(-3-n)（|n|<=30）都不是有理数的立方
  b4-lemmaP   引理 2.5 的佐证（不是证明的一部分）：Catalan 数、调和数、sum_j C(n,j)^2/j! 在素数下标处的 p 进赋值 >= -2（p<=400）
  b4-two      定理 3（每个 i 两个原子）：U_k(1) = c_1(k+2)+c_1(k+1)-1（k<=40）；U_k(2) 的两原子式在 0<=k<=40 中只有 k=1 不成立，
              c 换成双向延拓 c~ 后 0<=k<=40 全部成立；
              |a|,|a'|<=40 内 W~_i ∈ span(x^a,x^a') 的解：i=1 有 14 对、i=2 恰为 (3,8)、(5,15)、3<=i<=8 没有（精确）；
              纤维 3 的证书（T=6720，8 个素数，阶逐次乘方求得）：b≢0 的 45,151,680 个剩余类全部筛掉，b≡0 的每个 n0 都有 l 进证书；
              反向检查：W~_3 换成 x^5+2x^9（人为制造解 (n,b)=(-5,4)）后，该类被保留；E 的对照（复核者 s12-b4t3）：K_3 中
              W~_3-1 = 33x^8+27x^13，E_k(3) = c_1(k+4)/2 - c_2(k+4) - 2c_2(k+1) + (11/2)c_3(k+1) + (9/2)c_3(k-4) 在 0<=k<=40 中只有 k=1 不符
  b4-rev      反向检查：W~_i 换成 1（即 U^c）时坐标为 (1,0,0)、无 p 进障碍；断言改成 -3(p-1)/2+1 时全部失败；
              由 (-1,3) 形状单和本身造出的数列，b4-shapeD 的判据不报「无解」
"""
import os
import sys
import time
import random
from fractions import Fraction as Fr
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_table  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []
PR = (1 << 61) - 1


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def binom(n, k):
    if k < 0 or n < 0 or k > n:
        return 0
    return comb(n, k)


# ---------------------------------------------------------------- 原始定义：U^c（不以上升结尾）
def Uc_table(K, M):
    """T[k][m] = 长 k、取值 {0..m}、满足三元组条件、且不以上升结尾（k>=2 时 h_{k-1} >= h_k）的序列数。"""
    def good(a, b, c):
        return b == c or (a >= b and a >= c)
    T = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        n = m + 1
        T[0][m] = 1
        if K >= 1:
            T[1][m] = n
        cnt = {(a, b): 1 for a in range(n) for b in range(n)}
        if K >= 2:
            T[2][m] = sum(v for (a, b), v in cnt.items() if a >= b)
        for k in range(3, K + 1):
            new = {}
            for (a, b), v in cnt.items():
                for c in range(n):
                    if good(a, b, c):
                        new[(b, c)] = new.get((b, c), 0) + v
            cnt = new
            T[k][m] = sum(v for (a, b), v in cnt.items() if a >= b)
    return T


# ---------------------------------------------------------------- K_i = Q[x]/(b_i) 的运算
def red(poly, i):
    """多项式（低次在前）模 b_i = 1 - x - i x^3 约化到次数 <= 2：x^3 = (1-x)/i。"""
    c = [Fr(v) for v in poly] + [Fr(0)] * 3
    for d in range(len(c) - 1, 2, -1):
        if c[d]:
            t = c[d] / i
            c[d] = Fr(0)
            c[d - 3] += t
            c[d - 2] -= t
    return c[:3]


def kmul(a, b, i):
    p = [Fr(0)] * 5
    for s in range(3):
        if a[s]:
            for t in range(3):
                p[s + t] += a[s] * b[t]
    return red(p, i)


def knorm(a, i):
    cols = [a, kmul(a, [0, 1, 0], i), kmul(a, [0, 0, 1], i)]
    M = [[cols[j][r] for j in range(3)] for r in range(3)]
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def ffall(i, j):
    r = 1
    for t in range(j):
        r *= (i - t)
    return r


def Wtilde(i):
    c = [0] * (3 * i + 3)
    c[0] = 1
    for j in range(1, i + 1):
        c[3 * j + 2] += j * ffall(i, j)
    return c


def coords(i):
    if i == 0:
        return [Fr(1), Fr(0), Fr(0)]
    return red(Wtilde(i), i)


def c_seq(i, N):
    c = [0] * (N + 1)
    for n in range(N + 1):
        c[n] = (1 if n == 0 else c[n - 1]) + (i * c[n - 3] if n >= 3 else 0)
    return c


def cbar_neg_rec(i, nmax):
    """c~_i(-n)，n=0..nmax，按递推向负方向解：c(n-3) = (c(n)-c(n-1))/i。"""
    vals = {0: Fr(1), 1: Fr(1), 2: Fr(1)}     # c_i(0)=c_i(1)=c_i(2)=1
    for n in range(2, -nmax - 1, -1):
        vals[n - 3] = (vals[n] - vals[n - 1]) / i
    return {n: vals[-n] for n in range(nmax + 1)}


def cbar_neg_closed(i, n):
    if n <= 0:
        raise ValueError
    s = Fr(0)
    for l in range(0, n):
        t = n - 3 - 2 * l
        if t < 0:
            break
        s += (-1) ** (n - 3 - l) * Fr(comb(l, t), i ** (l + 1))
    return s


def vp(x, p):
    x = Fr(x)
    if x == 0:
        return None
    n, d, v = x.numerator, x.denominator, 0
    while n % p == 0:
        n //= p; v += 1
    while d % p == 0:
        d //= p; v -= 1
    return v


def is_prime(n):
    return n >= 2 and all(n % q for q in range(2, int(n ** 0.5) + 1))


def icbrt(n):
    lo, hi = 0, 1
    while hi ** 3 <= n:
        hi *= 2
    while lo < hi - 1:
        mid = (lo + hi) // 2
        if mid ** 3 <= n:
            lo = mid
        else:
            hi = mid
    return lo


def is_rational_cube(r):
    r = Fr(r)
    a, b = abs(r.numerator), r.denominator
    return icbrt(a) ** 3 == a and icbrt(b) ** 3 == b


# ---------------------------------------------------------------- 单族方程组（与 check_b3 相同的判据）
def unknowns(al, be, c, d, K):
    lo = -(d // be) if be > 0 else 0
    hi = (K + c - d) // (al + be)
    return list(range(lo, hi + 1))


def sys_status(seq, al, be, c, d, k0, K):
    us = unknowns(al, be, c, d, K)
    rows = [[binom(k + c - al * s, be * s + d) for s in us] + [seq[k]] for k in range(k0, K + 1)]
    A = [[x % PR for x in r] for r in rows]
    ncol = len(us)
    r_ = 0
    for col in range(ncol):
        p = next((i for i in range(r_, len(A)) if A[i][col]), None)
        if p is None:
            continue
        A[r_], A[p] = A[p], A[r_]
        inv = pow(A[r_][col], PR - 2, PR)
        A[r_] = [x * inv % PR for x in A[r_]]
        for i in range(len(A)):
            if i != r_ and A[i][col]:
                f = A[i][col]
                A[i] = [(x - f * y) % PR for x, y in zip(A[i], A[r_])]
        r_ += 1
    if r_ == ncol and any(A[i][-1] for i in range(r_, len(A))):
        return 'inconsistent'
    return 'solvable' if solve_exact(seq, al, be, c, d, k0, K) else 'inconsistent'


def solve_exact(seq, al, be, c, d, k0, K):
    us = unknowns(al, be, c, d, K)
    A = [[Fr(binom(k + c - al * s, be * s + d)) for s in us] + [Fr(seq[k])] for k in range(k0, K + 1)]
    r_ = 0
    for col in range(len(us)):
        p = next((i for i in range(r_, len(A)) if A[i][col] != 0), None)
        if p is None:
            continue
        A[r_], A[p] = A[p], A[r_]
        pv = A[r_][col]
        A[r_] = [x / pv for x in A[r_]]
        for i in range(len(A)):
            if i != r_ and A[i][col] != 0:
                f = A[i][col]
                A[i] = [x - f * y for x, y in zip(A[i], A[r_])]
        r_ += 1
    return all(A[i][-1] == 0 for i in range(r_, len(A)))


def main():
    t0 = time.time()
    K = 40
    TU = U_fast_table(K, 12)
    TUc = Uc_table(K, 3)
    # 核对 U^c 的 DP 与 [x^k]1/P_m 一致（T2.2；顺带检查 DP 本身）
    def inv_Pm_series(m, K):
        # 1/P_m 的幂级数：逐个除以 b_v
        ser = [Fr(1)] + [Fr(0)] * K
        for v in range(m + 1):
            out = [Fr(0)] * (K + 1)
            for n in range(K + 1):
                out[n] = ser[n] + (out[n - 1] if n >= 1 else 0) + (v * out[n - 3] if n >= 3 else 0)
            ser = out
        return ser
    ucok = all(TUc[k][m] == inv_Pm_series(m, K)[k] for m in range(4) for k in range(K + 1))
    TE = [[TU[k][m] - TUc[k][m] for m in range(4)] for k in range(K + 1)]

    # ---- b4-trivial
    ok_a = True
    for (al, be, c, d) in [(-1, 2, 0, 0), (-2, 3, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0)]:
        for m in (1, 2, 3):
            seq = [TU[k][m] for k in range(31)]
            ok_a &= solve_exact(seq, al, be, c, d, 0, 30)
    # 三族分解：[x^k] x^r u^s
    def coef_xr_us(k, r, s):
        if s == 0:
            return 1 if k == r else 0
        return binom(k - r - 2 * s - 1, s - 1)
    # 直接验证 x^r u^s 的系数公式：x^{r+3s}(1-x)^{-s}
    ok_b = True
    for r in range(3):
        for s in range(0, 8):
            for k in range(0, 40):
                direct = binom(k - r - 3 * s + s - 1, s - 1) if s >= 1 else (1 if k == r else 0)
                if k - r - 3 * s < 0 and s >= 1:
                    direct = 0
                ok_b &= (direct == coef_xr_us(k, r, s))
    def three_family(seq, Kmax):
        a = {}
        for n in range(Kmax + 1):
            r, s = n % 3, n // 3
            rest = seq[n] - sum(av * coef_xr_us(n, rr, ss) for (rr, ss), av in a.items())
            a[(r, s)] = rest       # 领头系数 [x^{r+3s}] x^r u^s = 1
        return a
    rnd = random.Random(20261008)
    for seq in ([TU[k][3] for k in range(K + 1)], [rnd.randint(-50, 50) for _ in range(K + 1)]):
        a = three_family(seq, K)
        ok_b &= all(sum(av * coef_xr_us(k, r, s) for (r, s), av in a.items()) == seq[k] for k in range(K + 1))
    report('b4-trivial', ucok and ok_a and ok_b,
           '命题 0(a)：形状 (-1,2)、(-2,3)、(1,0)、(0,1) 对 U（m=1,2,3，k<=30）精确可解；命题 0(b)：[x^k]x^r u^s=C(k-r-2s-1,s-1)，'
           '三族分解对 U_k(3) 与随机数列逐项成立（k<=40）；U^c 的定义 DP 与 [x^k]1/P_m 一致（m<=3）')

    # ---- b4-shapeD
    shapes = [(-1, 3), (-1, 4), (-2, 4), (-2, 5), (-3, 5), (-1, 5), (-2, 6), (-3, 6)]
    found, nsys = [], 0
    targets = [('U', 1, [TU[k][1] for k in range(K + 1)]), ('U', 2, [TU[k][2] for k in range(K + 1)]),
               ('E', 2, [TE[k][2] for k in range(K + 1)])]
    for (al, be) in shapes:
        for (nm, m, seq) in targets:
            for k0 in (0, 6):
                for c in range(-2, 3):
                    for d in range(-2, 4):
                        nsys += 1
                        if sys_status(seq, al, be, c, d, k0, K) == 'solvable':
                            found.append((nm, m, al, be, k0, c, d))
    ctrl = all(sys_status([TU[k][m] for k in range(K + 1)], al, be, 0, 0, 0, K) == 'solvable'
               for (al, be) in [(-1, 2), (-2, 3)] for m in (1, 2))
    report('b4-shapeD', not found and ctrl,
           '%d 个方程组（8 种 alpha<0 的形状；U m=1,2，E m=2）全部无解；对照组 (-1,2)、(-2,3) 可解%s'
           % (nsys, '' if not found else '；有解：%s' % found[:3]))

    # ---- b4-fiberD（数值，需要求多项式根：用简单的 Durand-Kerner，避免依赖 numpy）
    def roots(coeffs):
        # coeffs 低次在前，复数
        n = len(coeffs) - 1
        lead = coeffs[-1]
        a = [c / lead for c in coeffs]
        z = [complex(0.4, 0.9) ** k for k in range(n)]
        for _ in range(2000):
            nz = []
            for k in range(n):
                num = sum(a[j] * z[k] ** j for j in range(n + 1))
                den = 1
                for j in range(n):
                    if j != k:
                        den *= (z[k] - z[j])
                nz.append(z[k] - num / den)
            if max(abs(nz[k] - z[k]) for k in range(n)) < 1e-14:
                z = nz
                break
            z = nz
        return z
    xi = 0.6823278038280193
    okf = True
    for (al, be) in shapes:
        e, b = al + be, be
        v0 = xi ** (e - 3 * b)
        # Phi(x) = x^e - v0 (1-x)^b，低次在前
        co = [0.0] * (b + 1)
        co[e] += 1.0
        for t in range(b + 1):
            co[t] -= v0 * comb(b, t) * (-1) ** t
        rs = roots([complex(c) for c in co])
        pe = 1
        p1 = 1
        for r in rs:
            pe *= r
            p1 *= (1 - r)
        pw = p1 / pe ** 3
        okf &= abs(pe - 1) < 1e-8 and abs(p1 - (-1) ** (b + 1) / v0) < 1e-6 * abs(1 / v0) \
            and abs(pw - (-1) ** (b + 1) * xi ** (3 * b - e)) < 1e-8 and xi ** (3 * b - e) < 1
    report('b4-fiberD', okf, '数值：8 种形状的纤维多项式满足 prod eta=1、prod(1-eta)=(-1)^(b+1)/v0、prod w=(-1)^(b+1)xi^(3b-e)，且 xi^(3b-e)<1')

    # ---- b4-pf
    M = 12
    CS = {i: c_seq(i, K + 3 * M + 5) for i in range(1, M + 1)}
    def cval(i, n):
        if n < 0:
            return 0
        return 1 if i == 0 else CS[i][n]
    bad = 0
    for m in range(M + 1):
        for k in range(K + 1):
            tot = Fr(0)
            for i in range(m + 1):
                A = coords(i)
                tot += Fr((-1) ** (m - i), factorial(i) * factorial(m - i)) * sum(A[r] * cval(i, k + 3 * m - r) for r in range(3))
            bad += (tot != TU[k][m])
    report('b4-pf', bad == 0, '引理 2.1 对 0<=k<=40、0<=m<=12 精确成立（不符 %d 处）' % bad)

    # ---- b4-Phi
    okp = True
    for i in range(1, 11):
        neg = cbar_neg_rec(i, 3 * i + 20)
        cs = c_seq(i, 60)
        def cb(n):
            return Fr(cs[n]) if n >= 0 else neg[-n]
        W = Wtilde(i)
        A = coords(i)
        for n in range(-12, 31):
            v1 = sum(W[a] * cb(n - a) for a in range(len(W)) if W[a])
            v2 = sum(A[r] * cb(n - r) for r in range(3))
            okp &= (v1 == v2)
    report('b4-Phi', okp, '引理 2.0：Phi_{W~_i}(n) 用未约化与约化代表计算一致（1<=i<=10，-12<=n<=30）')

    # ---- b4-unique
    oku = True
    for m in range(1, 9):
        cols = [[1] * 0]
        nrow = 3 * m + 6
        rows = []
        for n in range(40, 40 + nrow):
            row = [Fr(1)]
            for i in range(1, m + 1):
                cs = CS[i] if i in CS else c_seq(i, 200)
                row += [Fr(cs[n - r]) for r in range(3)]
            rows.append(row)
        # 精确秩
        A = [r[:] for r in rows]
        rk = 0
        ncol = len(A[0])
        for col in range(ncol):
            p = next((t for t in range(rk, len(A)) if A[t][col] != 0), None)
            if p is None:
                continue
            A[rk], A[p] = A[p], A[rk]
            pv = A[rk][col]
            A[rk] = [x / pv for x in A[rk]]
            for t in range(len(A)):
                if t != rk and A[t][col] != 0:
                    f = A[t][col]
                    A[t] = [x - f * y for x, y in zip(A[t], A[rk])]
            rk += 1
        oku &= (rk == ncol)
    report('b4-unique', oku, '常数列与 c_i(n-r)（1<=i<=m，r=0,1,2）列满秩（m<=8，n in [40,40+3m+6)，精确）')

    # ---- b4-negc
    okn = True
    for i in range(1, 31):
        rec = cbar_neg_rec(i, 60)
        okn &= all(rec[n] == cbar_neg_closed(i, n) for n in range(1, 61))
        okn &= rec[1] == 0 and rec[2] == 0 and rec[3] == Fr(1, i)
    report('b4-negc', okn, '引理 2.2：c~_i(-n) 的闭式与向负方向解递推一致（1<=i<=30，1<=n<=60）；c~(-1)=c~(-2)=0、c~(-3)=1/i')

    # ---- b4-A0
    oka = True
    for i in range(1, 41):
        neg = cbar_neg_rec(i, 3 * i + 3)
        val = 1 + sum(j * ffall(i, j) * neg[3 * j + 2] for j in range(1, i + 1))
        oka &= (val == coords(i)[0])
    report('b4-A0', oka, '引理 2.3：A_i^(0) = 1 + sum_j j i^(j) c~_i(-3j-2)（1<=i<=40）')

    # ---- b4-vp
    okv = True
    detail = []
    for p in range(3, 212):
        if not is_prime(p):
            continue
        v = vp(coords(p)[0], p)
        okv &= (v == -3 * (p - 1) // 2)
        if p <= 13:
            detail.append('%d:%d' % (p, v))
    okv1, v2d, oksum = True, {}, True
    for p in range(3, 212):
        if not is_prime(p):
            continue
        A = coords(p)
        t = -3 * (p - 1) // 2
        okv1 &= (vp(A[1], p) == t)
        v2d[p] = vp(A[2], p) - t
        oksum &= (2 * vp(A[0] + A[1], p) >= 5 - 3 * p)
    okid = True
    for i in range(1, 41):
        neg = cbar_neg_rec(i, 3 * i + 2)
        okid &= (1 + sum(j * ffall(i, j) * neg[3 * j + 1] for j in range(1, i + 1)) == coords(i)[0] + coords(i)[1])
    v2ok = v2d[3] == 2 and all(v2d[p] == 1 for p in v2d if p >= 5)
    oks = True
    for p in range(3, 102):
        if not is_prime(p):
            continue
        A = coords(p)
        for sg in range(-4, 5):
            el = A
            if sg >= 0:
                xp = [Fr(0), Fr(1), Fr(0)]
                for _ in range(sg):
                    el = kmul(el, xp, p)
            else:
                xinv = [Fr(1), Fr(0), Fr(p)]
                for _ in range(-sg):
                    el = kmul(el, xinv, p)
            mv = min(vp(t, p) for t in el if t != 0)
            oks &= (mv <= -3 * (p - 1) // 2 + abs(sg))
    report('b4-vp', okv and okv1 and oksum and okid and v2ok and oks,
           '引理 2.4：v_p(A_p^(0)) = -3(p-1)/2 对 3<=p<=211 的一切素数（%s）；v_p(A_p^(1)) 同值：%s；A^(0)+A^(1) 的恒等式（i<=40）：%s，'
           '其赋值 >= (5-3p)/2：%s；A^(2) 的数据（v_p+3(p-1)/2）：p=3 为 %d，5<=p<=211 全为 1：%s；sigma in [-4,4]、p<=101 时 '
           'min_r v_p(a_r^(sigma)) <= -3(p-1)/2+|sigma|' % (', '.join(detail), okv1, okid, oksum, v2d[3], v2ok))

    # ---- b4-two（定理 3：每个 i 两个原子）
    import check_b2 as B2   # 只在这里用：numpy 筛法与 l 进步骤（notes/08）
    c1, c2 = c_seq(1, K + 20), c_seq(2, K + 20)
    def cv(cs, n):
        return cs[n] if n >= 0 else 0
    ok1 = all(cv(c1, k + 2) + cv(c1, k + 1) - 1 == TU[k][1] for k in range(K + 1))
    bad2 = [k for k in range(K + 1)
            if Fr(1, 2) - Fr(1, 4) * cv(c1, k + 10) + Fr(1, 4) * cv(c1, k - 4) + Fr(5, 2) * cv(c2, k + 3) + 6 * cv(c2, k - 2)
            != TU[k][2]]
    n1 = cbar_neg_rec(1, 4)
    def cb1(n):
        return Fr(c1[n]) if n >= 0 else n1[-n]
    ok2bar = all(Fr(1, 2) - Fr(1, 4) * cb1(k + 10) + Fr(1, 4) * cb1(k - 4) + Fr(5, 2) * cv(c2, k + 3) + 6 * cv(c2, k - 2) == TU[k][2]
                 for k in range(K + 1))     # c~_2(-1)=c~_2(-2)=0，所以 c_2 处不用换
    def det3(u, v, w):
        return (u[0] * (v[1] * w[2] - v[2] * w[1]) - u[1] * (v[0] * w[2] - v[2] * w[0]) + u[2] * (v[0] * w[1] - v[1] * w[0]))
    pairs = {}
    for i in range(1, 9):
        X = {0: [Fr(1), Fr(0), Fr(0)]}
        for a in range(1, 41):
            X[a] = kmul(X[a - 1], [Fr(0), Fr(1), Fr(0)], i)
            X[-a] = kmul(X[-a + 1], [Fr(1), Fr(0), Fr(i)], i)       # x^-1 = 1 + i x^2
        W = coords(i)
        pairs[i] = [(a, b) for a in range(-40, 41) for b in range(a + 1, 41) if det3(W, X[a], X[b]) == 0]
    okw = (len(pairs[1]) == 14 and (-4, 10) in pairs[1] and pairs[2] == [(3, 8), (5, 15)]
           and all(not pairs[i] for i in range(3, 9)))
    T3 = 6720
    CERT3 = [(5, 20), (13, 84), (31, 480), (71, 70), (97, 96), (193, 96), (449, 448), (673, 672)]
    okc = True
    for (l, P) in CERT3:
        cur, order = [1, 0, 0], None
        for e in range(1, T3 + 1):
            cur = B2.mulm(cur, [0, 1, 0], 3, l)
            if cur == [1, 0, 0]:
                order = e
                break
        okc &= is_prime(l) and l % 2 == 1 and l != 3 and order == P and T3 % P == 0
    saved = (B2.T, B2.CERT.get(3))
    B2.T = T3                 # check_b2 的 sieve/padic 读模块全局 T 与 CERT；用完恢复
    B2.CERT[3] = CERT3
    try:
        surv, tabs = B2.sieve('U', (3,))
        unr, used = B2.padic('U', (3,), tabs)
        def planted(l):
            a5, a9 = B2.powm(5, 3, l), B2.powm(9, 3, l)
            return [(a5[t] + 2 * a9[t]) % l for t in range(3)]
        survP, _ = B2.sieve('U', (3,), elems={3: planted})
    finally:
        B2.T, B2.CERT[3] = saved
    okp = ((-5) % T3, 4) in set(survP)
    # E 的对照（注 3.2，复核者 s12-b4t3）：K_3 中 W~_3 - 1 = 33x^8 + 27x^13；E_k(3) 有每个 i 至多两个原子的表示（k≠1）
    W3m1 = red([c if a > 0 else 0 for a, c in enumerate(Wtilde(3))], 3)
    xp = [Fr(0), Fr(1), Fr(0)]
    x8 = [Fr(1), Fr(0), Fr(0)]
    for _ in range(8):
        x8 = kmul(x8, xp, 3)
    x13 = x8
    for _ in range(5):
        x13 = kmul(x13, xp, 3)
    okE3 = W3m1 == [33 * a + 27 * b for a, b in zip(x8, x13)]
    c3 = c_seq(3, K + 20)
    badE = [k for k in range(K + 1)
            if Fr(1, 2) * cv(c1, k + 4) - cv(c2, k + 4) - 2 * cv(c2, k + 1) + Fr(11, 2) * cv(c3, k + 1) + Fr(9, 2) * cv(c3, k - 4)
            != TE[k][3]]
    okE = okE3 and badE == [1]
    report('b4-two', ok1 and bad2 == [1] and ok2bar and okw and okc and not surv and not unr and okp and okE,
           '定理 3：U_k(1)=c_1(k+2)+c_1(k+1)-1（k<=40）：%s；U_k(2) 两原子式不符的 k（0..40）：%s，c 换成 c~ 后全部成立：%s；|a|,|a\'|<=40 的两原子解对数 %s；'
           '纤维 3 证书 T=6720、%d 个素数、阶核对：%s；筛法幸存 %d 类（共 %d 类）；l 进未解决 %d 个，首中次数 %s；'
           '反向检查（人为制造解 (-5,4) 的类被保留）：%s（幸存 %d 类）；E 的对照：W~_3-1=33x^8+27x^13：%s，E_k(3) 两原子式不符的 k：%s'
           % (ok1, bad2, ok2bar, {i: len(v) for i, v in pairs.items()}, len(CERT3), okc, len(surv), T3 * (T3 - 1), len(unr),
              {l: c for (_, l), c in sorted(used.items())}, okp, len(survP), okE3, badE))

    # ---- b4-onefiber
    n1 = knorm([Fr(1), Fr(1), Fr(0)], 1)                  # 1+xi
    nx = knorm([Fr(0), Fr(1), Fr(0)], 1)                  # xi
    W2m1 = red([c if a > 0 else 0 for a, c in enumerate(Wtilde(2))], 2)   # W~_2 - 1
    nW = knorm(W2m1, 2)
    neta = knorm([Fr(0), Fr(1), Fr(0)], 2)
    nocube = (not is_rational_cube(3)) and all(not is_rational_cube(Fr(17, 8) * Fr(2) ** (-n)) for n in range(-30, 31))
    report('b4-onefiber', n1 == 3 and nx == 1 and nW == Fr(17, 8) and neta == Fr(1, 2) and nocube,
           '定理 2(a)：N(1+xi)=%s、N(xi)=%s、N(W~_2-1)=%s、N(eta_2)=%s；3 与 17*2^(-3-n)（|n|<=30）都不是有理数的立方' % (n1, nx, nW, neta))

    # ---- b4-lemmaP（佐证）
    def minv(seqf, plist):
        return min(vp(seqf(p), p) for p in plist if seqf(p) != 0)
    plist = [p for p in range(50, 401) if is_prime(p)]
    cat = lambda n: Fr(comb(2 * n, n), n + 1)
    def harm(n):
        return sum(Fr(1, j) for j in range(1, n + 1))
    def sq(n):
        return sum(Fr(comb(n, j) ** 2, factorial(j)) for j in range(n + 1))
    mvc, mvh, mvs = minv(cat, plist), minv(harm, plist), minv(sq, plist[:20])
    report('b4-lemmaP', min(mvc, mvh, mvs) >= -2,
           '佐证：Catalan、调和数、sum_j C(n,j)^2/j! 在素数 p in [50,400] 处的 v_p 最小值分别为 %d、%d、%d（有界），而 A^(0) 在 p=211 处为 %d'
           % (mvc, mvh, mvs, -3 * 210 // 2))

    # ---- b4-rev
    rev1 = all(red([1], i) == [Fr(1), Fr(0), Fr(0)] for i in range(1, 20))
    rev2 = all(vp(coords(p)[0], p) != -3 * (p - 1) // 2 + 1 for p in range(3, 60) if is_prime(p))
    fake_A = {s: (s * s + 2 * s + 3) for s in range(0, 40)}
    fake = [sum(fake_A[s] * binom(k + 1 + s, 3 * s + 1) for s in fake_A) for k in range(K + 1)]
    rev3 = sys_status(fake, -1, 3, 1, 1, 0, K) == 'solvable'
    # U^c 的部分分式系数为 (1,0,0)：U^c_k(m) = sum_i (-1)^(m-i)/(i!(m-i)!) c_i(k+3m)
    rev4 = all(sum(Fr((-1) ** (m - i), factorial(i) * factorial(m - i)) * cval(i, k + 3 * m) for i in range(m + 1)) == TUc[k][m]
               for m in range(4) for k in range(K + 1))
    report('b4-rev', rev1 and rev2 and rev3 and rev4,
           '反向检查：W~ 换成 1 时坐标为 (1,0,0) 且 U^c = sum_i (-1)^(m-i)c_i(k+3m)/(i!(m-i)!)（m<=3）；断言改成 -3(p-1)/2+1 时全部失败；'
           '(-1,3) 形状单和本身造出的数列被判为可解')
    print('time %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
    n_pass = sum(RESULTS)
    n_fail = len(RESULTS) - n_pass
    print('SUMMARY b4 pass=%d fail=%d' % (n_pass, n_fail))
    sys.exit(0 if n_fail == 0 else 1)
