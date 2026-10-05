# -*- coding: utf-8 -*-
"""r-c3a 独立复核脚本 1：精确代数核对（Fraction / 整数，不 import 被复核者 c3a 的任何代码）。

思路：c3a 的恒等式都在 Q(x)[[t]] 里，每个 t^N 系数是 x 的有理函数；L_A 只含 t 方向导数，
所以在任一有理点 x0（使所有分母非零）处求值是环同态。我在多个随机有理点 x0 上把每个闭式的
t^N 系数精确算出来，与「由递推 b_m G_m = G_{m-1} + m x^2 / 由 ODE 的 t 系数递推」得到的值比较。
G_m 的 Taylor 系数另与我自己写的高度 DP（以及 core 的参考实现、原题直接计数）对照，锚定到原始定义。
"""
import os
import sys
import time
import random
from fractions import Fraction as Fr
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, CODE)
import core  # 只作为参考实现之一（只读）

T0 = time.time()
RES = []


def rep(cid, ok, desc):
    RES.append(bool(ok))
    print(('PASS' if ok else 'FAIL'), cid, desc, flush=True)


def good(a, b, c):
    return b == c or (a >= b and a >= c)


# ---------------------------------------------------------------- 定义层
def dp_col(m, K):
    """我自己的高度 DP：U_0(m..)…U_K(m)。"""
    n = m + 1
    out = [1]
    if K >= 1:
        out.append(n)
    if K >= 2:
        cnt = [[1] * n for _ in range(n)]
        out.append(n * n)
        for k in range(3, K + 1):
            new = [[0] * n for _ in range(n)]
            for a in range(n):
                row = cnt[a]
                for b in range(n):
                    v = row[b]
                    if v == 0:
                        continue
                    nb = new[b]
                    for c in range(n):
                        if b == c or (a >= b and a >= c):
                            nb[c] += v
            cnt = new
            out.append(sum(map(sum, cnt)))
    return out[:K + 1]


def my_table(K, M):
    cols = [dp_col(m, K) for m in range(M + 1)]
    return [[cols[m][k] for m in range(M + 1)] for k in range(K + 1)]


def dfs_stats(m, k):
    """枚举 {0..m}^k 合法序列：总数、不以上升结尾、以上升到 j 结尾。"""
    tot, na, asc = 0, 0, [0] * (m + 1)
    seq = []

    def rec():
        nonlocal tot, na
        if len(seq) == k:
            tot += 1
            if k <= 1 or seq[-2] >= seq[-1]:
                na += 1
            else:
                asc[seq[-1]] += 1
            return
        for v in range(m + 1):
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec()
            seq.pop()
    rec()
    return tot, na, asc


def my_N_dfs(k):
    """值域恰为 {0..q-1} 的合法词个数（我自己的 DFS）。"""
    res = [0] * (k + 1)
    if k == 0:
        res[0] = 1
        return res
    seq = []

    def rec(mx):
        if len(seq) == k:
            q = mx + 1
            if len(set(seq)) == q:
                res[q] += 1
            return
        # 值只能取 0..mx+1（保证最终值域是前缀 {0..q-1} 才计数，这里放宽到 0..k-1 再筛）
        for v in range(k):
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec(max(mx, v))
            seq.pop()
    rec(-1)
    return res


t1 = time.time()
TM = my_table(40, 20)
TC = core.U_fast_table(60, 41)
ok = all(TM[k][m] == TC[k][m] for k in range(41) for m in range(21))
ok &= all(TC[k][:7] == core.PROMPT_TABLE[k] for k in core.PROMPT_TABLE)
ok &= all(core.U_list(m, 12) == [TC[k][m] for k in range(13)] for m in range(0, 9))
# 原题直接计数（行转移 + 列三元组字面检查）锚定 a_k(n) = U_k(ceil(n/2)) U_k(floor(n/2))
ok &= all(core.a_direct(n, k) == TM[k][(n + 1) // 2] * TM[k][n // 2] for k in range(1, 5) for n in range(1, 8))
ok &= all(core.a_brute(n, k) == TM[k][(n + 1) // 2] * TM[k][n // 2] for (n, k) in [(2, 3), (3, 3), (4, 3), (3, 4), (4, 4), (5, 3)])
st_ok = True
for k in range(0, 8):
    for m in range(0, 5):
        tot, na, asc = dfs_stats(m, k)
        st_ok &= tot == TM[k][m]
rep('r1-anchor', ok and st_ok, 'my height DP == core fast DP (k<=40,m<=20) == prompt table == core.U_list (m<=8,k<=12); '
    'a_direct(n,k) and a_brute == U(ceil)U(floor) (k<=4,n<=7 / small); DFS totals == DP (k<=7,m<=4)  [%.1fs]' % (time.time() - t1))

# 细分计数：不以上升结尾 = 1/P_m，以上升到 j 结尾 = j x^2 / prod_{v=j}^m b_v（级数展开 vs DFS 与 DP 推出的统计）


def series_inv(p, n):
    p = list(p) + [0] * max(0, n - len(p))
    r = [Fr(0)] * n
    r[0] = Fr(1, p[0])
    for k in range(1, n):
        s = 0
        for i in range(1, k + 1):
            if p[i]:
                s += p[i] * r[k - i]
        r[k] = -s / p[0]
    return r


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def bpoly(i):
    return [1, -1, 0, -i]


def Ppoly(m):
    p = [1]
    for i in range(m + 1):
        p = pmul(p, bpoly(i))
    return p


ok = True
for m in range(0, 6):
    for k in range(0, 9):
        tot, na, asc = dfs_stats(m, k)
        inv = series_inv(Ppoly(m), k + 1)
        ok &= inv[k] == na
        for j in range(1, m + 1):
            den = [1]
            for v in range(j, m + 1):
                den = pmul(den, bpoly(v))
            s = series_inv(den, k + 1)
            ok &= (j * s[k - 2] if k >= 2 else 0) == asc[j]
rep('r1-refined', ok, 'refined counts by DFS (m<=5,k<=8): not-ascent == [x^k]1/P_m, ascent-to-j == [x^k] j x^2/prod_{v=j}^m b_v (C3A-02)')

# G_m = W_m/P_m 的 Taylor 系数 == DP（k<=60, m<=30）
def padd0(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


ok = True
for m in range(0, 31):
    W = [1]
    for j in range(1, m + 1):
        W = padd0(W, pmul([0, 0, j], Ppoly(j - 1)))
    s = series_inv(Ppoly(m), 61)
    ser = [sum(W[i] * s[k - i] for i in range(min(k, len(W) - 1) + 1)) for k in range(61)]
    ok &= all(ser[k] == TC[k][m] for k in range(61))
rep('r1-Wm', ok, 'G_m = W_m/P_m, W_m = 1 + x^2 sum_j j P_{j-1}: Taylor coefficients == DP, k<=60, m<=30')

# ---------------------------------------------------------------- 有理点求值工具


def poch(b, n):
    r = Fr(1)
    for i in range(n):
        r *= b + i
    return r


def G_vals(x, M):
    out, G = [], Fr(1)
    for m in range(M + 1):
        G = (G + m * x * x) / (1 - x - m * x ** 3)
        out.append(G)
    return out


def P_val(x, m):
    p = Fr(1)
    for i in range(m + 1):
        p *= 1 - x - i * x ** 3
    return p


def ser_mul(a, b, N):
    r = [Fr(0)] * (N + 1)
    for i in range(N + 1):
        if a[i]:
            for j in range(N + 1 - i):
                if b[j]:
                    r[i + j] += a[i] * b[j]
    return r


def one_minus_t_pow(c, N):
    """(1-t)^{-c} 的系数 (c)_j/j!。"""
    return [poch(Fr(c), j) / factorial(j) for j in range(N + 1)]


random.seed(424242)


def rand_x(M):
    while True:
        x = Fr(random.randint(1, 97), random.randint(2, 101))
        if x == 0:
            continue
        lam = (1 - x) / x ** 3
        if lam.denominator == 1:
            continue
        if any(1 - x - i * x ** 3 == 0 for i in range(M + 3)):
            continue
        return x


XS = [rand_x(30) for _ in range(10)] + [Fr(3, 5), Fr(-2, 7), Fr(5, 3)]

# C3A-04 / 06 / 07 / 08：1F1、Kummer、下不完全 Gamma、相邻关系（逐 t^n 系数的有理函数恒等式）
ok4 = ok6 = ok7 = ok8 = True
for x in XS:
    lam = (1 - x) / x ** 3
    xm3 = 1 / x ** 3
    for n in range(0, 26):
        lhs = (-1) ** n * xm3 ** n / (poch(1 - lam, n) * (1 - x))
        ok4 &= lhs == 1 / P_val(x, n)
        k6 = sum(Fr((-1) ** i, factorial(i)) * xm3 ** i * poch(-lam, n - i) / (poch(1 - lam, n - i) * factorial(n - i)) * xm3 ** (n - i)
                 for i in range(n + 1)) / (1 - x)
        ok6 &= k6 == 1 / P_val(x, n)
        k7 = xm3 * sum(Fr((-1) ** i, factorial(i)) * xm3 ** i * xm3 ** (n - i) / (factorial(n - i) * (lam - (n - i))) for i in range(n + 1))
        ok7 &= k7 == 1 / P_val(x, n)
        k8 = (-1) ** n * xm3 ** n / poch(-lam, n)
        ok8 &= k8 == (1 if n == 0 else 1 / P_val(x, n - 1))
rep('r1-1f1', ok4, 'C3A-04: [t^n] 1F1(1;1-lam;-t/x^3)/(1-x) == 1/P_n(x0) exactly at 13 rational points x0, n<=25')
rep('r1-kummer', ok6, 'C3A-06: [t^n] e^a 1F1(-lam;1-lam;-a)/(1-x) == 1/P_n(x0), 13 points, n<=25')
rep('r1-gamma', ok7, 'C3A-07: [t^n] x^{-3} e^a sum (-a)^j/(j!(lam-j)) == 1/P_n(x0), 13 points, n<=25')
rep('r1-shift', ok8, 'C3A-08: [t^n] 1F1(1;-lam;-t/x^3) == [n=0] + 1/P_{n-1}(x0), 13 points, n<=25')

# C3A-12 / 13：1F1 和式、Kummer 形式
ok12 = ok13 = True
for x in XS:
    lam = (1 - x) / x ** 3
    xm3 = 1 / x ** 3
    G = G_vals(x, 22)
    for m in range(0, 23):
        tot = Fr(0)
        for j in range(0, m + 1):
            cj = Fr(1) if j == 0 else j * x * x
            bj = 1 - x - j * x ** 3
            term = cj / bj * (-1) ** (m - j) * xm3 ** (m - j) / poch(j + 1 - lam, m - j)
            prodb = Fr(1)
            for i in range(j, m + 1):
                prodb *= 1 - x - i * x ** 3
            ok12 &= term == cj / prodb
            tot += term
        ok12 &= tot == G[m]

        def phi(n):
            return sum(Fr((-1) ** (n - j), factorial(n - j)) * (1 if j == 0 else j * x * x * (-x ** 3) ** j) for j in range(n + 1))
        k13 = xm3 * sum(Fr(1, factorial(m - n)) * (-1) ** m * xm3 ** m * phi(n) / (lam - n) for n in range(m + 1))
        ok13 &= k13 == G[m]
rep('r1-1f1sum', ok12, 'C3A-12: each term c_j t^j/b_j 1F1(1;j+1-lam;a) has t^m coeff c_j/prod_{i=j}^m b_i and the sum == G_m(x0); 13 points, m<=22')
rep('r1-kummerF', ok13, 'C3A-13: [t^m] x^{-3} e^a sum phi_n a^n/(lam-n) == G_m(x0); 13 points, m<=22')

# C3A-14：Humbert 解，三种写法 vs ODE 的 t 系数递推（L_A 只含 t 导数，可逐点求值）


def humbert_forms(x, A, be, N):
    A0 = sum(c * x ** i for i, c in enumerate(A))
    lamA = A0 / x ** 3
    xm3 = 1 / x ** 3
    # 递推：(A - n x^3) y_n - y_{n-1} = (beta)_n/n!
    rec, y = [], Fr(0)
    for n in range(N + 1):
        y = (y + poch(Fr(be), n) / factorial(n)) / (A0 - n * x ** 3)
        rec.append(y)
    # 第一种：(1/A)(1-t)^{-be} Phi_1(1,be;1-lamA; X=-t/(1-t), Y=-t/x^3)
    ph = [Fr(0)] * (N + 1)
    for m in range(N + 1):
        for n in range(N + 1 - m):
            c = Fr(factorial(m + n)) * poch(Fr(be), m) / (poch(1 - lamA, m + n) * factorial(m) * factorial(n))
            c *= (-1) ** (m + n) * xm3 ** n
            for r in range(N + 1 - m - n):
                cr = comb(m + r - 1, r) if m > 0 else (1 if r == 0 else 0)
                ph[m + n + r] += c * cr
    f1 = [v / A0 for v in ser_mul(ph, one_minus_t_pow(be, N), N)]
    # 第二种：(1/A) e^a Phi_1(-lamA, be; 1-lamA; t, -a)
    ph2 = [Fr(0)] * (N + 1)
    for m in range(N + 1):
        for n in range(N + 1 - m):
            ph2[m + n] += poch(-lamA, m + n) * poch(Fr(be), m) / (poch(1 - lamA, m + n) * factorial(m) * factorial(n)) * xm3 ** n
    ea = [Fr((-1) ** i, factorial(i)) * xm3 ** i for i in range(N + 1)]
    f2 = [v / A0 for v in ser_mul(ea, ph2, N)]
    # 系数形式：(1-t)^{-be} sum_n t^n/(A prod_{i<=n} b_i^A) sum_m C(n,m)(be)_m (x^3/(1-t))^m
    cf = [Fr(0)] * (N + 1)
    pb = A0
    for n in range(N + 1):
        if n >= 1:
            pb *= A0 - n * x ** 3
        for m in range(n + 1):
            c = comb(n, m) * poch(Fr(be), m) * x ** (3 * m) / pb
            s = one_minus_t_pow(m, N - n)
            for r in range(N + 1 - n):
                cf[n + r] += c * s[r]
    f3 = ser_mul(cf, one_minus_t_pow(be, N), N)
    return rec, f1, f2, f3


ok = True
cnt = 0
for x in XS[:8]:
    for A in ([1, -1], [1, -1, 0, 1], [1, 2, -1, 3], [1], [1, 0, 5]):
        A0 = sum(c * x ** i for i, c in enumerate(A))
        if A0 == 0 or (A0 / x ** 3).denominator == 1 or any(A0 - n * x ** 3 == 0 for n in range(20)):
            continue
        for be in (0, 1, 2, Fr(1, 2), -3, Fr(7, 3)):
            rec, f1, f2, f3 = humbert_forms(x, A, be, 12)
            ok &= rec == f1 == f2 == f3
            cnt += 1
rep('r1-humbert-general', ok, 'C3A-14: Y_beta first form (1/A)(1-t)^{-b}Phi_1(1,b;1-A/x^3;-t/(1-t),-t/x^3), second form (1/A)e^a Phi_1(-lamA,b;1-lamA;t,-a) '
    'and coefficient form all == unique solution of (A-t)Y-x^3tY_t=(1-t)^{-b} (t-recursion), exactly at rational x0; %d cases '
    '(5 A incl. 1+2x-x^2+3x^3, 6 beta), N<=12' % cnt)

# C3A-15 / 16：F 的有限闭式与系数形式
ok15 = ok16 = True
for x in XS:
    G = G_vals(x, 25)
    _, a1, a2, a3 = humbert_forms(x, [1, -1], 0, 16)
    _, b1, b2, b3 = humbert_forms(x, [1, -1], 1, 16)
    _, c1, c2, c3 = humbert_forms(x, [1, -1], 2, 16)
    for M in range(17):
        ok15 &= a1[M] + x * x * (c1[M] - b1[M]) == G[M]
        ok15 &= a2[M] + x * x * (c2[M] - b2[M]) == G[M]
    for M in range(26):
        s = 1 / P_val(x, M)
        for N in range(M + 1):
            inner = sum(comb(N, m) * x ** (3 * m) * (factorial(m + 1) * comb(M - N + m + 1, M - N) - factorial(m) * comb(M - N + m, M - N))
                        for m in range(N + 1))
            s += x * x * inner / P_val(x, N)
        ok16 &= s == G[M]
rep('r1-humbert-F', ok15, 'C3A-15: both Humbert closed forms of F (Y_0 + x^2(Y_2 - Y_1), A=1-x) have t^M coeff == G_M(x0); 13 points, M<=16')
rep('r1-humbert-coeff', ok16, 'C3A-16: coefficient formula for G_M == G_M(x0); 13 points, M<=25')

# C3A-31：Ncal 的 Humbert 形式 vs [y^q]Ncal = sum_i (-1)^{q-i} C(q,i) G_{i-1}
ok = True
Q = 14
for x in XS:
    A0 = 1 - x + x ** 3
    lam = (1 - x) / x ** 3
    xm3 = 1 / x ** 3
    if A0 == 0:
        continue
    G = G_vals(x, Q)
    target = [sum((-1) ** (q - i) * comb(q, i) * (1 if i == 0 else G[i - 1]) for i in range(q + 1)) for q in range(Q + 1)]

    def phi1(be):
        out = [Fr(0)] * (Q + 1)
        for m in range(Q + 1):
            for n in range(Q + 1 - m):
                c = Fr(factorial(m + n)) * poch(Fr(be), m) / (poch(-lam, m + n) * factorial(m) * factorial(n))
                c *= (-1) ** m * (-1) ** n * xm3 ** n          # (-y)^m * yh^n, yh^n = (-1)^n x^{-3n} y^n (1+y)^{-n}
                s = one_minus_t_pow(n, Q - m - n)              # (1+y)^{-n} = sum C(n+r-1,r)(-y)^r
                for r in range(Q + 1 - m - n):
                    out[m + n + r] += c * s[r] * (-1) ** r
        return out
    H0, H1, H2 = phi1(0), phi1(1), phi1(2)
    onepy = [Fr(1), Fr(1)] + [Fr(0)] * (Q - 1)
    onepy2 = [Fr(1), Fr(2), Fr(1)] + [Fr(0)] * (Q - 2)
    inner = [(A0 + x * x) * H0[q] for q in range(Q + 1)]
    t1_ = ser_mul([-2 * x * x * c for c in H1], onepy, Q)
    t2_ = ser_mul([x * x * c for c in H2], onepy2, Q)
    inner = [inner[q] + t1_[q] + t2_[q] for q in range(Q + 1)]
    inv1py = [Fr((-1) ** r) for r in range(Q + 1)]
    Ncal = [v / A0 for v in ser_mul(inner, inv1py, Q)]
    ok &= Ncal == target
rep('r1-N-humbert', ok, 'C3A-31: Ncal Humbert form (A=1-x+x^3) has y^q coeff == sum_i (-1)^{q-i}C(q,i)G_{i-1}(x0); 13 points, q<=14')

# Phi_1 的 Kummer 型变换本身、以及它的纯形式证明所用的 Pfaff 与 Kummer（随机有理参数，精确）
random.seed(99)
okT = okP = okK = True
for trial in range(12):
    al = Fr(random.randint(-50, 50), random.randint(1, 13))
    be = Fr(random.randint(-50, 50), random.randint(1, 13))
    ga = Fr(random.randint(-50, 50), random.randint(1, 13))
    if any(ga + i == 0 for i in range(30)):
        continue
    D = 10
    for p in range(D + 1):
        for q in range(D + 1 - p):
            lhs = poch(al, p + q) * poch(be, p) / (poch(ga, p + q) * factorial(p) * factorial(q))
            rhs = Fr(0)
            for m in range(p + 1):
                for n in range(q + 1):
                    e = poch(ga - al, m + n) * poch(be, m) / (poch(ga, m + n) * factorial(m) * factorial(n))
                    rhs += e * (-1) ** (m + n) * poch(be + m, p - m) / factorial(p - m) / factorial(q - n)
            okT &= lhs == rhs
    for Mx in range(16):   # Pfaff: 2F1(a,b;c;X) = (1-X)^{-b} 2F1(c-a,b;c;X/(X-1))
        lhs = poch(al, Mx) * poch(be, Mx) / (poch(ga, Mx) * factorial(Mx))
        rhs = sum(poch(ga - al, m) * poch(be, m) / (poch(ga, m) * factorial(m)) * (-1) ** m * poch(be + m, Mx - m) / factorial(Mx - m)
                  for m in range(Mx + 1))
        okP &= lhs == rhs
        lk = poch(al, Mx) / (poch(ga, Mx) * factorial(Mx))       # Kummer: 1F1(a;c;Y) = e^Y 1F1(c-a;c;-Y)
        rk = sum(poch(ga - al, n) / (poch(ga, n) * factorial(n)) * (-1) ** n / factorial(Mx - n) for n in range(Mx + 1))
        okK &= lk == rk
rep('r1-phi1-transform', okT, 'Phi_1(al,be;ga;X,Y) = (1-X)^{-be} e^Y Phi_1(ga-al,be;ga;X/(X-1),-Y): all X^pY^q coefficients, p+q<=10, '
    'at 12 random rational (al,be,ga) (exact)')
rep('r1-pfaff-kummer', okP and okK, 'Pfaff 2F1(a,b;c;X)=(1-X)^{-b}2F1(c-a,b;c;X/(X-1)) and Kummer 1F1(a;c;Y)=e^Y 1F1(c-a;c;-Y), coefficients <=15, '
    'same random parameters (these two give a purely formal proof of the Phi_1 transform)')

# C3A-22：留数律在 x_4 = 1/2（有理）处的精确核对，并对照主 Agent 的 c_4 = 645/6
x4 = Fr(1, 2)
ok = True
res = {}
for m in range(4, 41):
    W = Fr(1)
    for j in range(1, m + 1):
        W += x4 * x4 * j * P_val(x4, j - 1)
    dP = Fr(-1 - 12 * x4 * x4)          # b_4'(1/2) = -4
    for j in range(0, m + 1):
        if j != 4:
            dP *= 1 - x4 - j * x4 ** 3
    res[m] = W / dP
for m in range(4, 41):
    ok &= res[m] == res[4] * Fr(-8) ** (m - 4) / factorial(m - 4)
ok &= res[4] < 0
ok_c4 = res[4] == -Fr(645, 6) * x4
rep('r1-residue-exact', ok, 'C3A-22 at i=4 (x_4=1/2 rational): Res G_m = W_m(1/2)/P_m\'(1/2) == Res G_4 (-8)^{m-4}/(m-4)! exactly for 4<=m<=40; '
    'Res G_4 = %s < 0' % res[4])
rep('r1-residue-c4', ok_c4, 'Res_{1/2} G_4 == -c_4 x_4 with c_4 = 645/6 (main-agent value): Res = %s' % res[4])

# C3A-20：反例 (3/5,-1/2) 的独立精确部分和 + 我自己推的尾项界


def S_partial(x, t, M):
    G, tot, tp = Fr(1), Fr(0), Fr(1)
    for m in range(M + 1):
        G = (G + m * x * x) / (1 - x - m * x ** 3)
        tot += tp * G
        tp *= t
    return tot, G


def my_tail(x, t, M, GM):
    """m>lam 时 |G_m| <= (|G_{m-1}| + m x^2)/(x^3 m - 1 + x)。若 C >= |G_M| 且 C >= m x^2/(x^3 m - 2 + x) 对所有 m>M
    （该函数在 x^3 m > 2-x 时对 m 递减，故只需 m=M+1），则 |G_m| <= C (m>=M)。尾项 <= C|t|^{M+1}/(1-|t|)。"""
    assert x ** 3 * (M + 1) > 2 - x and M > (1 - x) / x ** 3
    C = max(abs(GM), (M + 1) * x * x / (x ** 3 * (M + 1) - 2 + x))
    return C * abs(t) ** (M + 1) / (1 - abs(t))


x, t = Fr(3, 5), Fr(-1, 2)
S400, G400 = S_partial(x, t, 400)
tb = my_tail(x, t, 400, G400)
okc = S400 + tb < 0
xs, ts = Fr(21, 100), Fr(-1, 2)
S500, G500 = S_partial(xs, ts, 500)
tb2 = my_tail(xs, ts, 500, G500)
okc2 = abs(S500) - tb2 > Fr(10) ** 44
rep('r1-counterex', okc and okc2, 'C3A-20: S(3/5,-1/2) = %.9f (+-%.1e, my own tail bound) < 0 while integrand > 0; '
    'S(21/100,-1/2) = %.4e, so |S| > 1e44 rigorously' % (float(S400), float(tb), float(S500)))

# C3A-26..29, 32..34：N、Ncal、H（我自己的 DFS-N k<=10 + core 快速 DP 反演 k<=40）
KN = 40
TCN = core.U_fast_table(KN, KN + 1)


def N_inv(k, q):
    s = 0
    for i in range(q + 1):
        u = (1 if k == 0 else 0) if i == 0 else TCN[k][i - 1]
        s += (-1) ** (q - i) * comb(q, i) * u
    return s


NT = [[N_inv(k, q) for q in range(KN + 1)] for k in range(KN + 1)]
ok = all(my_N_dfs(k) == NT[k][:k + 1] for k in range(0, 10))
ok &= all(NT[k][q] == 0 for k in range(KN + 1) for q in range(k + 1, KN + 1))
ok &= all(sum(NT[k][q] * comb(m + 1, q) for q in range(KN + 1)) == TCN[k][m] for k in range(KN + 1) for m in range(0, KN + 1))
rep('r1-N-basis', ok, 'C3A-26: my DFS N(k,q) (k<=9) == binomial inversion of DP; N(k,q)=0 for q>k; U_k(m) = sum_q N(k,q)C(m+1,q) (k<=40, m<=40)')


def Nc(k, q):
    return NT[k][q] if (0 <= k <= KN and 0 <= q <= KN) else 0


ok = True
for k in range(KN + 1):
    for q in range(KN + 1):
        lhs = Nc(k, q) - Nc(k - 1, q) - Nc(k - 1, q - 1) - (q - 1) * (Nc(k - 3, q) + 2 * Nc(k - 3, q - 1) + Nc(k - 3, q - 2))
        rhs = {(0, 0): 1, (1, 0): -1, (3, 0): 1, (2, 2): 1}.get((k, q), 0)
        ok &= lhs == rhs
rep('r1-N-pde', ok, 'C3A-28/29: x^k y^q coefficients of the Ncal PDE (incl. the 4 boundary corrections) and hence the triangle recurrence (k>=3,q>=1), k,q<=40')

ok = all(((1 if (k == 0 and n == 0) else 0) + (TCN[k][n - 1] if n >= 1 else 0)) == sum(NT[k][q] * comb(n, q) for q in range(KN + 1))
         for k in range(KN + 1) for n in range(KN + 2))
rep('r1-N-subst', ok, 'C3A-27: [x^k t^n](1+tF) == sum_q N(k,q) C(n,q) i.e. 1+tF = Ncal(x,t/(1-t))/(1-t), k<=40, n<=41')


def h_dp(k, deg):
    return [sum((-1) ** j * comb(k + 1, j) * TCN[k][i - j] for j in range(0, min(i, k + 1) + 1)) for i in range(deg + 1)]


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pder(p):
    return [i * p[i] for i in range(1, len(p))]


HD = [trim(h_dp(k, KN)) for k in range(KN + 1)]
ok = all(len(HD[k]) <= max(k, 1) for k in range(KN + 1))
for k in range(1, KN + 1):
    hN = [0] * (k + 1)
    for q in range(1, k + 1):
        for i in range(k - q + 1):
            hN[q - 1 + i] += NT[k][q] * comb(k - q, i) * (-1) ** i
    ok &= trim(hN) == HD[k]
hr = [[1], [1], [1, 1]]
for k in range(3, KN + 1):
    a = hr[k - 3]
    term = padd(pmul([1, -1], pder(a)) if len(a) > 1 else [0], [(k - 2) * c for c in a])
    hr.append(trim(padd(hr[k - 1], pmul([0, 1, -1], term))))
ok2 = all(hr[k] == HD[k] for k in range(KN + 1))
rep('r1-H', ok and ok2, 'C3A-32/34: h_k = (1-t)^{k+1} sum_m U_k(m)t^m has degree <= k-1 (k>=1), == sum_q N(k,q)t^{q-1}(1-t)^{k-q}; '
    '(C6) recurrence from h_0=h_1=1,h_2=1+t reproduces DP h_k, k<=40')

# H 的 PDE（C3A-33）：直接在 (z,t) 二元多项式层面核对 z^k 系数（k<=40）
ok = True
for k in range(KN + 1):
    s = list(HD[k])
    if k >= 1:
        s = padd(s, [-c for c in HD[k - 1]])
    if k >= 3:
        hk3 = HD[k - 3]
        s = padd(s, [-c for c in pmul([0, 1, -1], hk3)])                      # -z^3 t(1-t) H
        s = padd(s, [-(k - 3) * c for c in pmul([0, 1, -1], hk3)])            # -z^4 t(1-t) H_z
        if len(hk3) > 1:
            s = padd(s, [-c for c in pmul([0, 1, -2, 1], pder(hk3))])        # -z^3 t(1-t)^2 H_t
    ok &= trim(s) == ([1] if k == 0 else ([0, 1] if k == 2 else []))
rep('r1-H-pde', ok, 'C3A-33: z^k coefficient of (1-z-z^3t(1-t))H - z^4t(1-t)H_z - z^3t(1-t)^2H_t == 1 + z^2 t, exact in t, k<=40')

# C3A-09/10/11/30：我自己的朴素形式 Laplace（普通 s 级数 + Fraction），一般 A、一般 gamma；同时核对赋值界与截断安全


def lap_solve(A, gam, K, M, NX):
    """Y = A^{-1} L_s[exp((t/x^3)(e^{vs}-1)) gamma(x,t e^{vs})]，v = x^3/A。gam[m] = x-级数（长度 K+1）。
    返回 Y[m][k]、以及赋值界是否成立、N>NX-2 的项是否在 x^K 内全为 0。"""
    Ainv = series_inv(A, K + 1)
    Apw = [[Fr(1)] + [Fr(0)] * K]
    for N in range(1, NX + 1):
        Apw.append(ser_mul(Apw[-1], Ainv, K))

    def shift(p, e):
        return [Fr(0)] * e + p[:K + 1 - e] if e <= K else [Fr(0)] * (K + 1)
    # E = (e^{vs}-1)/x^3 = sum_{N>=1} x^{3N-3} A^{-N} s^N/N!
    E = {N: [c / factorial(N) for c in shift(Apw[N], 3 * N - 3)] for N in range(1, NX + 1)}
    # Phi_n := E^n/n!（s 级数，dict N -> x 级数）
    Phin = [{0: [Fr(1)] + [Fr(0)] * K}]
    for n in range(1, M + 1):
        prev = Phin[-1]
        cur = {}
        for N1, p in prev.items():
            for N2, e in E.items():
                if N1 + N2 > NX:
                    continue
                pr = ser_mul(p, e, K)
                cur[N1 + N2] = [a + b for a, b in zip(cur.get(N1 + N2, [Fr(0)] * (K + 1)), pr)]
        Phin.append({N: [c / n for c in p] for N, p in cur.items()})
    # Gam_j := gamma_j(x) e^{j v s}
    Gamj = []
    for j in range(M + 1):
        d = {}
        for N in range(NX + 1):
            if j == 0 and N > 0:
                break
            d[N] = [c * Fr(j) ** N / factorial(N) for c in ser_mul(shift(Apw[N], 3 * N), gam[j], K)]
        Gamj.append(d)
    Y, val_ok, trunc_ok = [], True, True
    for m in range(M + 1):
        Psi = {}
        for n in range(m + 1):
            for N1, p in Phin[n].items():
                for N2, q in Gamj[m - n].items():
                    if N1 + N2 > NX:
                        continue
                    pr = ser_mul(p, q, K)
                    Psi[N1 + N2] = [a + b for a, b in zip(Psi.get(N1 + N2, [Fr(0)] * (K + 1)), pr)]
        L = [Fr(0)] * (K + 1)
        for N, p in Psi.items():
            for k in range(K + 1):
                if p[k] != 0 and k < 3 * N - 3 * m:
                    val_ok = False
            if N > K // 3 + m and any(p):
                trunc_ok = False
            L = [a + factorial(N) * b for a, b in zip(L, p)]
        Y.append(ser_mul(L, Ainv, K))
    return Y, val_ok, trunc_ok


K, M = 18, 7
NX = K // 3 + M + 3
gF = [[Fr(1)] + [Fr(0)] * K] + [[Fr(0), Fr(0), Fr(m)] + [Fr(0)] * (K - 2) for m in range(1, M + 1)]
Y, v1, tr1 = lap_solve([1, -1], gF, K, M, NX)
okF = all(Y[m][k] == TCN[k][m] for m in range(M + 1) for k in range(K + 1))
AN = [1, -1, 0, 1]
gN = [[Fr(1), Fr(-1), Fr(0), Fr(1)] + [Fr(0)] * (K - 3)] + [[Fr(0), Fr(0), Fr(max(m - 1, 0))] + [Fr(0)] * (K - 2) for m in range(1, M + 1)]
YN, v2, tr2 = lap_solve(AN, gN, K, M, NX)
okN = all(YN[m][k] == ((1 if (k == 0 and m == 0) else 0) + (TCN[k][m - 1] if m >= 1 else 0)) for m in range(M + 1) for k in range(K + 1))
random.seed(5)
Ar = [1, 2, -1, 3]
gR = [[Fr(random.randint(-4, 4)) for _ in range(K + 1)] for _ in range(M + 1)]
YR, v3, tr3 = lap_solve(Ar, gR, K, M, NX)
okR = True
Ars = Ar + [0] * (K + 1)
for m in range(M + 1):
    for k in range(K + 1):
        s = sum(Ars[i] * YR[m][k - i] for i in range(0, k + 1)) - (YR[m - 1][k] if m >= 1 else 0) - (m * YR[m][k - 3] if k >= 3 else 0)
        okR &= s == gR[m][k]
rep('r1-laplace', okF and okN and okR and v1 and v2 and v3 and tr1 and tr2 and tr3,
    'C3A-09/10/11/30 with my own naive implementation: F (A=1-x) == DP and 1+tF (A=1-x+x^3, gamma=A+x^2t^2/(1-t)^2) == DP for k<=18, m<=7; '
    'random gamma with A=1+2x-x^2+3x^3 solves L_A[Y]=gamma; valuation bound ord_x[s^N t^m] >= 3N-3m holds and all N > k/3+m terms vanish (truncation safe)')

npass = sum(RES)
print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY r1 pass=%d fail=%d' % (npass, len(RES) - npass))
sys.exit(0 if npass == len(RES) else 1)
