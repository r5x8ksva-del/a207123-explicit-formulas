# -*- coding: utf-8 -*-
"""表 B 的 B9：h_k 的符号模式、固定位置系数的转正门槛与 h_k(-1) 的核对脚本（2026-10-08）。
证明见 notes/16-主Agent-表B-B9-符号模式与门槛.md。

逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b9 pass=<n> fail=<n>」。U_k(m) 由引理 1.1 的三项递推算，
与 code/core.py 的高度 DP 对照；h_k 由 T1.7 的递推算（只保留三项），与 h_{k,i} = sum_j (-1)^{i-j} C(k+1,i-j) U_k(j) 对照。
需要 numpy（只在 b9-binet 里求三次方程的近似复根做数值对照；门槛的证书全部是有理数运算）。
用法：py -3.14 code/tableB/check_b9.py [--full]（默认认证 i<=20，约 15 s；--full 认证 i<=40，约 2–3 分钟）
  b9-truth    U 的三项递推 = DP（k<=40, m<=8）；h 的递推 = 由 U 反演的 h（k<=60）
  b9-binet    引理 1（由 c5a 定理 2.2）：h_{k,i} = sum_{j<=i} (-1)^{i-j} sum_{s∈Z_j} γ_j(s) s^k L_{i-j}(k,s^3)，
              L_n(k,a) = sum_r C(k+1,r) a^{n-r}/(n-r)!（数值对照，0<=i<=10，0<=k<=40，误差 / 最大项 < 1e-10）
  b9-tau      定理 2（计算机辅助）：τ_i（h_{k,i}>0 对一切 k>=τ_i 成立的最小 τ_i）对 1<=i<=I 等于所列值；每个 i 的证书：
              K* 处 余项上界/主项下界 < 1（Fraction 区间运算），K* 起每一项单调减，k<=K* 用精确整数
  b9-tau-rev  反向检查：h_{τ_i-1,i}<=0（门槛不能再小）；在 K=τ_i 处同一个余项界 >=1（证书确实需要精确部分）；把 c_i 的下界
              缩小 10^6 倍后在原 K* 处认证失败
  b9-second   定理 3：次高项 h_{k,d-1} 的闭式（c5a 定理 4.4(d)）= 实际值（3<=k<=1000）；B_1(a)<0（1<=a<=54）、>0（55<=a<=2000），
              B_2(a)>0（1<=a<=2000）；Δφ_1 = [(n-4)(H_n-2)-7+4/n]/(n(n+1)) 精确成立（n<=300），且 n>=12 时为正（n<=2000）
  b9-signs    k<=1000：h_k 没有零系数；系数恰变号 floor(k/3) 次（A19 的推论）；初始正段长 >= 1+#{i<=I: τ_i<=k}
  b9-hm1      h_k(-1) = sum_q (-1)^{q-1} 2^{k-q} N(k,q)（1<=k<=200）；3<=k<=1000 时 h_k(-1)!=0（k=2 时 h_2(-1)=0）
  b9-osc      数值佐证（不是证明）：h_k(-1) 在 3<=k<=1000 的变号次数（997 次相邻比较）与 997·arg(w_0)/(3π)（w_0=-2+iπ）
              相差 <5，而奇点若在 iπ 则应约为 166 次（复核者 s14-b9 计入移动奇点的修正后预测 223.3）
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial, log, exp, pi, atan2, lgamma

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_table, N_from_U  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []
TAU = [2, 8, 16, 24, 33, 41, 50, 59, 68, 77, 86, 95, 105, 114, 123, 132, 141, 151, 160, 169,
       178, 188, 197, 206, 216, 225, 234, 244, 253, 263, 272, 281, 291, 300, 310, 319, 328, 338, 347, 357]


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


# ------------------------------------------------------------------ U 与 h
def U_cols(M, K):
    """U[m][k] = U_k(m)（0<=m<=M, 0<=k<=K），引理 1.1：U_k(m)=U_k(m-1)+U_{k-1}(m)+m U_{k-3}(m)，U_{-1}=1，U_{-2}=0，U_k(-1)=0（k>=1）。"""
    U = []
    for m in range(M + 1):
        col = [0] * (K + 1)
        for k in range(K + 1):
            if k == 0:
                col[k] = 1
                continue
            prev_m = U[m - 1][k] if m >= 1 else 0
            km3 = col[k - 3] if k >= 3 else (1 if k == 2 else 0)
            col[k] = prev_m + col[k - 1] + m * km3
        U.append(col)
    return U


def h_coef(U, k, i):
    return sum((-1) ** r * comb(k + 1, r) * U[i - r][k] for r in range(i + 1))


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def h_step(hk1, hk3, k):
    """T1.7：h_k = h_{k-1} + t(1-t)[(1-t)h'_{k-3} + (k-2)h_{k-3}]（k>=3）。"""
    g = hk3
    d = [i * g[i] for i in range(1, len(g))]
    a = padd(d, [-x for x in ([0] + d)])
    a = padd(a, [(k - 2) * x for x in g])
    b = padd([0] + a, [-x for x in ([0, 0] + a)])
    h = padd(hk1, b)
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


def h_iter(K):
    win = {0: [1], 1: [1], 2: [1, 1]}
    for k in range(0, K + 1):
        if k >= 3:
            win[k] = h_step(win[k - 1], win[k - 3], k)
            del win[k - 3]
        yield k, win[k]


def N_table(K):
    N = [[0] * (K + 2) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1], N[2][2] = 1, 2
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            t = (N[k - 3][q - 2] if q >= 2 else 0) + 2 * N[k - 3][q - 1] + N[k - 3][q]
            N[k][q] = N[k - 1][q - 1] + N[k - 1][q] + (q - 1) * t
    return N


# ------------------------------------------------------------------ 门槛证书（有理区间）
def bracket_rho(j, digits=30):
    if j == 0:
        return Fr(1), Fr(1)
    lo, hi = Fr(1), Fr(2)
    while hi ** 3 - hi ** 2 - j < 0:
        hi *= 2
    eps = Fr(1, 10 ** digits)
    while hi - lo > eps:
        mid = (lo + hi) / 2
        if mid ** 3 - mid ** 2 - j < 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


def sqrt_bounds(x, digits=30):
    lo, hi = Fr(0), max(Fr(1), x)
    eps = Fr(1, 10 ** digits)
    while hi - lo > eps:
        mid = (lo + hi) / 2
        if mid * mid < x:
            lo = mid
        else:
            hi = mid
    return lo, hi


def gnum(y, j):
    """y^{3j+3}/j! + sum_{l<j} (j-l) y^{3l+1}/l!（y>=0 时递增；γ_j(s) = gnum(s,j)/(s^2+3j)）。"""
    s = y ** (3 * j + 3) / factorial(j)
    for l in range(j):
        s += Fr(j - l) * y ** (3 * l + 1) / factorial(l)
    return s


class Roots:
    """ρ_j、|σ_j|、c_j = γ_j(ρ_j) 的有理区间，|γ_j(σ_j)| 的有理上界（j<=J）。"""
    def __init__(self, J, digits=30):
        self.rho, self.sig, self.c, self.gs = [], [], [], []
        for j in range(J + 1):
            lo, hi = bracket_rho(j, digits)
            self.rho.append((lo, hi))
            if j == 0:
                self.sig.append((Fr(0), Fr(0)))
                self.c.append((Fr(1), Fr(1)))
                self.gs.append(Fr(0))
                continue
            s2lo, s2hi = lo * (lo - 1), hi * (hi - 1)          # |σ_j|^2 = ρ_j(ρ_j-1)
            slo, _ = sqrt_bounds(s2lo, digits)
            _, shi = sqrt_bounds(s2hi, digits)
            self.sig.append((slo, shi))
            self.c.append((gnum(lo, j) / (hi * hi + 3 * j), gnum(hi, j) / (lo * lo + 3 * j)))
            d_lo, _ = sqrt_bounds(9 * lo * lo - 3 * hi - 2, digits)   # |3σ-2| = sqrt(9ρ^2-3ρ-2)
            self.gs.append(gnum(shi, j) / (s2lo * d_lo))             # |σ^2+3j| = |σ|^2 |3σ-2|


def L_val(n, k, a):
    return sum(comb(k + 1, r) * a ** (n - r) / factorial(n - r) for r in range(n + 1))


def tail_terms(R, i, k, c_scale=1):
    """余项各项除以主项下界 c_i ρ_i^k 后的上界 T 及单调参数 (q, n)：T(k) = A q^k L_n(k,a)/c_i。"""
    rlo = R.rho[i][0]
    clo = R.c[i][0] / c_scale
    terms = []
    q = R.sig[i][1] / rlo
    terms.append((2 * R.gs[i] * q ** k / clo, q, 0))
    for j in range(0, i):
        n = i - j
        rhi = R.rho[j][1]
        q = rhi / rlo
        terms.append((R.c[j][1] * q ** k * L_val(n, k, rhi ** 3) / clo, q, n))
        if j >= 1:
            shi = R.sig[j][1]
            q = shi / rlo
            terms.append((2 * R.gs[j] * q ** k * L_val(n, k, shi ** 3) / clo, q, n))
    return terms


def float_ratio(R, i, k):
    lr = log(float(R.rho[i][0]))
    lc = log(float(R.c[i][0]))
    tot = exp(log(2 * float(R.gs[i])) + k * (log(float(R.sig[i][1])) - lr) - lc)
    for j in range(i):
        n = i - j
        for (A, s) in ([(float(R.c[j][1]), float(R.rho[j][1]))] +
                       ([(2 * float(R.gs[j]), float(R.sig[j][1]))] if j >= 1 else [])):
            ls = [log(comb(k + 1, r)) + (n - r) * log(s ** 3) - lgamma(n - r + 1) for r in range(n + 1)]
            mx = max(ls)
            lL = mx + log(sum(exp(x - mx) for x in ls))
            tot += exp(log(A) + k * (log(s) - lr) + lL - lc)
    return tot


def certify(R, i, K, c_scale=1):
    terms = tail_terms(R, i, K, c_scale)
    total = sum(t[0] for t in terms)
    mono = all((K + 2 - n) > 0 and q * (K + 2) < (K + 2 - n) for (_, q, n) in terms)
    return total < 1, mono, total


def find_K(R, i, Kmax):
    lo, hi = i, Kmax
    if float_ratio(R, i, hi) >= 0.5:
        return None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if float_ratio(R, i, mid) < 0.5:
            hi = mid
        else:
            lo = mid
    return hi


# ------------------------------------------------------------------ Stirling 数（第一类无符号）
def stirling1_upto(n):
    c = [[0] * 5 for _ in range(n + 1)]   # 只需 c(n,0..3)
    c[0][0] = 1
    for m in range(1, n + 1):
        for k in range(1, 4):
            c[m][k] = (m - 1) * c[m - 1][k] + c[m - 1][k - 1]
    return c


def second_closed(k, c):
    a = k // 3
    if k % 3 == 0:
        return (-1) ** (a + 1) * 2 * a * factorial(a)
    if k % 3 == 1:
        return (-1) ** a * (c[a + 3][2] + c[a + 3][3] - factorial(a + 2) - (3 * a + 2) * c[a + 2][2])
    return (-1) ** a * (c[a + 3][2] + c[a + 3][3] - 3 * (a + 1) * factorial(a + 1))


def main(full=False):
    I = 40 if full else 20
    t0 = time.time()

    # ---- b9-truth
    T = U_fast_table(40, 8)
    U8 = U_cols(8, 40)
    ok_u = all(T[k][m] == U8[m][k] for k in range(41) for m in range(9))
    U60 = U_cols(61, 60)
    ok_h = True
    for k, h in h_iter(60):
        ok_h &= all((h[i] if i < len(h) else 0) == h_coef(U60, k, i) for i in range(0, min(k, 60) + 1))
    report('b9-truth', ok_u and ok_h, 'U 的三项递推 = DP（k<=40,m<=8）%s；h 的递推 = 由 U 反演（k<=60）%s' % (ok_u, ok_h))

    # ---- b9-binet（数值）
    def roots(j):
        if j == 0:
            return [1.0 + 0j]
        out = []
        for s in np.roots([1, -1, 0, -j]):
            s = complex(s)
            for _ in range(6):
                s -= (s ** 3 - s ** 2 - j) / (3 * s * s - 2 * s)
            out.append(s)
        return out

    def gam(j, s):
        if j == 0:
            return 1.0
        num = s ** (3 * j + 3) / factorial(j) + sum((j - l) * s ** (3 * l + 1) / factorial(l) for l in range(j))
        return num / (s * s + 3 * j)
    worst = 0.0
    U40 = U_cols(11, 40)
    for i in range(0, 11):
        for k in range(0, 41):
            v, big = 0j, 0.0
            for j in range(0, i + 1):
                for s in roots(j):
                    n = i - j
                    L = sum(comb(k + 1, r) * (s ** 3) ** (n - r) / factorial(n - r) for r in range(n + 1))
                    t = (-1) ** (i - j) * gam(j, s) * s ** k * L
                    v += t
                    big = max(big, abs(t))
            worst = max(worst, abs(v - h_coef(U40, k, i)) / big)
    report('b9-binet', worst < 1e-10, '引理 1（Binet 形式）与精确 h_{k,i} 对照（0<=i<=10，0<=k<=40）：|差|/最大项 <= %.1e' % worst)

    # ---- b9-tau
    R = Roots(I + 1)
    Kmax = 1100 if full else 520
    U = U_cols(I, Kmax)
    taus, info, ok_all = [], [], True
    certs = {}
    for i in range(1, I + 1):
        K = find_K(R, i, Kmax)
        if K is None:
            ok_all = False
            break
        ok, mono, tot = certify(R, i, K)
        last_bad = None
        for k in range(0, K + 1):
            if h_coef(U, k, i) <= 0:
                last_bad = k
        tau = (last_bad + 1) if last_bad is not None else 0
        taus.append(tau)
        certs[i] = (K, tot)
        ok_all &= ok and mono
        info.append('%d:%d(K*=%d)' % (i, tau, K))
    ok_tau = ok_all and taus == TAU[:I]
    report('b9-tau', ok_tau, '定理 2：τ_1..τ_%d = %s；每个证书 K* 处余项/主项 < 1 且之后单调（%.0fs）；%s'
           % (I, taus, time.time() - t0, ' '.join(info[:6]) + ' … ' + info[-1]))

    # ---- b9-tau-rev
    rv1 = all(h_coef(U, TAU[i - 1] - 1, i) <= 0 for i in range(1, I + 1))
    rv2 = all(not certify(R, i, TAU[i - 1])[0] for i in range(2, min(I, 12) + 1))
    rv3 = all(not certify(R, i, certs[i][0], c_scale=10 ** 6)[0] for i in range(2, min(I, 12) + 1))
    report('b9-tau-rev', rv1 and rv2 and rv3, '反向检查：h_{τ_i-1,i}<=0（i<=%d）%s；K=τ_i 处余项界 >=1（2<=i<=12）%s；'
           'c_i 下界缩小 10^6 倍后原 K* 处认证失败 %s' % (I, rv1, rv2, rv3))

    # ---- b9-second
    c = stirling1_upto(2010)
    ok_cf = True
    for k, h in h_iter(1000):
        if k >= 3:
            ok_cf &= (h[-2] == second_closed(k, c))
    B1 = [c[a + 3][2] + c[a + 3][3] - factorial(a + 2) - (3 * a + 2) * c[a + 2][2] for a in range(1, 2001)]
    B2 = [c[a + 3][2] + c[a + 3][3] - 3 * (a + 1) * factorial(a + 1) for a in range(1, 2001)]
    ok_b1 = all(B1[a - 1] < 0 for a in range(1, 55)) and all(B1[a - 1] > 0 for a in range(55, 2001))
    ok_b2 = all(v > 0 for v in B2)

    def Hn(n):
        return sum(Fr(1, i) for i in range(1, n + 1))

    def e2(n):
        s, h = Fr(0), Fr(0)
        for i in range(1, n + 1):
            s += h / i
            h += Fr(1, i)
        return s

    def phi1(n):   # n = a+2：φ_1 = H_n + e_2(n) - 1 - (3n-4) H_{n-1}/n
        return Hn(n) + e2(n) - 1 - Fr(3 * n - 4, n) * Hn(n - 1)
    ok_d = all(phi1(n + 1) - phi1(n) == ((n - 4) * (Hn(n) - 2) - 7 + Fr(4, n)) / (n * (n + 1)) for n in range(3, 301))
    ok_pos = True
    H = Fr(0)
    Hf = 0.0
    for n in range(1, 2001):
        Hf += 1.0 / n
        if n >= 12 and n <= 300:
            H = Hn(n) if n == 12 else H + Fr(1, n)
            ok_pos &= ((n - 4) * (H - 2) - 7 + Fr(4, n)) > 0
        elif n > 300:
            ok_pos &= ((n - 4) * (Hf - 2) - 7 + 4.0 / n) > 1.0      # 远离 0，浮点足够（n>300 时值 > 1000）
    ok_phi = all((phi1(a + 2) < 0) == (a <= 54) for a in range(1, 80))
    report('b9-second', ok_cf and ok_b1 and ok_b2 and ok_d and ok_pos and ok_phi,
           '定理 3：次高项闭式 = 实际值（3<=k<=1000）%s；B_1(a)<0 ⇔ a<=54（a<=2000）%s；B_2(a)>0（a<=2000）%s；'
           'Δφ_1 恒等式（n<=300）%s；n>=12 时 Δφ_1>0（n<=2000）%s；φ_1(a+2)<0 ⇔ a<=54（a<80，精确）%s'
           % (ok_cf, ok_b1, ok_b2, ok_d, ok_pos, ok_phi))

    # ---- b9-signs 与 b9-hm1
    N = N_table(200)
    ok_z, ok_chg, ok_run, ok_hm, ok_nz = True, True, True, True, True
    hm1 = []
    for k, h in h_iter(1000):
        if any(x == 0 for x in h):
            ok_z = False
        sg = [x > 0 for x in h]
        if sum(1 for i in range(len(sg) - 1) if sg[i] != sg[i + 1]) != k // 3:
            ok_chg = False
        run = 0
        while run < len(h) and h[run] > 0:
            run += 1
        if run < 1 + sum(1 for t in TAU[:I] if t <= k) and k >= 2:
            ok_run = False
        v = sum(x if i % 2 == 0 else -x for i, x in enumerate(h))
        hm1.append(v)
        if 1 <= k <= 200:
            ok_hm &= (v == sum((-1) ** (q - 1) * 2 ** (k - q) * N[k][q] for q in range(1, k + 1)))
        if k >= 3 and v == 0:
            ok_nz = False
    report('b9-signs', ok_z and ok_chg and ok_run, 'k<=1000：没有零系数 %s；变号次数 = floor(k/3) %s；初始正段长 >= 1+#{i<=%d: τ_i<=k} %s'
           % (ok_z, ok_chg, I, ok_run))
    report('b9-hm1', ok_hm and ok_nz and hm1[2] == 0, 'h_k(-1) = sum_q (-1)^{q-1} 2^{k-q} N(k,q)（1<=k<=200）%s；3<=k<=1000 时 h_k(-1)!=0 %s；h_2(-1)=0'
           % (ok_hm, ok_nz))

    # ---- b9-osc（数值佐证）
    chg = sum(1 for k in range(3, 1001) if (hm1[k] > 0) != (hm1[k - 1] > 0))
    steps = 1000 - 3 + 1 - 1          # 3<=k<=1000 的相邻比较次数：997（k=2 处 h_2(-1)=0，不参与）
    pred = steps * atan2(pi, -2) / (3 * pi)
    alt = steps * (pi / 2) / (3 * pi)
    report('b9-osc', abs(chg - pred) < 5, '数值佐证：h_k(-1) 在 3<=k<=1000 变号 %d 次（%d 次相邻比较）；w_0=-2+iπ 的相位给出 %.1f 次，'
           '奇点若在 iπ 则约 %.1f 次' % (chg, steps, pred, alt))
    print('total %.0fs' % (time.time() - t0))


if __name__ == '__main__':
    main(full='--full' in sys.argv)
    n_pass = sum(RESULTS)
    n_fail = len(RESULTS) - n_pass
    print('SUMMARY b9 pass=%d fail=%d' % (n_pass, n_fail))
    sys.exit(0 if n_fail == 0 else 1)
