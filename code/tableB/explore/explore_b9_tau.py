# -*- coding: utf-8 -*-
"""B9 探索：固定位置系数 h_{k,i} 的转正门槛 tau_i 的严格确定（计算机辅助证明的原型）。

h_{k,i} = sum_{j=0}^{i} (-1)^{i-j} sum_{s in Z_j} gamma_j(s) s^k L_{i-j}(k, s^3)，
L_n(k,a) = sum_{r=0}^{n} C(k+1,r) a^{n-r}/(n-r)!（由 c5a 定理 2.2 的 Binet 公式代入
h_{k,i} = sum_r (-1)^r C(k+1,r) U_k(i-r) 得到）。主项 c_i rho_i^k（c_i = gamma_i(rho_i) > 0），
余项按绝对值放大：|L_n(k,a)| <= L_n(k,|a|)，复根 |gamma_j(s)| 用三角不等式与
|s^2+3j| = |s|^2 sqrt(9 rho^2 - 3 rho - 2)。在 K* 处用 Fraction 区间验证 余项/主项 < 1，
再用 T(k+1)/T(k) <= q (k+2)/(k+2-n) 证明 k >= K* 时每一项单调减。K* 以下用精确整数逐个算。
"""
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial, log, exp


def U_cols(M, K):
    """U[m][k] = U_k(m)，0<=m<=M，0<=k<=K，按引理 1.1 的三项递推（对 k 递推）。"""
    U = []
    for m in range(M + 1):
        col = [0] * (K + 1)
        for k in range(K + 1):
            if k == 0:
                col[k] = 1
                continue
            prev_m = U[m - 1][k] if m >= 1 else 0          # U_k(m-1)，U_k(-1)=0 (k>=1)
            km1 = col[k - 1]                                 # U_{k-1}(m)
            if k - 3 >= 0:
                km3 = col[k - 3]
            elif k - 3 == -1:
                km3 = 1                                      # U_{-1} = 1
            else:
                km3 = 0                                      # U_{-2} = 0
            col[k] = prev_m + km1 + m * km3
        U.append(col)
    return U


def h_coef(U, k, i):
    return sum((-1) ** r * comb(k + 1, r) * U[i - r][k] for r in range(i + 1))


def bracket_rho(j, digits=30):
    """f_j(y)=y^3-y^2-j 的实根的有理区间 [lo,hi]，宽度 < 10^-digits。j=0 时 rho_0=1。"""
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
    """x>0 的平方根的有理区间。"""
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
    """y^{3j+3}/j! + sum_{l<j} (j-l) y^{3l+1}/l!，y>=0 时关于 y 递增。"""
    s = y ** (3 * j + 3) / factorial(j)
    for l in range(j):
        s += Fr(j - l) * y ** (3 * l + 1) / factorial(l)
    return s


class Roots:
    def __init__(self, J, digits=30):
        self.rho = []      # (lo, hi)
        self.sig = []      # |sigma_j| 的 (lo, hi)
        self.c = []        # c_j 的 (lo, hi)
        self.gs = []       # |gamma_j(sigma_j)| 的上界
        for j in range(J + 1):
            lo, hi = bracket_rho(j, digits)
            self.rho.append((lo, hi))
            if j == 0:
                self.sig.append((Fr(0), Fr(0)))
                self.c.append((Fr(1), Fr(1)))
                self.gs.append(Fr(0))
                continue
            s2lo, s2hi = lo * (lo - 1), hi * (hi - 1)
            slo, _ = sqrt_bounds(s2lo, digits)
            _, shi = sqrt_bounds(s2hi, digits)
            self.sig.append((slo, shi))
            clo = gnum(lo, j) / (hi * hi + 3 * j)
            chi = gnum(hi, j) / (lo * lo + 3 * j)
            self.c.append((clo, chi))
            # |s^2+3j| = |s|^2 sqrt(9 rho^2 - 3 rho - 2) 的下界
            d_lo, _ = sqrt_bounds(9 * lo * lo - 3 * hi - 2, digits)
            den = s2lo * d_lo
            self.gs.append(gnum(shi, j) / den)


def L_val(n, k, a):
    return sum(comb(k + 1, r) * a ** (n - r) / factorial(n - r) for r in range(n + 1))


def tail_terms(R, i, k):
    """返回 [(A, q, n)]：每一项上界为 A*q^k*L_n(k,a)，a 已并入 A 的计算之外。这里直接给出项的值上界与单调参数。"""
    rho_i_lo = R.rho[i][0]
    c_i_lo = R.c[i][0]
    terms = []
    # j = i 的复根两项
    shi = R.sig[i][1]
    q = shi / rho_i_lo
    terms.append((2 * R.gs[i] * q ** k / c_i_lo, q, 0))
    for j in range(0, i):
        n = i - j
        # 实根 rho_j（j=0 时就是 1）
        rhi = R.rho[j][1]
        q = rhi / rho_i_lo
        a = rhi ** 3
        terms.append((R.c[j][1] * q ** k * L_val(n, k, a) / c_i_lo, q, n))
        if j >= 1:
            shi = R.sig[j][1]
            q = shi / rho_i_lo
            a = shi ** 3
            terms.append((2 * R.gs[j] * q ** k * L_val(n, k, a) / c_i_lo, q, n))
    return terms


def float_ratio(R, i, k):
    """余项/主项 的浮点估计（用来找 K*），log 域。"""
    tot = 0.0
    lr = log(float(R.rho[i][0]))
    lc = log(float(R.c[i][0]))
    def add(logA, qlog, n, a):
        nonlocal tot
        # L_n(k,a) 用对数和
        ls = []
        for r in range(n + 1):
            ls.append(log(comb(k + 1, r)) + (n - r) * log(a) - log(factorial(n - r)) if a > 0 else (log(comb(k + 1, r)) if r == n else -1e300))
        mx = max(ls)
        lL = mx + log(sum(exp(x - mx) for x in ls))
        tot += exp(logA + k * qlog + lL - lc)
    sh = float(R.sig[i][1])
    tot += exp(log(2 * float(R.gs[i])) + k * (log(sh) - lr) - lc)
    for j in range(i):
        n = i - j
        rh = float(R.rho[j][1])
        add(log(float(R.c[j][1])), log(rh) - lr, n, rh ** 3)
        if j >= 1:
            sh = float(R.sig[j][1])
            add(log(2 * float(R.gs[j])), log(sh) - lr, n, sh ** 3)
    return tot


def certify(R, i, K):
    """在 K 处严格验证：sum 项 < 1，且每一项从 K 起单调减。"""
    terms = tail_terms(R, i, K)
    total = sum(t[0] for t in terms)
    mono = all((K + 2 - n) > 0 and q * (K + 2) < (K + 2 - n) for (_, q, n) in terms)
    return total < 1, mono, float(total)


def main(I0=12, Kmax=700):
    t0 = time.time()
    R = Roots(I0 + 1)
    U = U_cols(I0, Kmax)
    print('setup %.1fs' % (time.time() - t0))
    taus = []
    for i in range(1, I0 + 1):
        # 找 K*：浮点比值 < 0.5 的最小 k（从 2i 往上）
        K = None
        lo, hi = i, Kmax
        if float_ratio(R, i, hi) < 0.5:
            while hi - lo > 1:          # 二分（比值在这一段单调减；找到的 K 不必最小，认证才是证明）
                mid = (lo + hi) // 2
                if float_ratio(R, i, mid) < 0.5:
                    hi = mid
                else:
                    lo = mid
            K = hi
        if K is None:
            print('i=%d: K* > Kmax' % i)
            break
        ok, mono, tot = certify(R, i, K)
        # K* 以下精确
        last_bad = None
        for k in range(0, K + 1):
            if h_coef(U, k, i) <= 0:
                last_bad = k
        tau = (last_bad + 1) if last_bad is not None else 0
        taus.append(tau)
        print('i=%2d  tau=%4d  K*=%4d  certified=%s monotone=%s  ratio(K*)=%.3g  (%.1fs)' % (i, tau, K, ok, mono, tot, time.time() - t0), flush=True)
    print('taus:', taus)


if __name__ == '__main__':
    I0 = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    Kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 700
    main(I0, Kmax)
