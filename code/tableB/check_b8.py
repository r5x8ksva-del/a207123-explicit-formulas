# -*- coding: utf-8 -*-
"""表 B 的 B8：U_k 的其他负整数零点 的核对脚本（2026-10-08）。证明见 notes/15-主Agent-表B-B8-负整数零点.md。

逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b8 pass=<n> fail=<n>」。N(k,q) 由三角递推（T1.4(2)）算，
与 code/core.py 的 DP（容斥）和 DFS 计数对照；U_k(m)（m 为任意整数）按 U_k(m) = sum_q N(k,q) C(m+1,q) 取多项式值，
与 G_{-j} 的递推（T5.3(2)）对照。需要 numpy（只用于 b8-scan 的模素数向量化求值；模两个素数都为 0 时改用精确整数）。
用法：py -3.14 code/tableB/check_b8.py [--full]（默认扫描 k<=150，约半分钟；--full 扫描 k<=300，约 17 分钟）
（2026-10-08 晚按复核者 s14-b8 的意见：b8-need 改为完整周期判定并说明例外，加 b8-top，b8-scan 报告模 P1 为 0 的个数，
  b8-rev 补上经过扫描函数的人为零点与非零点对照。）
  b8-truth   N 表对照 DP（k<=40）与 DFS（k<=8）；U_k(-j) 的多项式值对照 G_{-j} 递推（k<=60, j<=40）；U_k(m) 对照 DP（k<=40, m<=10）
  b8-cong    定理 1：p 素数、p^e>k 时 U_k(m+p^e) ≡ U_k(m) (mod p)（1<=k<=30，p<=31，e=e_min 与 e_min+1，-30<=m<=30）
  b8-need    对照：p^e<=k 时同余一般不成立（在完整周期 0<=m<p^{e_min} 上判定）；不失败的恰是 p=2、2^e∈{k-1,k}
             （因为 N(k,k)、N(k,k-1) 是偶数），所以 p=2 时条件可放宽为 2^e>=k-1
  b8-one     推论 2：p^e | j 且 p^e>k 时 U_k(-j) ≡ 1 (mod p)（k<=60，j<=600，所有这样的 p）
  b8-bound   定理 3：J'_k := max_q ceil(θ_q) 恰为 θ_{k-1} = k(k^2-k-4)/2-k+2（4<=k<=K，默认 150，--full 300）；j=J_k+1 时 T_q 严格增，
             且 (-1)^k U_k(-j) > 0（k<=40，J_k<j<=J_k+200）；j=J_k 时 T_k=T_{k-1}（条件恰好失效）
  b8-small   不用定理 1 的筛选：1<=k<=60 时对一切 s_k<j<=J_k 直接检查 U_k(-j) != 0（模素数，为 0 时精确）
  b8-scan    定理 4（计算机辅助）：1<=k<=K 时，对一切 s_k<j<=J'_k 且 j | lcm(1..k) 的 j，U_k(-j) != 0；报告模 P1 为 0 的个数；
             同时确认 1<=j<=s_k 处求值器给出 0（平凡零点，求值器能识别零）
  b8-top     推论 6：j=s_k+1、s_k+2 时 U_k(-j) 等于 c5a 定理 4.3 的顶端闭式（按层 δ=3j-3-k），且不为零（1<=k<=K）
  b8-near    观察 5（数据）：u_30 在 (-60.0004,-60.0003) 有根，u_10 在 (-9.03,-9.02) 有根，U_10(-9) = -153
  b8-rev     反向检查：把 N(20,1) 改成 2，平凡零点检查失败；求值器 eval_mod 在若干非零点（含 k=K）上的余数 = 精确值的余数；
             把 (m+j0)·u_{k-1}(m)（在 C(m+1,q) 基下的系数为整数，j0>s_k 处为零）送进扫描函数 nonzero_all，确认它走到 P2 与
             精确分支并只报出 j0
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_table, N_from_U, N_brute  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []
P1 = 2147483629   # < 2^31 的素数（脚本里用 Miller-Rabin 确认）
P2 = 2147483587


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def is_prime(n):
    if n < 2:
        return False
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for p in small:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def primes_upto(n):
    return [p for p in range(2, n + 1) if is_prime(p)]


def N_table(K):
    """N[k][q]（0<=q<=k+1），三角递推 T1.4(2)：N(k,q)=N(k-1,q-1)+N(k-1,q)+(q-1)[N(k-3,q-2)+2N(k-3,q-1)+N(k-3,q)]（k>=3）。"""
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


def binom_int(n, q):
    """整数 n（可为负）上的二项式系数 C(n,q)，q>=0。"""
    if q < 0:
        return 0
    if n >= 0:
        return comb(n, q) if q <= n else 0
    return (-1) ** q * comb(q - n - 1, q)


def U_val(N, k, m):
    """U_k(m) 的多项式值（m 为任意整数）。"""
    if k == 0:
        return 1
    return sum(N[k][q] * binom_int(m + 1, q) for q in range(1, k + 1))


def U_rat(N, k, y):
    """u_k 在有理点 m=y 处的值。"""
    if k == 0:
        return Fr(1)
    tot, b = Fr(0), Fr(1)
    for q in range(1, k + 1):
        b = b * (y + 1 - (q - 1)) / q
        tot += N[k][q] * b
    return tot


def Gneg_table(J):
    G = {1: [1]}
    for j in range(1, J):
        g = G[j]
        c = [0] * (len(g) + 3)
        for k in range(len(c)):
            v = (g[k] if k < len(g) else 0) - (g[k - 1] if 0 <= k - 1 < len(g) else 0)
            v += j * (g[k - 3] if 0 <= k - 3 < len(g) else 0)
            if k == 2:
                v += j
            c[k] = v
        while len(c) > 1 and c[-1] == 0:
            c.pop()
        G[j + 1] = c
    return G


def J_bound(N, k):
    """max_{1<=q<=k-1} θ_q 的上取整，θ_q = (q+1)N(k,q)/N(k,q+1) - q + 1。"""
    best = None
    for q in range(1, k):
        v = -(-(q + 1) * N[k][q] // N[k][q + 1]) - q + 1
        best = v if best is None else max(best, v)
    return best


def smooth_divisors(k, J):
    """lcm(1..k) 的 <=J 的全部因子（每个素数幂因子都 <=k 的 j）。"""
    out = [1]
    for p in primes_upto(k):
        pe = [1]
        while pe[-1] * p <= k:
            pe.append(pe[-1] * p)
        new = []
        for d in out:
            for f in pe:
                if d * f <= J:
                    new.append(d * f)
                else:
                    break
        out = new
    return sorted(out)


def eval_mod(Nk, k, js, P):
    """U_k(-j) mod P（向量化于 js）。U_k(-j) = sum_q (-1)^q N(k,q) C(j+q-2,q)。"""
    j = np.array(js, dtype=np.int64) % P
    tot = np.zeros(len(js), dtype=np.int64)
    B = np.ones(len(js), dtype=np.int64)
    for q in range(1, k + 1):
        B = (B * ((j + (q - 2)) % P)) % P
        B = (B * pow(q, P - 2, P)) % P
        c = Nk[q] % P
        if q % 2:
            c = (P - c) % P
        tot = (tot + B * c) % P
    return tot


def nonzero_all(N, k, js):
    """对 js 中每个 j 判断 U_k(-j) != 0：先模 P1，为 0 的再模 P2，仍为 0 的用精确整数。
    返回 (全部非零?, 模 P1 为 0 的个数, 精确算过的个数, 真零点列表)。"""
    if not js:
        return True, 0, 0, []
    r1 = eval_mod(N[k], k, js, P1)
    idx = np.nonzero(r1 == 0)[0]
    exact_n, zeros = 0, []
    if len(idx):
        sub = [js[i] for i in idx]
        r2 = eval_mod(N[k], k, sub, P2)
        for jj, v in zip(sub, r2):
            if v == 0:
                exact_n += 1
                if U_val(N, k, -jj) == 0:
                    zeros.append(jj)
    return not zeros, len(idx), exact_n, zeros


def main(full=False):
    K_SCAN = 300 if full else 150
    t_start = time.time()
    N = N_table(max(K_SCAN, 60))

    # ---- b8-truth
    T = U_fast_table(40, 41)
    ok_dp = all(N[k][q] == N_from_U(T, k, q) for k in range(0, 41) for q in range(0, k + 1))
    ok_dfs = True
    for k in range(1, 9):
        nb = N_brute(k)
        ok_dfs &= all(N[k][q] == nb.get(q, 0) for q in range(0, k + 1))
    G = Gneg_table(40)
    ok_g = all(U_val(N, k, -j) == (G[j][k] if k < len(G[j]) else 0) for k in range(0, 61) for j in range(1, 41))
    ok_pos = all(U_val(N, k, m) == T[k][m] for k in range(0, 41) for m in range(0, 11))
    ok_triv = all(U_val(N, k, -j) == 0 for k in range(1, 61) for j in range(1, (k + 2) // 3 + 1))
    report('b8-truth', ok_dp and ok_dfs and ok_g and ok_pos and ok_triv,
           'N 表 = DP 容斥（k<=40）%s，= DFS（k<=8）%s；U_k(-j) 的多项式值 = G_{-j} 递推（k<=60,j<=40）%s；U_k(m) = DP（k<=40,m<=10）%s；'
           '1<=j<=s_k 时 U_k(-j)=0（k<=60）%s' % (ok_dp, ok_dfs, ok_g, ok_pos, ok_triv))

    # ---- b8-cong
    cnt, bad = 0, 0
    for k in range(1, 31):
        vals = {m: U_val(N, k, m) for m in range(-30, 31)}
        for p in primes_upto(31):
            e0 = 1
            while p ** e0 <= k:
                e0 += 1
            for e in (e0, e0 + 1):
                pe = p ** e
                for m in range(-30, 31):
                    cnt += 1
                    if (U_val(N, k, m + pe) - vals[m]) % p:
                        bad += 1
    report('b8-cong', bad == 0, '定理 1：U_k(m+p^e) ≡ U_k(m) (mod p)，p^e>k（1<=k<=30，p<=31，e=e_min,e_min+1，|m|<=30）：%d 组，失败 %d' % (cnt, bad))

    # ---- b8-need：p^e<=k 时的反例（完整周期 0<=m<p^{e_min} 上判定；由定理 1，U_k mod p 以 p^{e_min} 为周期）
    fails = 0
    tot_need = 0
    holds = []
    for k in range(2, 41):
        for p in primes_upto(k):
            emin = 1
            while p ** emin <= k:
                emin += 1
            per = p ** emin
            pe = p
            while pe <= k:
                tot_need += 1
                if any((U_val(N, k, m + pe) - U_val(N, k, m)) % p for m in range(0, per)):
                    fails += 1
                else:
                    holds.append((k, p, pe))
                pe *= p
    ok_exc = all(p == 2 and pe in (k - 1, k) for (k, p, pe) in holds)
    ok_exc = ok_exc and all((k, 2, pe) in holds for k in range(4, 41) for pe in (k - 1, k) if pe & (pe - 1) == 0)
    report('b8-need', fails > 0 and ok_exc,
           '对照：p^e<=k 时（2<=k<=40）%d 组 (k,p^e) 中有 %d 组同余失败；不失败的 %d 组恰为 p=2、2^e∈{k-1,k}（N(k,k)、N(k,k-1) 为偶数）%s'
           % (tot_need, fails, len(holds), ok_exc))

    # ---- b8-one
    cnt1, bad1 = 0, 0
    for k in range(1, 61):
        ps = primes_upto(600)
        for j in range(1, 601):
            for p in ps:
                if p > j:
                    break
                if j % p:
                    continue
                pe = 1
                while j % (pe * p) == 0:
                    pe *= p
                if pe > k:
                    cnt1 += 1
                    if U_val(N, k, -j) % p != 1 % p:
                        bad1 += 1
    report('b8-one', bad1 == 0, '推论 2：p^e | j、p^e>k 时 U_k(-j) ≡ 1 (mod p)（k<=60，j<=600）：%d 组，失败 %d' % (cnt1, bad1))

    # ---- b8-bound
    ok_J = True
    ok_inc = True
    ok_eq = True
    for k in range(4, K_SCAN + 1):
        Jf = k * (k * k - k - 4) // 2 - k + 2
        ok_J &= (J_bound(N, k) == Jf)
        j = Jf + 1
        Tq = [N[k][q] * comb(j + q - 2, q) for q in range(1, k + 1)]
        ok_inc &= all(Tq[i] < Tq[i + 1] for i in range(len(Tq) - 1))
        j = Jf
        ok_eq &= (N[k][k] * comb(j + k - 2, k) == N[k][k - 1] * comb(j + k - 3, k - 1))
    ok_sign = all((-1) ** k * U_val(N, k, -j) > 0 for k in range(1, 41)
                  for j in range((J_bound(N, k) if k >= 2 else 1) + 1, (J_bound(N, k) if k >= 2 else 1) + 201))
    report('b8-bound', ok_J and ok_inc and ok_eq and ok_sign,
           '定理 3：J_k = max θ_q = k(k^2-k-4)/2-k+2（4<=k<=%d）%s；j=J_k+1 时 T_q 严格增 %s；j=J_k 时 T_k=T_{k-1} %s；'
           '(-1)^k U_k(-j)>0（k<=40，J_k<j<=J_k+200）%s' % (K_SCAN, ok_J, ok_inc, ok_eq, ok_sign))

    # ---- b8-small：不经筛选
    ok_small, nsm, nex = True, 0, 0
    for k in range(1, 61):
        s = (k + 2) // 3
        J = J_bound(N, k) if k >= 2 else 1
        js = list(range(s + 1, J + 1))
        nsm += len(js)
        ok, p1z, ex, zs = nonzero_all(N, k, js)
        ok_small &= ok
        nex += ex
    report('b8-small', ok_small, '不用定理 1：1<=k<=60 时一切 s_k<j<=J_k 都有 U_k(-j)!=0（共 %d 个 j，其中 %d 个模两素数为 0 改用精确）' % (nsm, nex))

    # ---- b8-scan
    t0 = time.time()
    ok_scan, ncand, nex, np1, zero_found = True, 0, 0, 0, []
    ok_trivdet = True
    for k in range(1, K_SCAN + 1):
        s = (k + 2) // 3
        J = J_bound(N, k) if k >= 2 else 1
        cand = [j for j in smooth_divisors(k, J) if j > s]
        ncand += len(cand)
        ok, p1z, ex, zs = nonzero_all(N, k, cand)
        ok_scan &= ok
        nex += ex
        np1 += p1z
        zero_found += [(k, z) for z in zs]
        if s >= 1:
            r = eval_mod(N[k], k, list(range(1, s + 1)), P1)
            ok_trivdet &= bool(np.all(r == 0))
    report('b8-scan', ok_scan and ok_trivdet and is_prime(P1) and is_prime(P2),
           '定理 4：1<=k<=%d，s_k<j<=J_k 且 j | lcm(1..k) 的 %d 个 j 全部 U_k(-j)!=0（模 P1 为 0 的 %d 个，改用精确 %d 个；零点 %s）；'
           '求值器在 1<=j<=s_k 处给出 0：%s；P1、P2 是素数（%.0fs）' % (K_SCAN, ncand, np1, nex, zero_found or '无', ok_trivdet,
                                                          time.time() - t0))

    # ---- b8-top：推论 6
    cst = [[0] * 4 for _ in range(K_SCAN + 10)]     # c(n,k)，k<=3（第一类无符号 Stirling 数）
    cst[0][0] = 1
    for n in range(1, K_SCAN + 10):
        for kk in range(1, 4):
            cst[n][kk] = (n - 1) * cst[n - 1][kk] + cst[n - 1][kk - 1]

    def top_closed(j, d):
        f = factorial(j - 1)
        return [f, f, -cst[j][2], f, cst[j][2] + cst[j][3], f - cst[j][2] - cst[j][3]][d]
    ok_top, ntop = True, 0
    for k in range(1, K_SCAN + 1):
        s = (k + 2) // 3
        for j in (s + 1, s + 2):
            d = 3 * j - 3 - k
            v = U_val(N, k, -j)
            ok_top &= (0 <= d <= 5) and v == top_closed(j, d) and v != 0
            ntop += 1
    report('b8-top', ok_top, '推论 6：j=s_k+1、s_k+2 时 U_k(-j) = c5a 定理 4.3 的顶端闭式且不为零（1<=k<=%d，%d 个）' % (K_SCAN, ntop))

    # ---- b8-near
    def sgn(v):
        return (v > 0) - (v < 0)
    a1 = U_rat(N, 30, Fr(-600003, 10000))
    a2 = U_rat(N, 30, Fr(-600004, 10000))
    b1 = U_rat(N, 10, Fr(-902, 100))
    b2 = U_rat(N, 10, Fr(-903, 100))
    u10 = U_val(N, 10, -9)
    ok_near = sgn(a1) * sgn(a2) < 0 and sgn(U_val(N, 30, -60)) == sgn(a1) and sgn(b1) * sgn(b2) < 0 and u10 == -153 \
        and U_val(N, 30, -60) == 131528853446152312280711
    report('b8-near', ok_near, '观察 5（数据）：u_30 在 m∈(-60.0004,-60.0003) 变号（U_30(-60)=%d），u_10 在 (-9.03,-9.02) 变号，U_10(-9)=%d'
           % (U_val(N, 30, -60), u10))

    # ---- b8-rev
    Nbad = [row[:] for row in N[:61]]
    Nbad[20][1] = 2
    rv1 = not all(U_val(Nbad, 20, -j) == 0 for j in range(1, 8))
    k0, j0 = 45, 400
    ref = U_val(N, k0, -j0)
    js = list(range(16, 600))
    r = [(U_val(N, k0, -j) - ref) % P1 for j in js]
    rv2 = (r[js.index(j0)] == 0) and sum(1 for v in r if v == 0) == 1
    # 求值器在非零点上与精确值的余数一致（含 k=K_SCAN）
    rv3 = True
    for k in (50, 100, K_SCAN):
        s = (k + 2) // 3
        J = J_bound(N, k)
        pts = [s + 1, s + 7, J // 2, J]
        rv3 &= all(int(v) == U_val(N, k, -j) % P1 for j, v in zip(pts, eval_mod(N[k], k, pts, P1)))
    # (m+j0)·u_{k-1}(m) 在 C(m+1,q) 基下的系数（用 (m+1)C(m+1,q) = (q+1)C(m+1,q+1) + q C(m+1,q)），送进扫描函数
    kf, jf = 40, 1234
    Nf = [row[:] for row in N[:kf + 1]]
    Nf[kf] = [0] * (kf + 2)
    for q in range(0, kf):
        Nf[kf][q + 1] += (q + 1) * N[kf - 1][q]
        Nf[kf][q] += (q + jf - 1) * N[kf - 1][q]
    ok_poly = all(U_val(Nf, kf, m) == (m + jf) * U_val(N, kf - 1, m) for m in range(-60, 30))
    okf, p1z, ex, zs = nonzero_all(Nf, kf, list(range(15, 2001)))
    rv4 = ok_poly and (not okf) and zs == [jf] and p1z >= 1 and ex >= 1
    report('b8-rev', rv1 and rv2 and rv3 and rv4,
           '反向检查：N(20,1) 改成 2 后平凡零点检查失败 %s；人为零点 U_45(-j)-U_45(-400) 只在 j=400 处为 0 %s；'
           'eval_mod 在非零点（k=50,100,%d）的余数 = 精确值的余数 %s；(m+%d)u_%d(m) 经扫描函数走到 P2（%d 个）与精确分支（%d 个），'
           '只报出 j=%s %s' % (rv1, rv2, K_SCAN, rv3, jf, kf - 1, p1z, ex, zs, rv4))
    print('total %.0fs' % (time.time() - t_start))


if __name__ == '__main__':
    main(full='--full' in sys.argv)
    n_pass = sum(RESULTS)
    n_fail = len(RESULTS) - n_pass
    print('SUMMARY b8 pass=%d fail=%d' % (n_pass, n_fail))
    sys.exit(0 if n_fail == 0 else 1)
