# -*- coding: utf-8 -*-
"""表 B 的 B11（p_d 在任何整数平移基下都有负系数）的部分结果核对（2026-10-08）。说明见 notes/10-主Agent-表B-B11-平移范围.md。

p_d 为 N(k,k-d) 在 k>=2d+2 上的插值多项式（T4.1），deg p_d = 2d。对整数 s，平移基下的系数
  h*_j(s) = sum_{i=0}^{j} (-1)^i C(2d+1, i) p_d(s+j-i)，  p_d(k) = sum_j h*_j(s) C(k-s+2d-j, 2d)。
引理（平移范围）：若某个 s 使 h*(s) >= 0，则 s 在 [d-1, 3d-1] 内（由 p_d 的根之和 4d^2-3d，T4.1）。
逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b11 pass=<n> fail=<n>」。
  b11-mean   p_d 的次首项系数 / 首项系数 = -(4d^2-3d)（即根之和 4d^2-3d，T4.1 的结论，这里对 d<=D 重新精确核对）
  b11-hstar  对 1<=d<=D 与 [d-1, 3d-1] 中的每个整数 s，h*(s) 都有负分量（精确整数运算）；记录用到的是哪个分量
  b11-rev    反向检查：同一程序对 Stirling 数 S(k,k-d)（2d 次多项式）在平移 s=d+1 处给出非负的 h*，且等于二阶 Euler 数
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []
D = int(sys.argv[1]) if len(sys.argv) > 1 else 100


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def N_triangle(K):
    N = [[0] * (K + 3) for _ in range(K + 1)]
    N[0][0] = 1
    N[1][1] = 1
    N[2][1], N[2][2] = 1, 2
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            r = q - 1
            v = N[k - 1][r] + N[k - 1][r + 1]
            if r >= 1:
                v += r * (N[k - 3][r - 1] + 2 * N[k - 3][r] + N[k - 3][r + 1])
            N[k][q] = v
    return N


def poly_values(base_vals, n_deg, lo):
    """已知次数 <= n_deg 的多项式在 base, base+1, ... 的值（至少 n_deg+1 个），
    用 (n_deg+1) 阶差分为零向左外推到 lo。返回 dict k -> 值。"""
    vals = dict(base_vals)
    k = min(vals)
    while k > lo:
        k -= 1
        # sum_{i=0}^{n+1} (-1)^i C(n+1,i) p(k+i) = 0
        s = 0
        for i in range(1, n_deg + 2):
            s += (-1) ** i * comb(n_deg + 1, i) * vals[k + i]
        vals[k] = -s
    return vals


def hstar(vals, d, s):
    n = 2 * d
    return [sum((-1) ** i * comb(n + 1, i) * vals[s + j - i] for i in range(j + 1)) for j in range(n + 1)]


def lagrange_coeffs_top2(xs, ys):
    """返回插值多项式的首项与次首项系数（Fraction）。用 Newton 差商。"""
    n = len(xs)
    c = [Fr(y) for y in ys]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            c[i] = (c[i] - c[i - 1]) / (xs[i] - xs[i - j])
    # p = c0 + c1 (x-x0) + ... + c_{n-1} prod_{i<n-1}(x-x_i)
    lead = c[n - 1]
    sub = c[n - 2] - c[n - 1] * sum(xs[:n - 1])
    return lead, sub


def main():
    t0 = time.time()
    K = 5 * D + 5
    N = N_triangle(K)
    ok_mean = True
    ok_h = True
    stats = {}
    first_fail = None
    for d in range(1, D + 1):
        n = 2 * d
        base = {k: N[k][k - d] for k in range(2 * d + 2, 5 * d + 3)}
        # 首项、次首项
        xs = list(range(2 * d + 2, 4 * d + 3))
        lead, sub = lagrange_coeffs_top2(xs, [base[k] for k in xs])
        if sub != -(4 * d * d - 3 * d) * lead:
            ok_mean = False
        vals = poly_values(base, n, d - 1 - n - 2)
        for s in range(d - 1, 3 * d):
            h = hstar(vals, d, s)
            neg = [j for j in range(n + 1) if h[j] < 0]
            if not neg:
                ok_h = False
                if first_fail is None:
                    first_fail = (d, s)
                continue
            key = 'h0' if neg[0] == 0 else ('h1' if neg[0] == 1 else 'other')
            stats[key] = stats.get(key, 0) + 1
    report('b11-mean', ok_mean, 'p_d 的次首项/首项 = -(4d^2-3d)，1<=d<=%d' % D)
    report('b11-hstar', ok_h, '1<=d<=%d、d-1<=s<=3d-1：h*(s) 都有负分量（最先出现的负分量：%s）；首个反例 %s' % (D, stats, first_fail))
    # 反向检查：Stirling S(k,k-d)
    S = [[0] * (K + 2) for _ in range(K + 1)]
    S[0][0] = 1
    for a in range(1, K + 1):
        for b in range(1, a + 1):
            S[a][b] = b * S[a - 1][b] + S[a - 1][b - 1]
    E2 = [[0] * (K + 2) for _ in range(K + 2)]   # 二阶 Euler 数 <<n,k>>
    E2[0][0] = 1
    for a in range(1, 30):
        for b in range(0, a):
            E2[a][b] = (b + 1) * E2[a - 1][b] + ((2 * a - 1 - b) * E2[a - 1][b - 1] if b >= 1 else 0)
    ok_rev = True
    for d in range(1, min(D, 25) + 1):
        n = 2 * d
        base = {k: S[k][k - d] for k in range(2 * d, 5 * d + 3)}   # S(k,k-d) 对 k>=d 是 2d 次多项式
        vals = poly_values(base, n, 0)
        h = hstar(vals, d, d + 1)
        # S(k,k-d) = sum_{j<d} <<d,j>> C(k+d-1-j, 2d)，而 s=d+1 时基为 C(k-d-1+2d-j, 2d) = C(k+d-1-j, 2d)
        expect = [E2[d][j] if j < d else 0 for j in range(n + 1)]
        if h != expect:
            ok_rev = False
    report('b11-rev', ok_rev, 'S(k,k-d) 在平移 s=d+1 处的 h* 非负且就是二阶 Euler 数（d<=%d）' % min(D, 25))
    print('time %.1fs' % (time.time() - t0))
    npass = sum(RESULTS)
    print('SUMMARY b11 pass=%d fail=%d' % (npass, len(RESULTS) - npass))
    return 0 if npass == len(RESULTS) else 1


if __name__ == '__main__':
    sys.exit(main())
