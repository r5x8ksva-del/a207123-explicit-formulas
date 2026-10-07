# -*- coding: utf-8 -*-
"""表 B 的 B7 前半（f_k(t) 的 Gevrey-1/3 增长）的核对脚本（2026-10-07）。证明见 notes/07-主Agent-表B-B7-Gevrey上界.md。

f_k(t) := sum_m U_k(m) t^m = h_k(t)/(1-t)^(k+1)，h_k(t) = sum_q N(k,q) t^(q-1) (1-t)^(k-q)。
逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b7 pass=<n> fail=<n>」。
  b7-hk     由 N 三角算出的 h_k 与 U 的 DP 一致：h_{k,i} = sum_j (-1)^(i-j) C(k+1,i-j) U_k(j)（k<=40）
  b7-rec    f_k 的递推 (1-t) f_k = f_{k-1} + t f'_{k-3}（k>=3）在 t=-1/2, 1/3 处精确成立（k<=60；f' 由 h 的导数精确算出）
  b7-upper  定理 G1 的显式上界 |f_k(t)| <= M lambda^k (2/(1-r))^floor(k/3) floor(k/3)!（r=|t|）在 t in {-1/2, 1/2, -9/10, 9/10} 成立（k<=300）
  b7-lower  引理：U_k(m) >= m^floor(k/3)（k<=40, m<=12）；定理 G2 的下界 f_k(t) >= t floor(k/3)!/(e sqrt(floor(k/3)) L^floor(k/3))（L=ln(1/t)）在 t in {1/2, 9/10} 成立（3<=k<=300）
  b7-growth 记录：|f_k(-1/2)|^(1/k) 在 k=75,150,300 的值（与报告 T3.4(5) 的 1.669、2.036 对照），比值约为 2^(1/3)
"""
import math
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_table  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []


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


def h_poly(N, k):
    """h_k 的系数（低次在前），k>=1：sum_q N(k,q) t^(q-1)(1-t)^(k-q)；h_0 = 1。"""
    if k == 0:
        return [1]
    out = [0] * k
    for q in range(1, k + 1):
        c = N[k][q]
        if not c:
            continue
        for i in range(k - q + 1):
            out[q - 1 + i] += c * comb(k - q, i) * (-1) ** i
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def peval(p, x):
    s = Fr(0)
    for c in reversed(p):
        s = s * x + c
    return s


def f_val(h, k, t):
    return peval(h, t) / (1 - t) ** (k + 1)


def f_deriv(h, k, t):
    """f = h/(1-t)^(k+1)，f' = h'/(1-t)^(k+1) + (k+1) h/(1-t)^(k+2)。"""
    dh = [i * h[i] for i in range(1, len(h))] or [0]
    return peval(dh, t) / (1 - t) ** (k + 1) + (k + 1) * peval(h, t) / (1 - t) ** (k + 2)


def log_abs(x):
    """|x| 的自然对数，x 为 Fraction（可很大或很小）。"""
    x = abs(x)
    return math.log(x.numerator) - math.log(x.denominator)


def main():
    t0 = time.time()
    K = 300
    N = N_triangle(K)
    H = {k: h_poly(N, k) for k in range(0, K + 1)}
    # b7-hk
    Tab = U_fast_table(40, 42)
    ok = True
    for k in range(1, 41):
        for i in range(len(H[k])):
            v = sum((-1) ** (i - j) * comb(k + 1, i - j) * Tab[k][j] for j in range(0, i + 1))
            ok = ok and v == H[k][i]
        ok = ok and all(sum((-1) ** (i - j) * comb(k + 1, i - j) * Tab[k][j] for j in range(0, i + 1)) == 0
                        for i in range(len(H[k]), k + 2))
    report('b7-hk', ok, 'N 三角给出的 h_k 与 U 的 DP 一致（k<=40，含次数）')
    # b7-rec
    ok = True
    for t in (Fr(-1, 2), Fr(1, 3)):
        for k in range(3, 61):
            lhs = (1 - t) * f_val(H[k], k, t)
            rhs = f_val(H[k - 1], k - 1, t) + t * f_deriv(H[k - 3], k - 3, t)
            ok = ok and lhs == rhs
    report('b7-rec', ok, '(1-t)f_k = f_{k-1} + t f\'_{k-3} 在 t=-1/2, 1/3 精确成立（3<=k<=60）')
    # b7-upper
    ok = True
    worst = {}
    for t in (Fr(-1, 2), Fr(1, 2), Fr(-9, 10), Fr(9, 10)):
        r = abs(float(t))
        R = (1 + r) / 2
        lam = max(2 / (1 - R), (2 * math.e * R / (1 - R)) ** (1 / 3))
        M = (1 + R) / (1 - R) ** 3
        slack = []
        for k in range(0, K + 1):
            p = k // 3
            lb = math.log(M) + k * math.log(lam) + p * math.log(2 / (1 - r)) + math.lgamma(p + 1)
            lf = log_abs(f_val(H[k], k, t)) if peval(H[k], t) != 0 else -1e9
            slack.append(lb - lf)
            ok = ok and lf <= lb - 1e-9
        worst[str(t)] = round(min(slack), 2)
    report('b7-upper', ok, '显式上界在 t=-1/2, 1/2, -9/10, 9/10 对 0<=k<=%d 成立（log 余量最小值 %s）' % (K, worst))
    # b7-lower
    Tab2 = U_fast_table(40, 12)
    ok = all(Tab2[k][m] >= m ** (k // 3) for k in range(0, 41) for m in range(1, 13))
    for t in (Fr(1, 2), Fr(9, 10)):
        L = -math.log(float(t))
        for k in range(3, K + 1):
            j = k // 3
            lb = math.log(float(t)) + math.lgamma(j + 1) - 1 - 0.5 * math.log(j) - j * math.log(L)
            ok = ok and log_abs(f_val(H[k], k, t)) >= lb
    report('b7-lower', ok, 'U_k(m) >= m^floor(k/3)（k<=40, m<=12）；f_k(t) 的下界在 t=1/2, 9/10 对 3<=k<=%d 成立' % K)
    # b7-growth（记录）
    vals = {k: math.exp(log_abs(f_val(H[k], k, Fr(-1, 2))) / k) for k in (75, 150, 300)}
    report('b7-growth', vals[150] / vals[75] > 1.1 and vals[300] / vals[150] > 1.1,
           '|f_k(-1/2)|^(1/k)：k=75 %.4f，k=150 %.4f，k=300 %.4f（相邻比 %.3f、%.3f；2^(1/3)=%.3f）'
           % (vals[75], vals[150], vals[300], vals[150] / vals[75], vals[300] / vals[150], 2 ** (1 / 3)))
    print('time %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
    n_pass = sum(RESULTS)
    n_fail = len(RESULTS) - n_pass
    print('SUMMARY b7 pass=%d fail=%d' % (n_pass, n_fail))
    sys.exit(0 if n_fail == 0 else 1)
