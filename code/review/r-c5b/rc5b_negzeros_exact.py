# -*- coding: utf-8 -*-
"""r-c5b：把 c5b-32「U_k 的负整数零点恰为 -1..-floor((k+2)/3)」对每个 k<=K0 变成严格的有限验证。

方法（每个 k 都是完整证明，不依赖抽样范围）：
  1. P_k(m) := k!·U_k(m) = Σ_q N(k,q)·(k!/q!)·(m+1)m…(m+2-q) ∈ Z[m]，常数项 = k!·U_k(0) = k!。
     N(k,q) 由自写高度 DP 的 U_k(0..k-1) 容斥得到（T1）。
  2. 有理根定理：整数根 -j 必须整除常数项 k!，所以 j 的素因子都 <= k 且 v_p(j) <= v_p(k!)。
  3. Fujiwara 界：所有复根 |z| <= B_k := 2·max( |a_{k-i}/a_k|^{1/i} (1<=i<k), |a_0/(2a_k)|^{1/k} )。
  4. 枚举所有 j | k!、j <= B_k，精确计算 P_k(-j)。
同时报告 c5b 只检查到 j<=31 时漏掉的「大负实根」位置（数值，numpy，仅作说明）。
"""
import math
import os
import sys
import time
from math import comb, factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rc5b_lib as L  # noqa: E402

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass
K0 = int(sys.argv[1]) if len(sys.argv) > 1 else 60
t0 = time.time()


def primes_upto(n):
    s = [True] * (n + 1)
    s[0:2] = [False, False]
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = [False] * len(s[i * i::i])
    return [i for i in range(n + 1) if s[i]]


def vp_fact(n, p):
    v, q = 0, p
    while q <= n:
        v += n // q
        q *= p
    return v


def divisors_upto(k, B):
    ps = primes_upto(k)
    lim = {p: vp_fact(k, p) for p in ps}
    out = []

    def rec(i, cur):
        if i == len(ps):
            out.append(cur)
            return
        p = ps[i]
        x = cur
        for _ in range(lim[p] + 1):
            if x > B:
                break
            rec(i + 1, x)
            x *= p
    rec(0, 1)
    return out


def int_poly(k):
    col = [L.U(k, m) for m in range(k)]
    Nk = L.N_from_values(k, col)
    P = []
    kf = factorial(k)
    for q, v in Nk.items():
        p = [1]
        for i in range(q):
            p = L.pmul(p, [1 - i, 1])          # (m+1-i)
        P = L.padd(P, [c * v * (kf // factorial(q)) for c in p])
    return P                                   # 升幂整数系数


def logabs(x):
    return math.log(abs(x)) if x else -math.inf


def fujiwara(P):
    k = len(P) - 1
    la = logabs(P[k])
    best = -math.inf
    for i in range(1, k + 1):
        c = P[k - i]
        if c == 0:
            continue
        val = (logabs(c) - la - (math.log(2) if i == k else 0.0)) / i
        best = max(best, val)
    return 2 * math.exp(best) * 1.0001 + 1


def horner(P, x):
    r = 0
    for c in reversed(P):
        r = r * x + c
    return r


summary = []
maxB = 0
for k in range(1, K0 + 1):
    P = int_poly(k)
    assert len(P) == k + 1 and P[0] == factorial(k)
    # 额外点（m=k..k+5）与 DP 一致：确认 P_k = k!·U_k（插值只用了 m=-1..k-1）
    assert all(horner(P, m) == factorial(k) * L.U(k, m) for m in range(k, k + 6)), k
    r = (k + 2) // 3
    B = fujiwara(P)
    maxB = max(maxB, B)
    cands = [j for j in divisors_upto(k, B) if j >= 1]
    zeros = sorted(j for j in cands if horner(P, -j) == 0)
    assert zeros == list(range(1, r + 1)), (k, zeros)
    summary.append((k, r, int(B), len(cands)))

print('k, r=floor((k+2)/3), Fujiwara 界 B_k, 需检查的 j|k! 且 j<=B_k 个数：')
for row in summary:
    print('  k=%2d r=%2d B=%9d cand=%6d' % row)
print('结论：1<=k<=%d 时，U_k 的全部负整数零点恰为 -1..-floor((k+2)/3)（有理根定理 + Fujiwara 界，精确整数，完整证明）。' % K0)

# 说明：c5b 的检查范围 j<=31 不足以覆盖实根，举 U_7 为例
try:
    import numpy as np
    for k in (5, 6, 7, 10, 20, 30):
        P = int_poly(k)
        rts = np.roots([float(c) for c in reversed(P)])
        real_neg = sorted(z.real for z in rts if abs(z.imag) < 1e-6 * max(1, abs(z)) and z.real < 0)
        print('  U_%d 的负实根（数值）最小者 ≈ %.3f；负实根个数 %d' % (k, real_neg[0], len(real_neg)))
except Exception as ex:  # noqa
    print('numpy 说明部分跳过：%r' % ex)
print('max B = %d, time %.1fs' % (maxB, time.time() - t0))
