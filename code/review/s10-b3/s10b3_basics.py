# -*- coding: utf-8 -*-
"""s10-b3 检查 1：真值、§2(1) 的母函数恒等式、α+β=1 的构造（充分性）。

B1 自写 DP 与暴力枚举一致（m<=3，k<=8）。
B2 自写 DP 与 W_m/P_m 的级数展开一致（m<=5，k<=40）——即论文定理 3.1 的 G_m=W_m/P_m。
B3 §2(1)：对 β s+d>=0，sum_{k in Z} C(k+c-αs, βs+d) x^k = x^{e_s}(1-x)^{-(βs+d+1)}，e_s=(α+β)s+d-c；
   对 βs+d<0 全部系数为 0（按论文约定，a<0 也取 0）。k 在 [-40,60] 上逐项比较。
B4 (0,1) 形状：Newton 级数 U_k=sum_s Δ^s U(0) C(k,s)（c=d=0，k>=0），m<=4，k<=40。
B5 (1,0) 形状：U_k=sum_{s<=k} A(s) C(k-s,0)，A(s)=U_s-U_{s-1}（c=d=0）；
   以及 d>=1 时 A=x^{c-d}(1-x)^{d+1}G_m 的系数给出的表示（m<=3，c∈[-2,2]，d∈[0,3]）。
B6 正对照：不以上升结尾的部分 U-U^up = sum_s S(m+s,m) C(k+m-2s, m+s)（论文定理 6.2 前的说明），m<=4，k<=40。
"""
import sys
from fractions import Fraction
from s10b3_common import (binom, U_dp, U_up_dp, U_brute, P_poly, W_poly, series_div)

results = []


def report(tag, ok, info=""):
    results.append((tag, ok))
    print(("PASS " if ok else "FAIL ") + tag + ("  " + info if info else ""))


# B1
ok = True
for m in range(0, 4):
    u = U_dp(m, 8)
    for k in range(0, 9):
        if U_brute(m, k) != u[k]:
            ok = False
report("B1 DP=brute (m<=3,k<=8)", ok)

# B2
ok = True
for m in range(0, 6):
    u = U_dp(m, 40)
    s = series_div(W_poly(m), P_poly(m), 40)
    if u != s:
        ok = False
        print("  mismatch m=%d" % m)
report("B2 DP=series(W_m/P_m) (m<=5,k<=40)", ok)


# B3
def neg_binom_coeff(n, j):
    """[x^j](1-x)^{-(n+1)} = C(j+n, n), j>=0, n>=0。"""
    return binom(j + n, n)


ok = True
cnt = 0
for alpha in range(0, 5):
    for beta in range(0, 5):
        if alpha == 0 and beta == 0:
            continue
        for c in range(-3, 4):
            for d in range(-3, 4):
                for s in range(-4, 5):
                    n = beta * s + d
                    e = (alpha + beta) * s + d - c
                    for k in range(-40, 61):
                        lhs = binom(k + c - alpha * s, n)
                        if n < 0:
                            rhs = 0
                        else:
                            rhs = neg_binom_coeff(n, k - e) if k >= e else 0
                        cnt += 1
                        if lhs != rhs:
                            ok = False
report("B3 GF identity of each term (%d coefficient comparisons)" % cnt, ok)

# B4
ok = True
for m in range(1, 5):
    u = U_dp(m, 40)
    # Newton 系数 A(s)=Δ^s u(0)
    A = []
    row = u[:]
    for s in range(41):
        A.append(row[0])
        row = [row[i + 1] - row[i] for i in range(len(row) - 1)]
    for k in range(41):
        if sum(A[s] * binom(k, s) for s in range(41)) != u[k]:
            ok = False
report("B4 (0,1) Newton series reproduces U (m<=4,k<=40)", ok)

# B5
ok = True
for m in range(1, 5):
    u = U_dp(m, 40)
    A = [u[0]] + [u[s] - u[s - 1] for s in range(1, 41)]
    for k in range(41):
        if sum(A[s] * binom(k - s, 0) for s in range(41)) != u[k]:
            ok = False
# d>=1：A(x)=x^{c-d}(1-x)^{d+1}G_m，A(s)=[x^{s-(c-d)}](1-x)^{d+1}G_m
for m in range(1, 4):
    u = U_dp(m, 60)
    for c in range(-2, 3):
        for d in range(0, 4):
            # (1-x)^{d+1}G_m 的系数
            onemx = [(-1) ** j * binom(d + 1, j) for j in range(d + 2)]
            g = [sum(onemx[j] * u[t - j] for j in range(len(onemx)) if t - j >= 0) for t in range(61)]
            s0 = c - d
            A = {s0 + t: g[t] for t in range(61)}
            for k in range(0, 40):
                rhs = sum(a * binom(k + c - s, d) for s, a in A.items())
                if rhs != u[k]:
                    ok = False
report("B5 (1,0) partial sums and d>=1 constructions reproduce U", ok)


# B6
def stirling2(n, k):
    S = [[0] * (k + 1) for _ in range(n + 1)]
    S[0][0] = 1
    for i in range(1, n + 1):
        for j in range(1, min(i, k) + 1):
            S[i][j] = j * S[i - 1][j] + S[i - 1][j - 1]
    return S[n][k]


ok = True
for m in range(1, 5):
    u = U_dp(m, 40)
    up = U_up_dp(m, 40)
    for k in range(41):
        rhs = sum(stirling2(m + s, m) * binom(k + m - 2 * s, m + s) for s in range(0, k + 1))
        if rhs != u[k] - up[k]:
            ok = False
report("B6 U-U^up = sum S(m+s,m) C(k+m-2s,m+s) (m<=4,k<=40)", ok)

nf = sum(1 for _, o in results if not o)
print("SUMMARY basics: %d PASS, %d FAIL" % (len(results) - nf, nf))
sys.exit(1 if nf else 0)
