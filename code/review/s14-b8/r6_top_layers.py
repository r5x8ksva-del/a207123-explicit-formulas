# -*- coding: utf-8 -*-
"""复核者 s14-b8（附带，属于「可推进的思路」）：靠近 s_k 的几层 j=s_k+1..s_k+10 对很大的 k 也不为零。

记 a_r(j):=[x^{3j-3-r}]G_{-j}=U_{3j-3-r}(-j)（r>=0），则 j-s_k=ceil((r+1)/3)（k=3j-3-r）。由 G_{-j-1}=(1-x+jx^3)G_{-j}+jx^2，
  a_r(j+1) = j·a_r(j) - a_{r-2}(j) + a_{r-3}(j)（3j-r≠2 时），即 b_r:=a_r/(j-1)! 满足 b_r(j+1)=b_r(j)+(b_{r-3}(j)-b_{r-2}(j))/j，
是嵌套调和和。这里：t-closed  r<=5 时与 c5a 定理 4.3 的闭式（Stirling 数）一致（j<=200）；t-rec  递推与完整 G_{-j} 一致（j<=80）；
t-nonzero  r<=29、j<=JT 时 a_r(j)!=0（覆盖 k 到 3JT），并报告每个 r 的 b_r(j) 最后一次变号的位置。
用法：py -3.14 code/review/s14-b8/r6_top_layers.py [JT=20000]
"""
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

JT = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
R = 29
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


T0 = time.time()
# 完整的 G_{-j}（不截断），j<=80
JF = 80
G = {1: [1]}
g = [1]
for j in range(1, JF):
    new = [0] * (len(g) + 3)
    for n in range(len(new)):
        v = (g[n] if n < len(g) else 0) - (g[n - 1] if 0 <= n - 1 < len(g) else 0)
        v += j * (g[n - 3] if 0 <= n - 3 < len(g) else 0)
        if n == 2:
            v += j
        new[n] = v
    while len(new) > 1 and new[-1] == 0:
        new.pop()
    g = new
    G[j + 1] = g
ok_deg = all(len(G[j]) - 1 == 3 * j - 3 for j in range(1, JF + 1))


def a_full(r, j):
    n = 3 * j - 3 - r
    return G[j][n] if 0 <= n < len(G[j]) else 0


# 无符号第一类 Stirling 数 c(n,k)
C = [[0] * 5 for _ in range(201)]
C[0][0] = 1
for n in range(1, 201):
    for k in range(0, 5):
        C[n][k] = (n - 1) * C[n - 1][k] + (C[n - 1][k - 1] if k >= 1 else 0)
ok_cl = True
for j in range(3, JF + 1):
    f = math.factorial(j - 1)
    cl = [f, f, -C[j][2], f, C[j][2] + C[j][3], f - C[j][2] - C[j][3]]
    ok_cl &= all(a_full(r, j) == cl[r] for r in range(6))
report('t-closed', ok_cl and ok_deg, 'deg G_{-j}=3j-3（j<=%d）%s；r<=5 的顶端系数 = c5a 定理 4.3 的 Stirling 闭式（3<=j<=%d）%s' % (JF, ok_deg, JF, ok_cl))

# 递推
j0 = R + 5
a = [a_full(r, j0) for r in range(R + 1)]
ok_rec = True
last_change = [None] * (R + 1)
prev_sign = [0] * (R + 1)
zeros = []
for r in range(R + 1):
    prev_sign[r] = (a[r] > 0) - (a[r] < 0)
for j in range(j0, JT):
    na = []
    for r in range(R + 1):
        v = j * a[r] - (a[r - 2] if r >= 2 else 0) + (a[r - 3] if r >= 3 else 0)
        na.append(v)
    a = na
    jj = j + 1
    if jj <= JF:
        ok_rec &= all(a[r] == a_full(r, jj) for r in range(R + 1))
    for r in range(R + 1):
        sg = (a[r] > 0) - (a[r] < 0)
        if sg == 0:
            zeros.append((r, jj))
        elif sg != prev_sign[r]:
            last_change[r] = jj
            prev_sign[r] = sg
    if jj % 5000 == 0:
        print('  j=%d (%.0fs)' % (jj, time.time() - T0), flush=True)
report('t-rec', ok_rec, '顶端系数递推 a_r(j+1)=j a_r(j)-a_{r-2}(j)+a_{r-3}(j) 与完整 G_{-j} 一致（r<=%d，%d<=j<=%d）' % (R, j0, JF))
report('t-nonzero', not zeros,
       'r<=%d、%d<=j<=%d 时 a_r(j)=U_{3j-3-r}(-j)!=0（即 j-s_k<=10 的各层，k 到 %d）；零点 %s；各 r 的最后一次变号 j：%s；'
       '终值符号（r=0..%d）：%s'
       % (R, j0, JT, 3 * JT - 3, zeros[:5] or '无', last_change, R, ''.join('+' if s > 0 else '-' for s in prev_sign)))
print('total %.0fs' % (time.time() - T0))
n_pass = sum(RES)
print('SUMMARY s14-b8-r6 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
sys.exit(0 if n_pass == len(RES) else 1)
