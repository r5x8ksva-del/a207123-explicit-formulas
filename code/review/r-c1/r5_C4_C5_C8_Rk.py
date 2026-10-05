# -*- coding: utf-8 -*-
"""r-c1 独立复核 5：(C4)、(C5)、(C8)、R_k 与 OEIS A038718（C4-c、C4-S、C4-generalized、C4-pf、C4-theta、C5、C8、Rk-OEIS）。

真值：自写高度 DP（k<=80,m<=25；k<=60,m<=66）；OEIS 只读快照 data/oeis/b038718.txt（不联网）。
"""
import os
import sys
import time
from fractions import Fraction
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, HERE)
from rc1lib import (U_table, Reporter, trim, add, sub, scal, mul, ev, bpoly, ser_inv, ser_mul, bm_mod,  # noqa: E402
                    stirling2, binom0, poly_shift_arg)

rep = Reporter('r-c1-C4-C5-C8-Rk')
T0 = time.time()
KA, MA = 80, 25
TA = U_table(KA, MA)
TB = U_table(60, 66)
print('INFO DP tables [%.1fs]' % (time.time() - T0), flush=True)

# ---------------- C4 ----------------
NCMAX = KA + 1 + 3 * MA + 5
CT = [[sum(binom0(n - 2 * j, j) * i ** j for j in range(0, n // 3 + 1)) for n in range(NCMAX + 1)] for i in range(MA + 1)]
t = time.time()
bad = [i for i in range(MA + 1) if CT[i] != ser_inv(bpoly(i), NCMAX + 1)]
rep('C4a-c', not bad, '(C4) c_i(n)=sum_{0<=j<=n/3}C(n-2j,j)i^j（0^0=1）== [x^n]1/(1-x-i x^3)（级数求逆），0<=i<=25, 0<=n<=%d [%.1fs] %s'
    % (NCMAX, time.time() - t, bad[:3]))

PC = {-1: [1]}
for i in range(0, MA + 1):
    PC[i] = mul(PC[i - 1], bpoly(i))
INVP = {m: ser_inv(PC[m], KA + 2) for m in range(MA + 1)}
S2 = stirling2(2 * MA + KA)
t = time.time()
bad = [(m, n) for m in range(MA + 1) for n in range(KA + 2)
       if INVP[m][n] != sum(S2[s + m][m] * binom0(n + m - 2 * s, m + s) for s in range(0, n // 3 + 1))]
rep('C4b-S', not bad, '(C4) [x^n]1/P_m = sum_{0<=s<=n/3} S(m+s,m)C(n+m-2s,m+s)，0<=m<=25, 0<=n<=81 [%.1fs] %s' % (time.time() - t, bad[:3]))


def gbin(a, b):
    num = 1
    for i in range(b):
        num *= (a - i)
    return Fraction(num, factorial(b))


g1 = S2[2][1] * gbin(0 + 1 - 2, 1 + 1)
g2 = S2[3][1] * gbin(0 + 1 - 4, 1 + 2)
cg = sum(gbin(1 - 2 * j, j) * 5 ** j for j in range(0, 2))
# 再找一个「广义二项式 + 全部 s>=0 求和到 s<=n+m」也失败的例子：m=2,n=1
alt = sum(S2[s + 2][2] * gbin(1 + 2 - 2 * s, 2 + s) for s in range(0, 4))
rep('C4c-generalized-refuted', g1 == 1 and g2 == -10 and cg == -4 and INVP[1][0] == 1 and CT[5][1] == 1,
    '(C4 约定) 按广义二项式把求和推到 n/3 以外会出错：m=1,n=0 时 s=1 项=%s、s=2 项=%s；c_5(1) 变为 %s（真值 %s）；'
    '另 m=2,n=1 时 s<=3 的广义和=%s（真值 %s）' % (g1, g2, cg, CT[5][1], alt, INVP[2][1]))

t = time.time()
bad = []
for m in range(MA + 1):
    fm = factorial(m)
    for n in range(-3 * m, KA + 2):
        tot = sum((-1) ** (m - i) * comb(m, i) * CT[i][n + 3 * m] for i in range(m + 1))
        if tot != (fm * INVP[m][n] if n >= 0 else 0):
            bad.append((m, n))
rep('C4d-pf', not bad, '(C4) m![x^n]1/P_m = sum_i(-1)^{m-i}C(m,i)c_i(n+3m)，0<=m<=25, 0<=n<=81；-3m<=n<0 时右边为 0 [%.1fs] %s'
    % (time.time() - t, bad[:3]))


def theta(m, tt, n):
    return Fraction(sum((-1) ** r * comb(tt, r) * CT[m - r][n] for r in range(tt + 1)), factorial(tt))


t = time.time()
bad, nonint = [], 0
for m in range(MA + 1):
    for k in range(KA + 1):
        main = theta(m, m, k + 1 + 3 * m)
        rest = [theta(m, tt, k + 3 * tt) for tt in range(m)]
        nonint += sum(1 for v in [main] + rest if v.denominator != 1)
        if main - sum(rest) != TA[k][m]:
            bad.append((k, m))
# 中间恒等式
for m in range(MA + 1):
    for tt in range(m + 1):
        den = [1]
        for i in range(m - tt, m + 1):
            den = mul(den, bpoly(i))
        inv = ser_inv(den, KA + 1)
        if any(theta(m, tt, k + 3 * tt) != inv[k] for k in range(KA + 1)):
            bad.append(('mid', m, tt))
rep('C4e-theta', not bad and nonint == 0, '(C4) U_k(m)=Θ_m(k+1+3m)-sum_{t<m}Θ_t(k+3t) 对自写 DP：0<=k<=80（含 k=0）, 0<=m<=25，全部 Θ 为整数；'
    'Θ_t(k+3t)=[x^k]prod_{i=m-t}^m b_i^{-1}，0<=t<=m<=25, k<=80 [%.1fs] %s' % (time.time() - t, bad[:3]))

# ---------------- C5 ----------------
t = time.time()
bad = []
for k in range(KA + 1):
    for m in range(MA + 1):
        lhs = TA[k][m] - (TA[k - 1][m] if k >= 1 else 0) - (TA[k][m - 1] if m >= 1 else 0) - (m * TA[k - 3][m] if k >= 3 else 0)
        rhs = (1 if (k == 0 and m == 0) else 0) + (m if k == 2 else 0)
        if lhs != rhs:
            bad.append((k, m))
rep('C5-pde', not bad, '(C5) [x^k t^m]{(1-x-t)F - x^3 t F_t} == [x^k t^m]{1 + x^2 t/(1-t)^2}，0<=k<=80, 0<=m<=25（F 取自写 DP） [%.1fs] %s'
    % (time.time() - t, bad[:3]))

# ---------------- C8 ----------------
t = time.time()
s1t = [[0] * 62 for _ in range(62)]
s1t[0][0] = 1
for j in range(1, 62):
    for i in range(1, j + 1):
        s1t[j][i] = s1t[j - 1][i - 1] - (j - 1) * s1t[j - 1][i]


def upoly(k):
    vals = [TB[k][m] for m in range(k + 1)]
    cur, d = vals[:], []
    for j in range(k + 1):
        d.append(cur[0])
        cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
    poly = [Fraction(0)] * (k + 1)
    for j in range(k + 1):
        if d[j]:
            c = Fraction(d[j], factorial(j))
            for i in range(j + 1):
                poly[i] += c * s1t[j][i]
    return trim(poly)


def compose_lin(p, a, b):
    """p(a*n+b) 作为 n 的多项式。"""
    out = []
    pw = [Fraction(1)]
    for c in p:
        out = add(out, scal(pw, c))
        pw = mul(pw, [Fraction(b), Fraction(a)])
    return out


bad = []
for k in range(1, 21):
    u = upoly(k)
    c = u[-1]
    E = mul(compose_lin(u, Fraction(1, 2), 0), compose_lin(u, Fraction(1, 2), 0))
    O = mul(compose_lin(u, Fraction(1, 2), Fraction(1, 2)), compose_lin(u, Fraction(1, 2), Fraction(-1, 2)))
    p = scal(add(E, O), Fraction(1, 2))
    q = scal(sub(E, O), Fraction(1, 2))
    if len(p) - 1 != 2 * k or len(q) - 1 != 2 * k - 2:
        bad.append(('deg', k))
        continue
    if p[-1] != c * c / 4 ** k or q[-1] != c * c * k / (2 * 4 ** k):
        bad.append(('lc', k))
    for n in range(0, 4 * k + 21):
        if ev(p, n) + (-1) ** n * ev(q, n) != TB[k][(n + 1) // 2] * TB[k][n // 2]:
            bad.append(('val', k, n))
            break
rep('C8a-pq', not bad, '(C8) 由精确 u_k 复合得到 p=(E+O)/2,q=(E-O)/2：deg p=2k、deg q=2k-2、lc p=c^2/4^k、lc q=c^2 k/(2*4^k)，'
    '且 p(n)+(-1)^n q(n)=U_k(ceil(n/2))U_k(floor(n/2)) 对 n<=4k+20，1<=k<=20 [%.1fs] %s' % (time.time() - t, bad[:3]))

t = time.time()
bad = []
P1 = 1_000_000_007
for k in range(1, 15):
    seq = [TB[k][(n + 1) // 2] * TB[k][n // 2] for n in range(0, 8 * k + 20)]
    C, L = bm_mod(seq, P1)
    target = [1]
    for _ in range(2 * k + 1):
        target = mul(target, [1, -1])
    for _ in range(2 * k - 1):
        target = mul(target, [1, 1])
    if L != 4 * k or C != [x % P1 for x in target]:
        bad.append((k, L))
rep('C8b-order', not bad, '(C8/A 推导链的数据核对) 模 1e9+7 的 BM 作用于 a_k(n)（n<=8k+19）：线性复杂度恰为 4k，连接多项式 ≡ (1-x)^{2k+1}(1+x)^{2k-1}，1<=k<=14 '
    '[%.1fs] %s' % (time.time() - t, bad[:3]))

# ---------------- Rk 与 OEIS ----------------
t = time.time()
bfile = os.path.join(ROOT, 'data', 'oeis', 'b038718.txt')
A = {}
with open(bfile, encoding='utf-8') as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        a, b = line.split()
        A[int(a)] = int(b)
R = [TB[k][1] for k in range(61)]
Rrec = [1, 2, 4]
while len(Rrec) < max(A) - 1:
    k = len(Rrec)
    Rrec.append(1 + Rrec[k - 1] + Rrec[k - 3])
ok_dp = all(R[k] == A[k + 2] for k in range(61))
ok_rec = all(Rrec[k] == A[k + 2] for k in range(len(Rrec)) if k + 2 in A)
nrec = sum(1 for k in range(len(Rrec)) if k + 2 in A)
ok_alt = all(R[k] == A[k + 1] for k in range(1, 20))
rep('Rk-OEIS', ok_dp and ok_rec and not ok_alt, 'R_k = A038718(k+2)（快照 b038718.txt，offset 1）：DP 值 k<=60 一致；由已证明的 R_k=1+R_{k-1}+R_{k-3} 推出的 k<=%d 全部一致；'
    'A038718(k+1) 不成立：%s [%.1fs]' % (nrec - 1, not ok_alt, time.time() - t))

print('TIME r5 total %.1fs' % (time.time() - T0), flush=True)
sys.exit(0 if rep.summary() else 1)
