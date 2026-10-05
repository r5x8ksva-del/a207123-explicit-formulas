# -*- coding: utf-8 -*-
"""r-c1 独立复核 4：(C3)、(C6)、(C7)（C3-basis、C3-tri、C3-init、C3-diag、C3-subdiag、C6、C6-explicit、C7、C7-rec）。

N(k,q) 的三种来源：
  NO  「序型 DP」（与 c1 完全不同的算法）：逐个字母构造词，状态 = (已用不同值个数 q, 倒数第二个字母的秩, 最后一个字母的秩)，
      下一个字母要么取已有的某个秩，要么插入到 q+1 个空隙之一成为新值（其余秩相应平移），三元组条件按秩判断。
      每个值域恰为 {1..q} 的合法词恰对应一条路径，所以终态按 q 求和就是 N(k,q)。k<=28。
  NB  DFS 按定义枚举（自写），k<=9
  NI  容斥 N(k,q)=sum_i (-1)^{q-i}C(q,i)U_k(i-1)（U 取自写 DP），k<=100
"""
import os
import sys
import time
from math import comb, factorial
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rc1lib import (good, U_table, Reporter, trim, add, sub, scal, mul, shiftx, ev, deriv, bpoly, ser_mul)  # noqa: E402

rep = Reporter('r-c1-C3-C6-C7')
T0 = time.time()
TA = U_table(60, 62)
TB = U_table(100, 22)
print('INFO DP tables [%.1fs]' % (time.time() - T0), flush=True)


def NI(T, k, q):
    s = 0
    for i in range(q + 1):
        u = (1 if k == 0 else 0) if i == 0 else T[k][i - 1]
        s += (-1) ** (q - i) * comb(q, i) * u
    return s


KN = 60
NIT = [[NI(TA, k, q) for q in range(0, 64)] for k in range(KN + 1)]


def Nv(k, q):
    if k < 0 or q < 0 or q > 63:
        return 0
    return NIT[k][q]


# ---------------- 序型 DP ----------------
def N_ordertype(K):
    res = {0: {0: 1}, 1: {1: 1}}
    st = defaultdict(int)
    st[(1, 1, 1)] += 1
    st[(2, 1, 2)] += 1
    st[(2, 2, 1)] += 1
    if K >= 2:
        d = defaultdict(int)
        for (q, r1, r2), v in st.items():
            d[q] += v
        res[2] = dict(d)
    for k in range(3, K + 1):
        new = defaultdict(int)
        for (q, r1, r2), v in st.items():
            for s in range(1, q + 1):                     # 取已有值
                if good(r1, r2, s):
                    new[(q, r2, s)] += v
            for g in range(0, q + 1):                     # 插入新值（成为秩 g+1）
                a = r1 + (1 if r1 > g else 0)
                b = r2 + (1 if r2 > g else 0)
                s = g + 1
                if good(a, b, s):
                    new[(q + 1, b, s)] += v
        st = new
        d = defaultdict(int)
        for (q, r1, r2), v in st.items():
            d[q] += v
        res[k] = dict(d)
    return res


t = time.time()
KO = 28
NO = N_ordertype(KO)
tO = time.time() - t


def N_dfs(k):
    res = defaultdict(int)
    if k == 0:
        return {0: 1}
    seq = []

    def rec():
        if len(seq) == k:
            s = set(seq)
            if s == set(range(len(s))):
                res[len(s)] += 1
            return
        for v in range(k):
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec()
            seq.pop()
    rec()
    return dict(res)


t = time.time()
bad = []
for k in range(0, 10):
    nb = N_dfs(k)
    if any(nb.get(q, 0) != NO[k].get(q, 0) for q in range(0, k + 2)):
        bad.append(('dfs-vs-ot', k))
for k in range(0, KO + 1):
    if any(NO[k].get(q, 0) != NIT[k][q] for q in range(0, 64)):
        bad.append(('ot-vs-ie', k))
# 二项式基：用序型 DP 的 N（与 U 无关）重建 U
for k in range(0, KO + 1):
    for m in range(0, 63):
        if TA[k][m] != sum(NO[k].get(q, 0) * comb(m + 1, q) for q in range(0, k + 1)):
            bad.append(('basis', k, m))
            break
# 容斥值的零值与 k<=60 的二项式基（这一项本质上是容斥的反演，只作一致性检查）
for k in range(0, KN + 1):
    for q in range(0, 64):
        if (q > k or (q == 0 and k >= 1)) and NIT[k][q] != 0:
            bad.append(('zero', k, q))
    for m in range(0, 63):
        if TA[k][m] != sum(NIT[k][q] * comb(m + 1, q) for q in range(0, k + 1)):
            bad.append(('basis-ie', k, m))
            break
rep('C3a-basis', not bad, '(C3) N 的组合意义与二项式基：DFS 定义（k<=9）== 序型 DP（k<=28，独立算法 %.1fs）== 容斥；'
    '用序型 DP 的 N 重建 U_k(m)=sum_q N(k,q)C(m+1,q)，k<=28,m<=62；容斥 N 的零值 N(k,q)=0（q>k 或 q=0<k）与基展开 k<=60,m<=62 [%.1fs] %s'
    % (tO, time.time() - t, bad[:3]))

t = time.time()
bad = []
for k in range(3, KN + 1):
    for r in range(0, k + 1):
        if Nv(k, r + 1) != Nv(k - 1, r) + Nv(k - 1, r + 1) + r * (Nv(k - 3, r - 1) + 2 * Nv(k - 3, r) + Nv(k - 3, r + 1)):
            bad.append((k, r))
for k in range(3, KO + 1):            # 也对序型 DP 的 N 检查（与 U 无关）
    for r in range(0, k + 1):
        n_ = lambda kk, qq: NO[kk].get(qq, 0) if kk >= 0 and qq >= 0 else 0  # noqa: E731
        if n_(k, r + 1) != n_(k - 1, r) + n_(k - 1, r + 1) + r * (n_(k - 3, r - 1) + 2 * n_(k - 3, r) + n_(k - 3, r + 1)):
            bad.append(('ot', k, r))
rep('C3b-tri', not bad, '(C3) 三角递推 N(k,r+1)=N(k-1,r)+N(k-1,r+1)+r[N(k-3,r-1)+2N(k-3,r)+N(k-3,r+1)]：容斥 N 3<=k<=60；序型 DP 的 N 3<=k<=28；0<=r<=k [%.1fs] %s'
    % (time.time() - t, bad[:3]))

t = time.time()


def Ne(k, q):
    if k == -1:
        return 1 if q == 0 else 0
    if k < -1 or q < 0:
        return 0
    return Nv(k, q)


zero_bd = Nv(1, 1) + Nv(1, 2) + 1 * 0
ext = all(Ne(k, r + 1) == Ne(k - 1, r) + Ne(k - 1, r + 1) + r * (Ne(k - 3, r - 1) + 2 * Ne(k - 3, r) + Ne(k - 3, r + 1))
          for k in range(1, KN + 1) for r in range(0, k + 1))
rep('C3c-init', zero_bd == 1 and Nv(2, 2) == 2 and ext, '(C3 初值) k=2,r=1 用零边界得 %d≠N(2,2)=%d；约定 N(-1,0)=1,N(-1,q>=1)=0,N(-2,.)=0 时递推对 1<=k<=60 成立：%s'
    % (zero_bd, Nv(2, 2), ext))

d1 = all(Nv(k, k) == 2 for k in range(2, KN + 1))
d2 = all(Nv(k, k - 1) == k * k - k - 4 for k in range(4, KN + 1))
d3 = Nv(3, 2) == 4 and Nv(1, 1) == 1 and all(NO[k].get(k, 0) == 2 for k in range(2, KO + 1)) and \
    all(NO[k].get(k - 1, 0) == k * k - k - 4 for k in range(4, KO + 1))
# 组合解释：合法排列恰为 w_1>...>w_{k-1} 且 w_k ∈ {1,2}（k>=3），对 k<=8 全枚举排列核对
from itertools import permutations  # noqa: E402
d4 = True
for k in range(3, 9):
    legal = [p for p in permutations(range(1, k + 1)) if all(good(p[i], p[i + 1], p[i + 2]) for i in range(k - 2))]
    expect = [p for p in permutations(range(1, k + 1)) if all(p[i] > p[i + 1] for i in range(k - 2)) and p[-1] in (1, 2)]
    if sorted(legal) != sorted(expect) or len(legal) != 2:
        d4 = False
rep('C3d-diag', d1 and d2 and d3 and d4, '(C3) N(k,k)=2（2<=k<=60）；N(k,k-1)=k^2-k-4（4<=k<=60）；N(3,2)=4；序型 DP 同样成立（k<=28）；'
    '合法排列 == {w_1>...>w_{k-1}, w_k∈{1,2}}（3<=k<=8 全枚举） [%s %s %s %s]' % (d1, d2, d3, d4))

# ---------------- C6 ----------------
t = time.time()
H = {0: [1], 1: [1], 2: [1, 1]}
for k in range(3, KN + 1):
    inner = add(mul([1, -1], deriv(H[k - 3])), scal(H[k - 3], k - 2))
    H[k] = add(H[k - 1], mul([0, 1, -1], inner))
pw = [[1]]
for _ in range(KN + 3):
    pw.append(mul(pw[-1], [1, -1]))
bad = []
for k in range(1, KN + 1):
    hN = []
    for q in range(1, k + 1):
        hN = add(hN, scal(shiftx(pw[k - q], q - 1), NIT[k][q]))
    if hN != H[k]:
        bad.append(('N', k))
for k in range(0, KN + 1):
    ser = ser_mul(pw[k + 1], [TA[k][m] for m in range(63)], 63)
    if trim(ser) != H[k] or (k >= 1 and len(H[k]) - 1 > k - 1):
        bad.append(('DP', k))
rep('C6a-h', not bad, '(C6) h_k 三种算法一致：递推（h_0=1,h_1=1,h_2=1+t）；N 表达式（1<=k<=60）；(1-t)^{k+1}sum_{m<=62}U_k(m)t^m（截断到 t^62，'
    '其余系数为 0，deg h_k<=k-1），0<=k<=60 [%.1fs] %s' % (time.time() - t, bad[:3]))

given = {3: [1, 2, -1], 4: [1, 4, -3], 5: [1, 8, -5, -2], 6: [1, 14, -7, -8, 2]}
e1 = all(H[k] == v for k, v in given.items())
e2 = all(ev(H[k], 1) == 2 for k in range(2, KN + 1)) and ev(H[1], 1) == 1
rep('C6b-explicit', e1 and e2, '(C6) h_3..h_6 显式值；h_k(1)=2（2<=k<=60），h_1(1)=1 [%s %s]' % (e1, e2))

# ---------------- C7 ----------------
t = time.time()
PC = {-1: [1]}
for i in range(0, 30):
    PC[i] = mul(PC[i - 1], bpoly(i))
WC = {-1: [1], 0: [1]}
for m in range(1, 30):
    WC[m] = add(WC[m - 1], shiftx(scal(PC[m - 1], m), 2))
KQ, QMAX = 100, 22
NUM = {}
bad = []
for q in range(1, QMAX + 1):
    ser = [NI(TB, k, q) for k in range(KQ + 1)]
    num = ser_mul(PC[q - 1], ser, KQ + 1)
    d = 3 * q - 2
    if any(num[d + 1:]):
        bad.append(('notpoly', q))
    poly = trim(num[:d + 1])
    NUM[q] = poly
    if len(poly) - 1 != d or poly[-1] != factorial(q - 1):
        bad.append(('deg/lc', q))
    low = next(i for i, c in enumerate(poly) if c)
    if (q == 1 and (low, poly[low]) != (1, 1)) or (q >= 2 and (low, poly[low]) != (q, 2)):
        bad.append(('low', q))
given = {1: [0, 1], 2: [0, 0, 2, 0, 1], 3: [0, 0, 0, 2, 2, 7, 0, 2], 4: [0, 0, 0, 0, 2, 8, 13, 15, 29, 0, 6]}
if any(NUM[q] != v for q, v in given.items()):
    bad.append('given')
rep('C7a-num', not bad, '(C7) Num_q=P_{q-1} sum_k N(k,q)x^k（N 取容斥，k<=100）：x^{3q-1}..x^100 系数全为 0，次数恰 3q-2，首项 (q-1)!，'
    '最低项 2x^q（q>=2）/ x（q=1），1<=q<=22；q=1..4 的给定分子 [%.1fs] %s' % (time.time() - t, bad[:3]))

t = time.time()
bad = []
for q in range(1, QMAX + 1):
    tot = []
    for i in range(0, q + 1):
        pr = [1]
        for v in range(i, q):
            pr = mul(pr, bpoly(v))
        tot = add(tot, scal(mul(WC[i - 1], pr), (-1) ** (q - i) * comb(q, i)))
    if tot != NUM[q]:
        bad.append(('ie', q))
for q in range(3, QMAX + 1):
    rhs = add(mul([0, 1, 0, 2 * (q - 1)], NUM[q - 1]), mul(scal(shiftx(bpoly(q - 2), 3), q - 1), NUM[q - 2]))
    if rhs != NUM[q]:
        bad.append(('rec', q))
# q=2 处三项递推的修正项（说明为什么 Num_2 要单给）
r2 = add(mul([0, 1, 0, 2], NUM[1]), mul(scal(shiftx(bpoly(0), 3), 1), [1]))
rep('C7b-ie-rec', not bad, '(C7) 容斥式 Num_q=sum_i(-1)^{q-i}C(q,i)W_{i-1}prod_{v=i}^{q-1}b_v（1<=q<=22）与三项递推（3<=q<=22）精确成立；'
    '（q=2 若硬套递推并取 Num_0=1 得 %s ≠ Num_2=%s） [%.1fs] %s' % (r2, NUM[2], time.time() - t, bad[:3]))

print('TIME r4 total %.1fs' % (time.time() - T0), flush=True)
sys.exit(0 if rep.summary() else 1)
