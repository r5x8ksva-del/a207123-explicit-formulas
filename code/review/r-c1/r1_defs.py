# -*- coding: utf-8 -*-
"""r-c1 独立复核 1：第 1 节归约 (a)(b)(c) 与基准数据（R-abc、BASE）。

全部自写，真值来自原题定义：
  D0  good <=> good_rows（逐行字面检查 001/010）<=> legal_next（DP 用的转移规则），全部 (a,b,c) in {0..40}^3
  D1  原题 n×k 矩阵的「全枚举」：行只取满足行规则的串（行规则是定义的一部分），所有 R_k^n 个组合逐个检查
      列三元组 001/011（位运算写法，另与逐列元组写法核对）；覆盖 R_k^n <= 1e6 的全部 (n,k)，与乘积公式比较
  D2  原题按行转移计数（状态 = 最后两行，列三元组字面检查），k<=8: n<=22；k=9,10: n<=16
  D3  自写多重链计数（允许行偏序集，逐分量序）== 高度 DP，k<=12, m<=20
  D4  高度向量直接枚举（每个三元组用 good_rows 字面检查）== 高度 DP，k<=6,m<=6；k=7,m<=5
  D5  与 core.U_height_table（第1节参考实现）、core.U_fast_table 的交叉对照：k<=132,m<=20；k<=60,m<=62
  D6  第 2 节表、R_1..R_10、a_3(1..6)
"""
import os
import sys
import time
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rc1lib import good, good_rows, legal_next, U_column, U_table, Reporter  # noqa: E402

rep = Reporter('r-c1-defs')
T0 = time.time()


def rows_of(k):
    """长度 k 的 0/1 串（元组，左到右），满足行规则：任何连续三位都不是 001、010。"""
    out = []
    for bits in product((0, 1), repeat=k):
        ok = True
        for i in range(k - 2):
            t = bits[i:i + 3]
            if t == (0, 0, 1) or t == (0, 1, 0):
                ok = False
                break
        if ok:
            out.append(bits)
    return out


def col_triple_ok(A, B, C):
    """三行 A,B,C（自上而下）在每一列都不是 001、也不是 011。"""
    for j in range(len(A)):
        t = (A[j], B[j], C[j])
        if t == (0, 0, 1) or t == (0, 1, 1):
            return False
    return True


# ---------------- D0 ----------------
t = time.time()
bad = []
for a in range(41):
    for b in range(41):
        for c in range(41):
            g = good(a, b, c)
            if g != good_rows(a, b, c) or g != legal_next(a, b, c):
                bad.append((a, b, c))
rep('D0-good', not bad, '(b) good(a,b,c) <=> 高度列逐行字面无 001/010 <=> DP 转移规则，全部 (a,b,c) in {0..40}^3 [%.1fs] %s'
    % (time.time() - t, bad[:3]))

# 公共：自写 DP 表
t = time.time()
TM = U_table(60, 66)          # k<=60, m<=66
TL = U_table(132, 30)         # k<=132, m<=30
print('INFO own DP tables built: k<=60,m<=66 and k<=132,m<=30 [%.1fs]' % (time.time() - t), flush=True)


def Uown(k, m):
    if k <= 60 and m <= 66:
        return TM[k][m]
    return TL[k][m]


# ---------------- D1 全枚举 ----------------
def to_mask(bits):
    """左起第 j 位 -> 二进制第 j 位。"""
    return sum(b << j for j, b in enumerate(bits))


def col_ok_mask(A, B, C, full):
    """三行（自上而下）A,B,C 的位掩码：任何一列都不是 001、也不是 011（逐列字面条件的位运算写法）。"""
    nA, nB = full & ~A, full & ~B
    bad001 = nA & nB & C
    bad011 = nA & B & C
    return (bad001 | bad011) == 0


t = time.time()
bad, pairs = [], []
ROWS = {k: rows_of(k) for k in range(1, 21)}
MASKS = {k: [to_mask(r) for r in ROWS[k]] for k in ROWS}
# 位运算写法与逐列元组写法的一致性（所有 k<=7 的允许行三元组）
mask_ok = all(col_ok_mask(to_mask(A), to_mask(B), to_mask(C), (1 << k) - 1) == col_triple_ok(A, B, C)
              for k in range(1, 6) for A in ROWS[k] for B in ROWS[k] for C in ROWS[k])
for k in range(1, 21):
    R = len(ROWS[k])
    n = 0
    while R ** n <= 1_000_000:
        pairs.append((n, k))
        n += 1
for (n, k) in pairs:
    ms = MASKS[k]
    full = (1 << k) - 1
    cnt = 0
    for M in product(ms, repeat=n):
        ok = True
        for i in range(n - 2):
            if not col_ok_mask(M[i], M[i + 1], M[i + 2], full):
                ok = False
                break
        if ok:
            cnt += 1
    if cnt != Uown(k, (n + 1) // 2) * Uown(k, n // 2):
        bad.append((n, k, cnt))
maxn = {}
for (n, k) in pairs:
    maxn[k] = max(maxn.get(k, 0), n)
rep('D1-full-enum', not bad and mask_ok, '(a)+(b) 原题矩阵全枚举（行取满足行规则的串，R_k^n<=1e6 的全部 %d 对 (n,k)，各 k 的最大 n=%s）'
    '== U_k(ceil(n/2))U_k(floor(n/2))；位运算列检查 == 逐列元组检查（k<=5 全部三元组）:%s [%.1fs] %s'
    % (len(pairs), dict(sorted(maxn.items())), mask_ok, time.time() - t, bad[:3]))


# ---------------- D2 按行转移 ----------------
def a_rows_dp_all(nmax, k):
    """一次算出 n=0..nmax。"""
    rows = ROWS[k]
    R = len(rows)
    out = [1, R]
    ms = MASKS[k]
    full = (1 << k) - 1
    nxt = [[[c for c in range(R) if col_ok_mask(ms[a], ms[b], ms[c], full)] for b in range(R)] for a in range(R)]
    cur = [[1] * R for _ in range(R)]
    out.append(R * R)
    for _ in range(3, nmax + 1):
        new = [[0] * R for _ in range(R)]
        for a in range(R):
            ca = cur[a]
            na = nxt[a]
            for b in range(R):
                v = ca[b]
                if v:
                    nb = new[b]
                    for c in na[b]:
                        nb[c] += v
        cur = new
        out.append(sum(map(sum, cur)))
    return out[:nmax + 1]


t = time.time()
bad = []
spec = [(k, 22) for k in range(1, 9)] + [(9, 16), (10, 16)]
for (k, nmax) in spec:
    vals = a_rows_dp_all(nmax, k)
    for n in range(nmax + 1):
        if vals[n] != Uown(k, (n + 1) // 2) * Uown(k, n // 2):
            bad.append((n, k))
rep('D2-row-transfer', not bad, '(a) 原题按行转移计数（列三元组字面检查）== 乘积公式：1<=k<=8 时 n<=22，k=9,10 时 n<=16 [%.1fs] %s'
    % (time.time() - t, bad[:3]))

# ---------------- D3 多重链 ----------------
t = time.time()
bad = []
for k in range(0, 13):
    rows = rows_of(k) if k > 0 else [()]
    R = len(rows)
    geq = [[all(x >= y for x, y in zip(rows[i], rows[j])) for j in range(R)] for i in range(R)]
    up = [[i for i in range(R) if geq[i][j]] for j in range(R)]
    f = [1] * R
    for m in range(1, 21):
        if m > 1:
            f = [sum(f[i] for i in up[j]) for j in range(R)]
        if sum(f) != Uown(k, m):
            bad.append((k, m))
    if Uown(k, 0) != 1:
        bad.append((k, 0))
rep('D3-multichain', not bad, '(c) 允许行偏序集（逐分量序）的 m 元多重链 r_1>=...>=r_m 个数 == 高度 DP，0<=k<=12, 0<=m<=20 [%.1fs] %s'
    % (time.time() - t, bad[:3]))

# ---------------- D4 高度向量直接枚举 ----------------
t = time.time()
bad = []
for k in range(0, 8):
    for m in range(0, 7 if k <= 6 else 6):
        cnt = 0
        for h in product(range(m + 1), repeat=k):
            if all(good_rows(h[i], h[i + 1], h[i + 2]) for i in range(k - 2)):
                cnt += 1
        if cnt != Uown(k, m):
            bad.append((k, m, cnt))
rep('D4-height-enum', not bad, '(b) 高度向量 {0..m}^k 直接枚举（每个三元组逐行字面检查）== 高度 DP，k<=6,m<=6 与 k=7,m<=5 [%.1fs] %s'
    % (time.time() - t, bad[:3]))

# ---------------- D5 与 core 交叉 ----------------
t = time.time()
sys.path.insert(0, os.path.dirname(os.path.dirname(HERE)))
import core  # noqa: E402

TH = core.U_height_table(60, 20)
okH = all(TH[k][m] == TM[k][m] for k in range(61) for m in range(21))
TF = core.U_fast_table(132, 20)
okF1 = all(TF[k][m] == TL[k][m] for k in range(133) for m in range(21))
TF2 = core.U_fast_table(60, 62)
okF2 = all(TF2[k][m] == TM[k][m] for k in range(61) for m in range(63))
rep('D5-vs-core', okH and okF1 and okF2, '自写 DP == core.U_height_table（参考实现）k<=60,m<=20；== core.U_fast_table k<=132,m<=20 与 k<=60,m<=62 '
    '[%s %s %s; %.1fs]' % (okH, okF1, okF2, time.time() - t))

# ---------------- D6 第 2 节数据 ----------------
PROMPT_TABLE = {
    1: [1, 2, 3, 4, 5, 6, 7], 2: [1, 4, 9, 16, 25, 36, 49], 3: [1, 6, 17, 36, 65, 106, 161],
    4: [1, 9, 32, 80, 165, 301, 504], 5: [1, 14, 64, 192, 457, 938, 1736],
    6: [1, 21, 119, 419, 1136, 2604, 5306], 7: [1, 31, 214, 873, 2669, 6778, 15108],
    8: [1, 46, 388, 1837, 6334, 17802, 43326], 9: [1, 68, 694, 3788, 14666, 45488, 120650],
    10: [1, 100, 1222, 7629, 32971, 112349, 323647]}
ok1 = all([TM[k][m] for m in range(7)] == PROMPT_TABLE[k] for k in range(1, 11))
ok2 = [TM[k][1] for k in range(1, 11)] == [2, 4, 6, 9, 14, 21, 31, 46, 68, 100]
a3 = a_rows_dp_all(6, 3)[1:]
ok3 = a3 == [6, 36, 102, 289, 612, 1296]
rep('D6-prompt-data', ok1 and ok2 and ok3, '第 2 节 U 表（k=1..10,m=0..6）、R_1..R_10、a_3(1..6)=6,36,102,289,612,1296（按行转移直接计数） [%s %s %s]'
    % (ok1, ok2, ok3))

print('TIME r1_defs total %.1fs' % (time.time() - T0), flush=True)
sys.exit(0 if rep.summary() else 1)
