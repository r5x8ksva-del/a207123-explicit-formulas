# -*- coding: utf-8 -*-
"""r-c3b 复核脚本 1：从原始定义独立重建 U / N 表，并与 core 的快速 DP 表（c3b 数据实验所用）逐项对照。

不调用 core 里的任何计数函数（只在最后导入 core.U_fast_table / N_from_U 作为“被核对对象”）。
独立实现：
  (I1) 原题矩阵定义直接计数 a_k(n)（逐行转移，行规则禁 001/010，列规则禁 001/011，逐列字面检查）
  (I2) 允许行偏序集上的多重链计数（第 1 节 (c)）
  (I3) 高度向量暴力枚举（第 1 节 (b)）
  (I4) 任务说明里逐字给出的参考实现 U_list（重新抄写），用于整张 0<=k,m<=40 表
  (I5) N(k,q) 的 DFS 定义（值集恰为 {0..q-1} 的合法词）
"""
import sys, os, time
from itertools import product
from collections import defaultdict

T0 = time.time()
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
CODE = os.path.join(ROOT, 'code')


def good(a, b, c):
    return b == c or (a >= b and a >= c)


# ---------- (I4) 参考实现（逐字照抄任务说明第 1 节）----------
def U_list(m, K):
    out = [1, m + 1]
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    out.append(sum(cnt.values()))
    for k in range(3, K + 1):
        new = defaultdict(int)
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] += v
        cnt = new
        out.append(sum(cnt.values()))
    return out


# ---------- (I1) 原题定义：直接数 a_k(n) ----------
def row_ok(r):
    return all((r[i], r[i + 1], r[i + 2]) not in ((0, 0, 1), (0, 1, 0)) for i in range(len(r) - 2))


def a_direct_mine(n, k):
    rows = [r for r in product((0, 1), repeat=k) if row_ok(r)]
    if n == 0:
        return 1
    if n == 1:
        return len(rows)

    def col_triple_ok(x, y, z):
        for j in range(k):
            if (x[j], y[j], z[j]) in ((0, 0, 1), (0, 1, 1)):
                return False
        return True
    R = len(rows)
    cur = {(i, j): 1 for i in range(R) for j in range(R)}
    nxt = {(i, j): [l for l in range(R) if col_triple_ok(rows[i], rows[j], rows[l])] for i in range(R) for j in range(R)}
    for _ in range(n - 2):
        new = defaultdict(int)
        for (i, j), v in cur.items():
            for l in nxt[(i, j)]:
                new[(j, l)] += v
        cur = new
    return sum(cur.values())


# ---------- (I2) 多重链 ----------
def U_multichain_mine(k, m):
    rows = [r for r in product((0, 1), repeat=k) if row_ok(r)]
    if m == 0:
        return 1
    # f[j] = 以 rows[j] 结尾的长 t 多重链数（r_1>=...>=r_t）
    f = [1] * len(rows)
    for _ in range(m - 1):
        f = [sum(f[i] for i in range(len(rows)) if all(x >= y for x, y in zip(rows[i], rows[j]))) for j in range(len(rows))]
    return sum(f)


# ---------- (I3) 高度向量暴力 ----------
def U_brute(k, m):
    c = 0
    for h in product(range(m + 1), repeat=k):
        if all(good(h[i], h[i + 1], h[i + 2]) for i in range(k - 2)):
            c += 1
    return c


# ---------- (I5) N 的 DFS 定义 ----------
def N_dfs(k):
    res = defaultdict(int)
    if k == 0:
        res[0] = 1
        return res
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
    return res


K = M = 40
ref_cols = [U_list(m, K) for m in range(M + 1)]
REF = [[ref_cols[m][k] for m in range(M + 1)] for k in range(K + 1)]
print('reference U_list table 0<=k,m<=40 built (%.1fs); U_40(40)=%d (%d digits)' % (time.time() - T0, REF[40][40], len(str(REF[40][40]))))

ok_all = True
# 多重链
ok = all(U_multichain_mine(k, m) == REF[k][m] for k in range(1, 9) for m in range(0, 6))
print('PASS' if ok else 'FAIL', 'multichain == U_list, 1<=k<=8, 0<=m<=5')
ok_all &= ok
# 暴力
ok = all(U_brute(k, m) == REF[k][m] for k in range(0, 8) for m in range(0, 5))
print('PASS' if ok else 'FAIL', 'height brute == U_list, 0<=k<=7, 0<=m<=4')
ok_all &= ok
# 原题直接计数
ok = True
for k in range(1, 7):
    for n in range(0, 13):
        if a_direct_mine(n, k) != REF[k][(n + 1) // 2] * REF[k][n // 2]:
            ok = False
print('PASS' if ok else 'FAIL', 'original-definition a_k(n) == U(ceil(n/2))U(floor(n/2)), 1<=k<=6, 0<=n<=12')
ok_all &= ok
ok = [a_direct_mine(n, 3) for n in range(1, 7)] == [6, 36, 102, 289, 612, 1296]
print('PASS' if ok else 'FAIL', 'a_3(n), n=1..6 == 6,36,102,289,612,1296 (task statement)')
ok_all &= ok

# 被核对对象：core 的快速 DP 表与 N 表（c3b 数据实验用的正是它们）
sys.path.insert(0, CODE)
from core import U_fast_table, N_from_U
T = U_fast_table(K, M)
ok = (T == REF)
print('PASS' if ok else 'FAIL', 'core.U_fast_table(40,40) (table used by c3b experiments) == reference U_list, ALL 0<=k,m<=40')
ok_all &= ok
NT = [[N_from_U(T, k, q) for q in range(M + 1)] for k in range(K + 1)]
ok = True
for k in range(0, 10):
    d = N_dfs(k)
    if [d.get(q, 0) for q in range(M + 1)] != NT[k]:
        ok = False
print('PASS' if ok else 'FAIL', 'N table (inclusion-exclusion of U) == DFS definition, 0<=k<=9, all q<=40')
ok_all &= ok
# 额外：N(k,q)=0 for q>k, N(k,k)=2 (k>=2) on the whole table (sanity of the 40x40 N table)
ok = all(NT[k][q] == 0 for k in range(K + 1) for q in range(k + 1, M + 1)) and all(NT[k][k] == 2 for k in range(2, K + 1))
print('PASS' if ok else 'FAIL', 'N table sanity on 40x40: N(k,q)=0 for q>k, N(k,k)=2 for 2<=k<=40')
ok_all &= ok
print('elapsed %.1fs' % (time.time() - T0))
print('OVERALL', 'PASS' if ok_all else 'FAIL')
