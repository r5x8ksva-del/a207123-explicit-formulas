# -*- coding: utf-8 -*-
"""s12-b5 复核 r1：真值的建立与定理 3（短双和）、注 3.1、注 3.2。

  r1-truth-dfs   自写穷举（字母表 {0..k-1}^k）对照自写分类 DP：N、N^E（k<=7）；对照 core.N_brute 的 N（k<=8）
  r1-truth-ie    自写分类 U-DP + 容斥 得到的 N、N^c、N^E 与分类 DP（值集状态）逐项相同（k<=30，q<=10）；
                 自写 U-DP 与 core.U_fast_table 相同（k<=30，m<=9）
  r1-thm3        定理 3 的三个式子（原子 w_i、c_i、w_i-c_i）对 1<=k<=30、1<=q<=10 等于分类 DP 的 N、N^c、N^E；
                 并对 1<=k<=60、1<=q<=10 等于容斥表
  r1-k0          k=0 时三个式子分别给出 (-1)^(q+1)、(-1)^(q+1)、0（而 N(0,q)=0，q>=1）：k>=1 的条件是必要的（预期的「不成立」）
  r1-lag         注 3.1：sum_t C(q,t) y^t/(n-t)! = y^n L_n^{(i+1)}(-1/y)，L 用三项递推独立计算（q<=16，0<=i<=q-1）
  r1-alt         注 3.2 的交错式 N^c = sum_s sum_i (-1)^{q-i} C(q,i) S(i-1+s,i-1) C(k-2s+i-1,k-3s)（1<=k<=30，q<=10）
  r1-w2          q=2：N(k,2)=w_1(k+3)-3、U_k(1)=w_1(k+3)-1（1<=k<=60）——w 原子下 N_2 只有一层（与注 3.2「N 比 U 多一层」的说法对照）
  r1-rev-*       反向检查：i=1 项变号、平移多 1、w_i 去掉 j=i 项、C(q,t) 换成 C(q,t+1)，都应被判为不成立
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'code'))
from s12b5_common import (report, summary, C, good, direct_counts, classified_U, ie_tables, CI, w_atom)  # noqa: E402
import core  # noqa: E402  只取原始定义的真值（U_fast_table、N_brute）

t0 = time.time()
KD, QD = 30, 10
DN, DNE = direct_counts(KD, QD)
DNc = [[DN[k][q] - DNE[k][q] for q in range(QD + 1)] for k in range(KD + 1)]
print('direct_counts(%d,%d) %.1fs' % (KD, QD, time.time() - t0), flush=True)


# ---------------------------------------------------------------- 真值的交叉核对
def brute_words(k):
    """穷举 {0..k-1}^k 中的合法词，按值集恰为 {0..q-1} 分类，返回 (N[q], NE[q])。"""
    N = [0] * (k + 1)
    NE = [0] * (k + 1)
    for w in product(range(k), repeat=k):
        ok = True
        for t in range(k - 2):
            if not good(w[t], w[t + 1], w[t + 2]):
                ok = False
                break
        if not ok:
            continue
        s = set(w)
        q = len(s)
        if max(s) != q - 1:
            continue
        N[q] += 1
        if k >= 2 and w[-2] < w[-1]:
            NE[q] += 1
    return N, NE


ok = True
for k in range(1, 8):
    bN, bNE = brute_words(k)
    for q in range(0, min(k, QD) + 1):
        if bN[q] != DN[k][q] or bNE[q] != DNE[k][q]:
            ok = False
            print('  mismatch brute k=%d q=%d' % (k, q), bN[q], DN[k][q], bNE[q], DNE[k][q])
for k in range(1, 9):
    nb = core.N_brute(k)
    for q in range(0, min(k, QD) + 1):
        if nb.get(q, 0) != DN[k][q]:
            ok = False
            print('  mismatch core.N_brute k=%d q=%d' % (k, q))
report(ok, 'r1-truth-dfs', '穷举 {0..k-1}^k（k<=7，N 与 N^E）与 core.N_brute（k<=8，N）都与分类 DP 一致')

KI = 60
IN, INc, INE = ie_tables(KI, QD)
U, UE = classified_U(KD, QD - 1)
T = core.U_fast_table(KD, QD - 1)
ok = all(U[k][m] == T[k][m] for k in range(KD + 1) for m in range(QD))
ok2 = all(IN[k][q] == DN[k][q] and INc[k][q] == DNc[k][q] and INE[k][q] == DNE[k][q]
          for k in range(KD + 1) for q in range(QD + 1))
report(ok and ok2, 'r1-truth-ie',
       '自写 U-DP = core.U_fast_table（k<=30,m<=9）；容斥得到的 N、N^c、N^E = 值集状态 DP（k<=30,q<=10），'
       '即 §0「三者用同一个二项式基」成立')


# ---------------------------------------------------------------- 定理 3
ci = CI(400)


def thm3(k, q, kind, sign_i1=1, shift=0, drop_top=False, binom_off=0):
    tot = Fr(0)
    for i in range(q):
        for t in range(q - i):
            coef = Fr((-1) ** (q - 1 - i) * C(q, t + binom_off), factorial(i) * factorial(q - 1 - i - t))
            if i == 1:
                coef *= sign_i1
            n = k + 3 * (q - 1 - t) + shift
            if kind == 'N':
                a = w_atom(ci, i, n, drop_top)
            elif kind == 'Nc':
                a = ci(i, n)
            else:
                a = w_atom(ci, i, n, drop_top) - ci(i, n)
            tot += coef * a
    return tot


# 反向演示：命令行加 --break 时，主检验故意用错的符号（i=1 项变号），脚本应报 FAIL、退出码 1
BREAK = '--break' in sys.argv
SG = -1 if BREAK else 1
if BREAK:
    print('[--break] 主检验 r1-thm3 故意把 i=1 项变号', flush=True)
bad = []
for k in range(1, KD + 1):
    for q in range(1, QD + 1):
        for kind, tab in (('N', DN), ('Nc', DNc), ('NE', DNE)):
            if thm3(k, q, kind, sign_i1=SG) != tab[k][q]:
                bad.append((kind, k, q))
for k in range(KD + 1, KI + 1):
    for q in range(1, QD + 1):
        for kind, tab in (('N', IN), ('Nc', INc), ('NE', INE)):
            if thm3(k, q, kind, sign_i1=SG) != tab[k][q]:
                bad.append((kind, k, q))
report(not bad, 'r1-thm3', '定理 3 的 N、N^c、N^E 三式：1<=k<=30 对照分类 DP、31<=k<=60 对照容斥表，1<=q<=10，共 %d 个值，不符 %d'
       % (3 * KI * QD, len(bad)))

vals = [(q, thm3(0, q, 'N'), thm3(0, q, 'Nc'), thm3(0, q, 'NE')) for q in range(1, QD + 1)]
ok = all(a == (-1) ** (q + 1) and b == (-1) ** (q + 1) and c == 0 for q, a, b, c in vals)
report(ok, 'r1-k0', 'k=0：定理 3 的 N、N^c 式给出 (-1)^(q+1)（真值 0），N^E 式给出 0：k>=1 的条件对 N、N^c 必要（q<=10）')


# ---------------------------------------------------------------- 注 3.1：Laguerre（三项递推独立计算）
def laguerre_poly(n, alpha):
    """L_n^{(alpha)}(x) 的系数列表（低次在前），用 (m+1)L_{m+1}=(2m+1+a-x)L_m-(m+a)L_{m-1}。"""
    L0 = [Fr(1)]
    if n == 0:
        return L0
    L1 = [Fr(1 + alpha), Fr(-1)]
    for m in range(1, n):
        a = [Fr(2 * m + 1 + alpha) * c for c in L1] + [Fr(0)]
        for j in range(len(L1)):
            a[j + 1] -= L1[j]
        for j in range(len(L0)):
            a[j] -= (m + alpha) * L0[j]
        L0, L1 = L1, [c / (m + 1) for c in a]
    return L1


ok = True
cnt = 0
for q in range(1, 17):
    for i in range(q):
        n = q - 1 - i
        Lp = laguerre_poly(n, i + 1)
        # y^n L_n(-1/y) = sum_l Lp[l] (-1)^l y^(n-l)
        rhs = [Fr(0)] * (n + 1)
        for l, cl in enumerate(Lp):
            rhs[n - l] += cl * (-1) ** l
        lhs = [Fr(C(q, t), factorial(n - t)) for t in range(n + 1)]
        cnt += 1
        if lhs != rhs:
            ok = False
            print('  laguerre mismatch q=%d i=%d' % (q, i))
report(ok, 'r1-lag', '注 3.1：sum_{t<=n} C(q,t) y^t/(n-t)! = y^n L_n^{(i+1)}(-1/y)（n=q-1-i；Laguerre 用三项递推；%d 组 (q,i)，q<=16）' % cnt)


# ---------------------------------------------------------------- 注 3.2：交错式
def stirling2(nmax):
    S = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    S[0][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
    return S


S2 = stirling2(80)
bad = 0
for k in range(1, KD + 1):
    for q in range(1, QD + 1):
        tot = 0
        for s in range(0, k // 3 + 1):
            for i in range(1, q + 1):
                tot += (-1) ** (q - i) * comb(q, i) * S2[i - 1 + s][i - 1] * C(k - 2 * s + i - 1, k - 3 * s)
        if tot != DNc[k][q]:
            bad += 1
report(bad == 0, 'r1-alt', '注 3.2 的交错式等于 N^c（1<=k<=30，1<=q<=10），不符 %d' % bad)


# ---------------------------------------------------------------- q=2：w 原子下的一层和
ok = all(IN[k][2] == w_atom(ci, 1, k + 3) - 3 for k in range(1, KI + 1))
U1, _ = classified_U(KI, 1)
ok2 = all(U1[k][1] == w_atom(ci, 1, k + 3) - 1 for k in range(0, KI + 1))
report(ok and ok2, 'r1-w2', 'N(k,2)=w_1(k+3)-3（1<=k<=60）、U_k(1)=w_1(k+3)-1（0<=k<=60）：q=2 时 N 在 w 原子下也是一层，'
       '注 3.2「N 比 U 多一层」不是下界意义的结论')


# ---------------------------------------------------------------- 反向检查
def any_mismatch(**kw):
    for k in range(1, 16):
        for q in range(2, 8):
            for kind, tab in (('N', DN), ('Nc', DNc), ('NE', DNE)):
                if kind == 'NE' and kw.get('only_nonNE'):
                    continue
                if thm3(k, q, kind, **{a: b for a, b in kw.items() if a != 'only_nonNE'}) != tab[k][q]:
                    return True
    return False


report(any_mismatch(sign_i1=-1), 'r1-rev-sign', '反向：定理 3 中 i=1 项变号后与真值不符（应不符）')
report(any_mismatch(shift=1), 'r1-rev-shift', '反向：原子下标多平移 1 后与真值不符（应不符）')
report(any_mismatch(drop_top=True), 'r1-rev-wtop', '反向：w_i 去掉 j=i 项后与真值不符（应不符）')
report(any_mismatch(binom_off=1), 'r1-rev-binom', '反向：C(q,t) 换成 C(q,t+1) 后与真值不符（应不符）')

print('time %.1fs' % (time.time() - t0))
sys.exit(1 if summary('r1') else 0)
