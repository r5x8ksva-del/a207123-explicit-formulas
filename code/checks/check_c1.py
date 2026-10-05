# -*- coding: utf-8 -*-
"""check_c1：C-1 复核的正式核对模块（对应 notes/c1.md）。

真值一律来自 core 里按第 1 节原始定义实现的程序：
  U_height_table（第 1 节参考实现 U_list）、U_fast_table / U_fast_column（同一高度 DP 的后缀和实现）、
  U_multichain（允许行偏序集的多重链定义）、a_direct（原题直接计数）、a_brute（2^(nk) 暴力）、
  N_brute（DFS 按定义枚举）。
只用精确整数 / Fraction；仅有的两条数值（decimal）检查是 C2-growth 与 C2-cm，容差写在各自的输出行里。
契约：从任意目录 `py -3.14 <path>/check_c1.py` 运行；每条结论一行
  PASS <id> <描述（含范围）>  或  FAIL <id> ...
最后一行 SUMMARY c1 pass=<n> fail=<n>；全部通过时退出码 0。
"""
import os
import sys
import time
import traceback
from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import product
from math import comb, factorial

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(HERE)
sys.path.insert(0, CODE)

from core import (row_ok, col_ok, a_brute, a_direct, U_multichain, good, U_list,          # noqa: E402
                  U_height_table, U_fast_column, U_fast_table, N_from_U, N_brute,
                  stirling2_table, PROMPT_TABLE, PROMPT_A3)
from polylib import (trim, padd, psub, pscale, pmul, pshift, peval, pdiv, pgcd, pderiv,  # noqa: E402
                     interpolate, P_poly, b_poly)

T_START = time.time()
NPASS = 0
NFAIL = 0


def report(cid, ok, desc):
    global NPASS, NFAIL
    if ok:
        NPASS += 1
    else:
        NFAIL += 1
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def run(cid, desc, fn):
    """fn() 返回 (ok, 附加信息)；抛异常记为 FAIL。"""
    t = time.time()
    try:
        ok, msg = fn()
    except Exception as e:  # pragma: no cover
        traceback.print_exc()
        ok, msg = False, 'EXCEPTION %r' % (e,)
    msg = (msg + '; ' if msg else '') + '%.1fs' % (time.time() - t)
    report(cid, ok, desc + ' [' + msg + ']')


def first_bad(bad):
    return ('bad=%s' % (bad[:4],)) if bad else ''


# ---------------------------------------------------------------------------
# 公共数据（全部来自 core 的原始定义程序）
# ---------------------------------------------------------------------------
KMAX, MMAX = 60, 20
MP = KMAX + 2                        # 62：多项式性 / N 需要 m 到 k+2
TF = U_fast_table(KMAX, MP)          # TF[k][m]，k<=60，m<=62（快速高度 DP）
TH = U_height_table(KMAX, MMAX)      # 第 1 节参考实现（逐字照抄的 U_list），k<=60，m<=20
KL = 2 * (3 * MMAX + 1) + 10         # 132：(C2) 的阶 / BM / (C7) 需要更长的 k
TL = U_fast_table(KL, MMAX)          # TL[k][m]，k<=132，m<=20


def U(k, m, T=None):
    """带引理 1 边界约定的 U_k(m)：U_0≡1，U_{-1}≡1，U_{-2}≡0，U_k(-1)=0（k>=1），U_0(-1)=1。"""
    if T is None:
        T = TF
    if k == -1:
        return 1
    if k < -1:
        return 0
    if m == -1:
        return 1 if k == 0 else 0
    return T[k][m]


def smul(a, b, n):
    """截断乘积（前 n 项），整数或 Fraction。"""
    r = [0] * n
    for i, x in enumerate(a[:n]):
        if x:
            for j in range(min(len(b), n - i)):
                r[i + j] += x * b[j]
    return r


def sinv_int(p, n):
    """1/p 的前 n 项，要求 p[0] == 1（纯整数）。"""
    assert p[0] == 1
    r = [0] * n
    r[0] = 1
    for k in range(1, n):
        s = 0
        for i in range(1, min(k, len(p) - 1) + 1):
            if p[i]:
                s += p[i] * r[k - i]
        r[k] = -s
    return r


def pad(p, n):
    p = list(p)[:n]
    return p + [0] * (n - len(p))


PCACHE = {j: P_poly(j) for j in range(-1, 61)}          # polylib.P_poly：P_m = prod_{i=0}^m (1-x-i x^3)
WCACHE = {-1: [1], 0: [1]}
for _i in range(1, 61):
    WCACHE[_i] = padd(WCACHE[_i - 1], pshift(pscale(PCACHE[_i - 1], _i), 2))


def W_poly(m):
    """W_m = 1 + x^2 * sum_{j=1}^m j*P_{j-1}；W_{-1} = W_0 = 1（m<=60，增量构造并缓存）。"""
    return WCACHE[m]


def legal_seqs(k, m):
    """DFS 枚举 {0..m}^k 中满足第 1 节 (b) 三元组条件的全部序列（m=-1 表示空字母表）。"""
    out = []
    seq = []
    vals = range(m + 1)

    def dfs():
        if len(seq) == k:
            out.append(tuple(seq))
            return
        for v in vals:
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            dfs()
            seq.pop()

    dfs()
    return out


def berlekamp_massey(seq):
    """有理数域上的 Berlekamp–Massey：返回 (连接多项式 C, 线性复杂度 L)，C[0]=1。"""
    s = [Fraction(v) for v in seq]
    C, B = [Fraction(1)], [Fraction(1)]
    L, shift, b = 0, 1, Fraction(1)
    for n in range(len(s)):
        d = s[n]
        for i in range(1, L + 1):
            if i < len(C):
                d += C[i] * s[n - i]
        if d == 0:
            shift += 1
            continue
        coef = d / b
        Told = C[:]
        need = len(B) + shift
        if len(C) < need:
            C = C + [Fraction(0)] * (need - len(C))
        for i, bi in enumerate(B):
            C[i + shift] -= coef * bi
        if 2 * L <= n:
            L = n + 1 - L
            B, b, shift = Told, d, 1
        else:
            shift += 1
    return trim(C), L


# ===========================================================================
# B：基准一致性（各原始定义程序之间）
# ===========================================================================
def chk_B1():
    ok = TH == [row[:MMAX + 1] for row in TF]
    bad = [m for m in (30, 40) if U_list(m, KMAX) != [TF[k][m] for k in range(KMAX + 1)]]
    return ok and not bad, first_bad(bad)


run('B1-fast-vs-height',
    'core.U_fast_table == core.U_height_table（第1节参考实现）k<=60,m<=20；另抽查 m=30,40 整列 k<=60'
    '（m=21..62 每一整列见 code/c1/extended_checks.py 的 E1）', chk_B1)


def chk_B2():
    pairs = [(k, m) for k in range(0, 13) for m in range(0, 16)] + \
            [(k, m) for k in range(0, 7) for m in range(16, 41)]
    bad = [(k, m) for (k, m) in pairs if U_multichain(k, m) != TF[k][m]]
    return not bad, first_bad(bad)


run('B2-dp-vs-multichain', '高度 DP == core.U_multichain（允许行偏序集的多重链定义）0<=k<=12,0<=m<=15；另 0<=k<=6,m<=40', chk_B2)


def chk_B3():
    pairs = [(k, n) for k in range(1, 10) for n in range(0, 14)]
    bad = [(k, n) for (k, n) in pairs if a_direct(n, k) != TF[k][(n + 1) // 2] * TF[k][n // 2]]
    return not bad, first_bad(bad)


run('B3-direct-vs-product', 'core.a_direct（原题直接计数）== U_k(ceil(n/2))*U_k(floor(n/2))，1<=k<=9, 0<=n<=13'
    '（k=10,11 与 k<=7,n<=20 见 extended_checks.py 的 E2）', chk_B3)


def chk_B4():
    bad, pairs = [], 0
    for k in range(1, 21):
        for n in range(0, 20 // k + 1):
            pairs += 1
            ab = a_brute(n, k)
            if ab != a_direct(n, k) or ab != TF[k][(n + 1) // 2] * TF[k][n // 2]:
                bad.append((n, k))
    return not bad, 'pairs=%d %s' % (pairs, first_bad(bad))


run('B4-brute', 'core.a_brute（2^(nk) 全枚举）== core.a_direct == U 乘积公式，全部 k>=1,n>=0,n*k<=20', chk_B4)


def chk_B5():
    ok = all(TH[k][:7] == PROMPT_TABLE[k] for k in range(1, 11))
    return ok, ''


run('B5-prompt-table', '第2节 U_k(m) 表（k=1..10, m=0..6）== 参考实现 DP', chk_B5)


def chk_B6():
    R = [TF[k][1] for k in range(KMAX + 1)]
    ok0 = R[1:11] == [2, 4, 6, 9, 14, 21, 31, 46, 68, 100]
    den = pmul([1, -1], [1, -1, 0, -1])                       # (1-x)(1-x-x^3)
    inv = sinv_int(den, KMAX + 2)
    ok1 = smul([1, 0, 1, -1], inv, KMAX + 2)[:KMAX + 1] == R   # (1+x^2-x^3)/den
    s2 = smul([1, -1, 1], inv, KMAX + 2)                      # (1-x+x^2)/den
    ok2 = all(s2[k + 1] == R[k] for k in range(KMAX + 1))
    ok3 = all(R[k] == 1 + R[k - 1] + U(k - 3, 1) for k in range(1, KMAX + 1))
    return ok0 and ok1 and ok2 and ok3, 'list=%s gf1=%s shift=%s rec=%s' % (ok0, ok1, ok2, ok3)


run('B6-Rk', 'R_k=U_k(1)：R_1..R_10=2,4,..,100；sum_k R_k x^k=(1+x^2-x^3)/((1-x)(1-x-x^3))；'
    'R_k=[x^{k+1}](1-x+x^2)/((1-x)(1-x-x^3))；R_k=1+R_{k-1}+R_{k-3}（k<=60）', chk_B6)


def chk_B7():
    a3 = [a_direct(n, 3) for n in range(1, 7)]
    pr = [TH[3][(n + 1) // 2] * TH[3][n // 2] for n in range(1, 7)]
    return a3 == PROMPT_A3 and pr == PROMPT_A3, 'a3=%s' % a3


run('B7-a3', 'a_3(1..6) = 6,36,102,289,612,1296（a_direct 与乘积公式）', chk_B7)


# ===========================================================================
# R：第 1 节归约 (a)(b)(c) 的定义级核对
# ===========================================================================
def chk_R1():
    ok = True
    for t in product((0, 1), repeat=3):
        if (t in ((0, 0, 1), (0, 1, 1))) != (t[0] == 0 and t[2] == 1):
            ok = False
    for L in range(0, 13):
        for col in product((0, 1), repeat=L):
            if col_ok(col) != all(col[i] >= col[i + 2] for i in range(L - 2)):
                ok = False
    return ok, ''


run('R1-col-rule', '(a) 列规则 <=> 对所有 i: b_i>=b_{i+2}（8 个三元组 + 长度<=12 的全部 0/1 列）', chk_R1)


def chk_R2():
    ok = True
    for M in range(0, 13):
        for a in range(M + 1):
            for b in range(M + 1):
                for c in range(M + 1):
                    rows_good = all(row_ok((int(r <= a), int(r <= b), int(r <= c))) for r in range(1, M + 1))
                    if rows_good != good(a, b, c):
                        ok = False
    cnt_pairs = 0
    for k in range(1, 17):
        for m in range(0, 16 // k + 1):
            cnt_pairs += 1
            cnt = 0
            for cells in product((0, 1), repeat=m * k):
                rows = [cells[i * k:(i + 1) * k] for i in range(m)]
                if all(rows[i][j] >= rows[i + 1][j] for i in range(m - 1) for j in range(k)) \
                        and all(row_ok(r) for r in rows):
                    cnt += 1
            if cnt != TF[k][m]:
                ok = False
    return ok, 'matrix pairs=%d' % cnt_pairs


run('R2-heights', '(b) 高度 (a,b,c) 在 {0..M}^3（M<=12）上「各行都不是001/010」<=> good(a,b,c)；'
    '且「列单调不增+行规则」的 m×k 矩阵（2^(mk) 全枚举，mk<=16）个数 == U_k(m)', chk_R2)


# ===========================================================================
# L：引理 1
# ===========================================================================
def lemma1_bad(T, kmax, mmax):
    return [(k, m) for k in range(1, kmax + 1) for m in range(0, mmax + 1)
            if T[k][m] != U(k, m - 1, T) + U(k - 1, m, T) + m * U(k - 3, m, T)]


run('L1-ref', '引理1 U_k(m)=U_k(m-1)+U_{k-1}(m)+m*U_{k-3}(m)（含边界约定）在参考实现表上成立，1<=k<=60, 0<=m<=20',
    lambda: (lambda b: (not b, first_bad(b)))(lemma1_bad(TH, KMAX, MMAX)))
run('L1-fast', '引理1 在快速 DP 表上成立，1<=k<=60, 0<=m<=62',
    lambda: (lambda b: (not b, first_bad(b)))(lemma1_bad(TF, KMAX, MP)))


def chk_L1_cases():
    bad = []
    for k in range(1, 9):
        for m in range(0, 7):
            seqs = legal_seqs(k, m)
            if len(seqs) != TF[k][m]:
                bad.append(('count', k, m))
                continue
            c = [0, 0, 0, 0]
            forced = True
            for s in seqs:
                if m not in s:
                    c[0] += 1
                    continue
                i = s.index(m) + 1
                if i == 1:
                    c[1] += 1
                elif i == 2:
                    c[2] += 1
                    if k >= 3 and s[2] != m:
                        forced = False
                else:
                    c[3] += 1
            exp = [U(k, m - 1), U(k - 1, m), m * U(k - 3, m), 0]
            if c != exp or not forced:
                bad.append((k, m, c, exp))
    return not bad, first_bad(bad)


run('L1-cases', '引理1 证明的分类逐类计数（DFS 枚举合法序列）：(i)=U_k(m-1),(ii)=U_{k-1}(m),(iii)=m*U_{k-3}(m)'
    '且 h_3 被迫为 m，(iv)=0；1<=k<=8, 0<=m<=6', chk_L1_cases)


# ===========================================================================
# C1：求和式、多项式性
# ===========================================================================
def chk_C1_sum():
    bad = [(k, m) for k in range(1, KMAX + 1) for m in range(0, MP + 1)
           if TF[k][m] != sum(U(k - 1, j) + j * U(k - 3, j) for j in range(m + 1))]
    return not bad, first_bad(bad)


run('C1-sum', '(C1) U_k(m)=sum_{j=0}^m [U_{k-1}(j)+j*U_{k-3}(j)]，1<=k<=60, 0<=m<=62', chk_C1_sum)


def chk_C1_poly():
    bad = []
    for k in range(0, KMAX + 1):
        cur = [TF[k][m] for m in range(MP + 1)]           # m = 0..62（至少 k+3 个点）
        lead = [cur[0]]
        for _ in range(1, k + 2):
            cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
            lead.append(cur[0])
        if any(cur):                                     # Δ^{k+1} 在 m=0..61-k 全为 0
            bad.append((k, 'D^{k+1}'))
        if lead[k] != (2 if k >= 2 else 1):              # Δ^k = k! * 首项系数
            bad.append((k, 'D^k', lead[k]))
        um1 = sum((-1) ** j * lead[j] for j in range(k + 1))   # Newton 前向公式在 x=-1
        if um1 != (0 if k >= 1 else 1):
            bad.append((k, 'u(-1)', um1))
    return not bad, first_bad(bad)


run('C1-poly', '(C1) 对每个 0<=k<=60，用 m=0..62（>=k+3 个点）的 DP 值做 Newton 前向差分插值：'
    'Δ^{k+1}≡0（次数<=k），Δ^k U_k(0)=2（k>=2；即首项 2/k!，次数恰为 k），插值多项式在 m=-1 取 0（k>=1）', chk_C1_poly)


def chk_C1_mono():
    bad = []
    for k in range(0, 21):
        xs = list(range(k + 3))
        poly = interpolate(xs, [TF[k][m] for m in xs])
        if len(poly) - 1 != k:
            bad.append((k, 'deg'))
            continue
        if k >= 2 and poly[-1] != Fraction(2, factorial(k)):
            bad.append((k, 'lc'))
        if k >= 1 and peval(poly, -1) != 0:
            bad.append((k, 'u(-1)'))
    return not bad, first_bad(bad)


run('C1-poly-monomial', '(C1) 单项式基交叉核对：polylib.interpolate 过 m=0..k+2 得次数=k、首项=2/k!（k>=2）、'
    'u_k(-1)=0（k>=1），0<=k<=20', chk_C1_mono)

# ===========================================================================
# C2：G_m 的递推、闭式、阶、最简性、增长率
# ===========================================================================
N2 = KL + 1
G = {m: [TL[k][m] for k in range(N2)] for m in range(MMAX + 1)}
G[-1] = [1] + [0] * KL


def chk_C2_rec():
    bad = []
    for m in range(0, MMAX + 1):
        lhs = smul([1, -1, 0, -m], G[m], N2)
        rhs = list(G[m - 1])
        rhs[2] += m
        if lhs != rhs:
            bad.append(m)
    return not bad, first_bad(bad)


run('C2-rec', '(C2) (1-x-m x^3) G_m = G_{m-1} + m x^2（G_{-1}=1），0<=m<=20，逐项到 x^132', chk_C2_rec)


def chk_C2_closed():
    bad = []
    for m in range(0, MMAX + 1):
        Pm, Wm = P_poly(m), W_poly(m)
        S = []
        for j in range(m):
            S = padd(S, P_poly(j))
        rhs = psub(psub([1], Pm), pshift(S, 1))           # 1 - P_m - x*sum_{j<m} P_j
        if pshift(Wm, 1) != rhs:
            bad.append(('x*W_m', m))
        if len(Wm) - 1 != 3 * m or len(Pm) - 1 != 3 * m + 1:
            bad.append(('deg', m))
        if Pm[-1] != (-1) ** (m + 1) * factorial(m) or (m >= 1 and Wm[-1] != (-1) ** m * factorial(m)):
            bad.append(('lc', m))
        if smul(pshift(Pm, 1), G[m], N2) != pad(rhs, N2):  # x P_m G_m == rhs（模 x^133）
            bad.append(('series', m))
    return not bad, first_bad(bad)


run('C2-closed', '(C2) x P_m G_m = 1 - P_m - x sum_{j<m} P_j（逐项到 x^132），且右边 = x*W_m，'
    'W_m = 1 + x^2 sum_{j=1}^m j P_{j-1}，deg W_m = 3m < deg P_m = 3m+1，lc P_m=(-1)^{m+1}m!，lc W_m=(-1)^m m!，0<=m<=20',
    chk_C2_closed)


def chk_C2_order():
    bad = []
    for m in range(0, MMAX + 1):
        Pm = P_poly(m)
        d = len(Pm) - 1
        for k in range(d, KL + 1):
            if sum(Pm[i] * TL[k - i][m] for i in range(d + 1)) != 0:
                bad.append((m, k))
                break
    return not bad, first_bad(bad)


run('C2-order', '(C2) 以 P_m 为特征多项式的 3m+1 阶递推对 DP 数据 U_k(m) 成立，3m+1<=k<=132，0<=m<=20', chk_C2_order)


def chk_C2_gcd():
    bad = [m for m in range(0, MMAX + 1) if pgcd(W_poly(m), P_poly(m)) != [1]]
    return not bad, first_bad(bad)


run('C2-gcd', '(C2 最简性) 精确 gcd(W_m, P_m) = 1（Fraction 欧几里得），0<=m<=20', chk_C2_gcd)


def chk_C2_BM():
    bad = []
    for m in range(0, MMAX + 1):
        L0 = 3 * m + 1
        C, L = berlekamp_massey([TL[k][m] for k in range(0, 2 * L0 + 6)])
        if L != L0 or C != [Fraction(c) for c in P_poly(m)]:
            bad.append((m, L))
    return not bad, first_bad(bad)


run('C2-BM', '(C2 最简性，独立于闭式) Berlekamp–Massey 直接作用于 DP 数据 U_0..U_{6m+7}(m)：'
    '线性复杂度恰为 3m+1，连接多项式恰为 P_m，0<=m<=20', chk_C2_BM)


def chk_C2_allm():
    bad = []
    for m in range(0, MMAX + 1):                     # W_m ≡ W_i (mod b_i)
        Wm = W_poly(m)
        for i in range(0, m + 1):
            if pdiv(psub(Wm, W_poly(i)), b_poly(i))[1]:
                bad.append(('cong', m, i))
    for i in range(0, 61):                           # W_i(1) = 1
        if peval(W_poly(i), 1) != 1:
            bad.append(('W(1)', i))
    red, unit_factors = [], []
    for i in range(1, 61):
        zs = [z for z in range(-i, i + 1) if z != 0 and i % abs(z) == 0 and z ** 3 - z ** 2 - i == 0]
        if not zs:                                   # b_i 在 Q 上不可约，唯一本原不可约因子 ±b_i
            factors = [b_poly(i)]
        else:
            z = zs[0]
            red.append(i)
            quad = [1, z - 1, z * (z - 1)]
            if pmul([1, -z], quad) != b_poly(i) or (z - 1) ** 2 - 4 * z * (z - 1) >= 0:
                bad.append(('fac', i))
            factors = [[1, -z], quad]
        for d in factors:
            if abs(peval(d, 1)) == 1:
                unit_factors.append((i, d))
    if red != [4, 18, 48]:
        bad.append(('reducible', red))
    if unit_factors != [(1, b_poly(1)), (4, [1, -2])]:
        bad.append(('unit', unit_factors))
    if pgcd(W_poly(1), b_poly(1)) != [1] or psub(W_poly(1), b_poly(1)) != [0, 1, 1]:
        bad.append('i=1')
    if peval(W_poly(4), Fraction(1, 2)) != Fraction(645, 512):
        bad.append('i=4')
    return not bad, 'reducible b_i (i<=60): %s %s' % (red, first_bad(bad))


run('C2-allm-ingredients', '(C2 对一切 m 的最简性证明的各成分) W_m≡W_i (mod b_i)（i<=m<=20）；W_i(1)=1（i<=60）；'
    'b_i 可约 <=> i=y^2(y-1)（i<=60 只有 4,18,48）且 b_i=(1-yx)(1+(y-1)x+y(y-1)x^2)、二次因子判别式<0；'
    'd(1)=±1 的不可约因子只有 b_1 与 1-2x，且 W_1-b_1=x+x^2、W_4(1/2)=645/512≠0', chk_C2_allm)


def chk_C2_sqfree():
    bad = []
    for i in range(0, 61):                                   # 每个 b_i 无重根
        if pgcd(b_poly(i), pderiv(b_poly(i))) != [1]:
            bad.append(('sq', i))
    for i in range(1, 61):                                   # z^3 - z^2 - i 的判别式 = -i(4+27i) < 0
        a, bb, c = -1, 0, -i
        disc = 18 * a * bb * c - 4 * a ** 3 * c + a * a * bb * bb - 4 * bb ** 3 - 27 * c * c
        if disc != -i * (4 + 27 * i) or disc >= 0:
            bad.append(('disc', i))
    for i in range(0, MMAX + 1):                             # b_i 两两互素
        for j in range(i + 1, MMAX + 1):
            if pgcd(b_poly(i), b_poly(j)) != [1]:
                bad.append(('cop', i, j))
    for m in range(0, 9):                                    # 小 m 再直接算 gcd(P_m, P_m')
        if pgcd(P_poly(m), pderiv(P_poly(m))) != [1]:
            bad.append(('direct', m))
    return not bad, first_bad(bad)


run('C2-sqfree', '(C2) P_m 无重因子：每个 b_i 与 b_i\' 互素（i<=60），z^3-z^2-i 的判别式=-i(4+27i)<0（i<=60），'
    'b_i 两两互素（i<j<=20），并对 m<=8 直接验证 gcd(P_m,P_m\')=1（故 G_m 的极点全是单极点）', chk_C2_sqfree)


def chk_C2_growth():
    getcontext().prec = 60
    KG = 2000
    worst, bad = Decimal(0), []
    for m in range(1, MMAX + 1):
        col = U_fast_column(m, KG + 1)
        ratio = Decimal(col[KG + 1]) / Decimal(col[KG])
        z = Decimal(m + 2)                               # 在根右侧起步，凸函数上牛顿法单调收敛
        for _ in range(300):
            zn = z - (z * z * z - z * z - m) / (3 * z * z - 2 * z)
            if zn == z:
                break
            z = zn
        err = abs(ratio - z)
        worst = max(worst, err)
        if err > Decimal('1e-9'):
            bad.append(m)
    return not bad, 'max |U_2001(m)/U_2000(m) - rho_m| = %.2e' % worst


run('C2-growth', '(C2 增长率，数值检查) rho_m = y^3=y^2+m 的唯一实根；DP 比值 U_2001(m)/U_2000(m) 与 rho_m 之差 < 1e-9'
    '（decimal 60 位，容差 1e-9），1<=m<=20', chk_C2_growth)


def chk_C2_cm():
    getcontext().prec = 150
    KG = 2000
    worst, bad = Decimal(0), []
    for m in range(1, MMAX + 1):
        z = Decimal(m + 2)
        for _ in range(500):
            zn = z - (z * z * z - z * z - m) / (3 * z * z - 2 * z)
            if zn == z:
                break
            z = zn
        x = 1 / z
        Pm1 = Decimal(1)
        for i in range(0, m):                                # P_{m-1}(x_m) 按因子相乘（避免抵消）
            Pm1 *= (1 - x - i * x ** 3)
        Wm1 = Decimal(0)
        for c in reversed(W_poly(m - 1)):                    # Horner（150 位足够）
            Wm1 = Wm1 * x + c
        cm = (Wm1 / Pm1 + m * x * x) / (x * (1 + 3 * m * x * x))
        col = U_fast_column(m, KG)
        rel = abs(Decimal(col[KG]) / z ** KG / cm - 1)
        worst = max(worst, rel)
        if rel > Decimal('1e-8'):
            bad.append(m)
        if abs(Pm1 / (factorial(m) * x ** (3 * m)) - 1) > Decimal('1e-100'):   # P_{m-1}(x_m) = m! x_m^{3m}
            bad.append(('P(x_m)', m))
    return not bad, 'max relative error = %.2e' % worst


run('C2-cm', '(C2 推论，数值检查) 单极点留数 c_m=(G_{m-1}(x_m)+m x_m^2)/(x_m(1+3m x_m^2))，x_m=1/rho_m，'
    'G_{m-1}=W_{m-1}/P_{m-1}：|U_2000(m)/(c_m rho_m^2000) - 1| < 1e-8（decimal 150 位，容差 1e-8）；'
    '另 P_{m-1}(x_m)=m! x_m^{3m}（相对误差<1e-100）；1<=m<=20', chk_C2_cm)

# ===========================================================================
# C3：N(k,q)、二项式基、三角递推、对角线
# ===========================================================================
QMAX = MP + 1                                                    # 63
NT = [[N_from_U(TF, k, q) for q in range(QMAX + 1)] for k in range(KMAX + 1)]


def Nv(k, q):
    if k < 0 or q < 0 or q > QMAX:
        return 0
    assert k <= KMAX
    return NT[k][q]


def chk_C3_zero():
    bad = [(k, q) for k in range(KMAX + 1) for q in range(QMAX + 1)
           if (q > k or (q == 0 and k >= 1)) and NT[k][q] != 0]
    ok = NT[0][0] == 1
    return ok and not bad, first_bad(bad)


run('C3-zero', '(C3) 容斥 N(k,q)=sum_i (-1)^{q-i}C(q,i)U_k(i-1)（由 DP 列 m<=62）：N(k,q)=0 对 k<q<=63，'
    'N(k,0)=0（k>=1），N(0,0)=1；0<=k<=60', chk_C3_zero)


def chk_C3_basis():
    bad = [(k, m) for k in range(KMAX + 1) for m in range(MP + 1)
           if TF[k][m] != sum(NT[k][q] * comb(m + 1, q) for q in range(0, k + 1))]
    return not bad, first_bad(bad)


run('C3-basis', '(C3) 二项式基 U_k(m)=sum_{q=0}^{k} N(k,q) C(m+1,q)，0<=k<=60, 0<=m<=62', chk_C3_basis)


def chk_C3_brute():
    bad = []
    for k in range(0, 10):
        br = N_brute(k)
        if [br.get(q, 0) for q in range(0, k + 2)] != [NT[k][q] for q in range(0, k + 2)]:
            bad.append(k)
    return not bad, first_bad(bad)


run('C3-brute', '(C3) 组合意义：core.N_brute（DFS 按定义数「值域恰为 q 个值的合法词」）== 容斥 N(k,q)，0<=k<=9'
    '（k=10,11 见 extended_checks.py 的 E3）', chk_C3_brute)


def chk_C3_tri():
    bad = [(k, r) for k in range(3, KMAX + 1) for r in range(0, k + 1)
           if Nv(k, r + 1) != Nv(k - 1, r) + Nv(k - 1, r + 1)
           + r * (Nv(k - 3, r - 1) + 2 * Nv(k - 3, r) + Nv(k - 3, r + 1))]
    return not bad, first_bad(bad)


run('C3-tri', '(C3) 三角递推 N(k,r+1)=N(k-1,r)+N(k-1,r+1)+r[N(k-3,r-1)+2N(k-3,r)+N(k-3,r+1)]，3<=k<=60, 0<=r<=k', chk_C3_tri)


def chk_C3_init():
    zero_boundary_value = Nv(1, 1) + Nv(1, 2) + 1 * (0 + 0 + 0)      # k=2, r=1，N(-1,.)≡0
    obs = zero_boundary_value == 1 and NT[2][2] == 2

    def Ne(k, q):
        if k == -1:
            return 1 if q == 0 else 0
        if k < -1 or q < 0:
            return 0
        return Nv(k, q)

    ext = all(Ne(k, r + 1) == Ne(k - 1, r) + Ne(k - 1, r + 1) + r * (Ne(k - 3, r - 1) + 2 * Ne(k - 3, r) + Ne(k - 3, r + 1))
              for k in range(1, KMAX + 1) for r in range(0, k + 1))
    return obs and ext, 'zero-boundary k=2 gives N(2,2)=%d (true 2); with N(-1,0)=1 holds k>=1: %s' % (zero_boundary_value, ext)


run('C3-init', '(C3 初值说明) 只给 N(0,0)=1+零边界时 k=2 处递推给出 N(2,2)=1≠2，故 k>=3 的递推需要 k=1,2 两行作初值；'
    '若约定 N(-1,0)=1、N(-2,.)=0（对应 U_{-1}≡1、U_{-2}≡0），递推对 1<=k<=60 全部成立', chk_C3_init)


def chk_C3_diag():
    ok1 = all(NT[k][k] == 2 for k in range(2, KMAX + 1))
    ok2 = all(NT[k][k - 1] == k * k - k - 4 for k in range(4, KMAX + 1))
    ok3 = NT[3][2] == 4 and NT[1][1] == 1 and NT[0][0] == 1
    return ok1 and ok2 and ok3, 'diag=%s subdiag=%s small=%s' % (ok1, ok2, ok3)


run('C3-diag', '(C3) N(k,k)=2（2<=k<=60）；N(k,k-1)=k^2-k-4（4<=k<=60）；N(3,2)=4（公式在 k=3 不成立）', chk_C3_diag)

PROMPT_N = {1: [1], 2: [1, 2], 3: [1, 4, 2], 4: [1, 7, 8, 2], 5: [1, 12, 25, 16, 2],
            6: [1, 19, 59, 65, 26, 2], 7: [1, 29, 124, 199, 139, 38, 2],
            8: [1, 44, 253, 557, 574, 277, 52, 2], 9: [1, 66, 493, 1416, 1991, 1446, 509, 68, 2],
            10: [1, 98, 925, 3337, 6051, 6012, 3257, 871, 86, 2]}

run('C3-prompt', '(C3) 提示词 N 三角形 k=1..10 与容斥值一致',
    lambda: (all(NT[k][1:k + 1] == PROMPT_N[k] for k in range(1, 11)), ''))


def chk_C3_cases():
    bad = []
    for k in range(3, 9):
        for q in range(1, k + 1):
            top, lower = q - 1, set(range(q - 1))
            words = [s for s in legal_seqs(k, q - 1) if len(set(s)) == q]
            cnt = dict(p1_again=0, p1_once=0, A_with=0, A_without=0, B_with=0, B_without=0, other=0)
            for s in words:
                i = s.index(top) + 1
                if i == 1:
                    cnt['p1_again' if top in s[1:] else 'p1_once'] += 1
                elif i == 2 and s[2] == top:
                    tail = set(s[3:])
                    if lower <= tail:
                        cnt['A_with' if top in tail else 'A_without'] += 1
                    elif lower - tail == {s[0]}:
                        cnt['B_with' if top in tail else 'B_without'] += 1
                    else:
                        cnt['other'] += 1
                else:
                    cnt['other'] += 1
            exp = dict(p1_again=Nv(k - 1, q), p1_once=Nv(k - 1, q - 1),
                       A_with=(q - 1) * Nv(k - 3, q), A_without=(q - 1) * Nv(k - 3, q - 1),
                       B_with=(q - 1) * Nv(k - 3, q - 1), B_without=(q - 1) * Nv(k - 3, q - 2), other=0)
            if cnt != exp or len(words) != Nv(k, q):
                bad.append((k, q))
    return not bad, first_bad(bad)


run('C3-cases', '(C3) 三角递推证明的 6 类逐类计数（DFS 枚举满射合法词）与 N(k-1,q),N(k-1,q-1),(q-1)N(k-3,q),'
    '(q-1)N(k-3,q-1)[两类],(q-1)N(k-3,q-2) 一致，且无其他情形；3<=k<=8', chk_C3_cases)

# ===========================================================================
# C4：1/P_m 的两个系数公式与 Θ 公式
# ===========================================================================
NC = KMAX + 1 + 3 * MMAX + 4                                      # 125
CT = [[sum(comb(n - 2 * j, j) * i ** j for j in range(0, n // 3 + 1)) for n in range(NC + 1)]
      for i in range(MMAX + 1)]
S2 = stirling2_table(2 * MMAX + 2)
INVP = {m: sinv_int(P_poly(m), KMAX + 1) for m in range(MMAX + 1)}


def chk_C4_c():
    bad = [i for i in range(MMAX + 1) if CT[i] != sinv_int(b_poly(i), NC + 1)]
    return not bad, first_bad(bad)


run('C4-c', '(C4) c_i(n)=sum_{0<=j<=n/3} C(n-2j,j) i^j == [x^n] 1/(1-x-i x^3)（级数求逆），0<=i<=20, 0<=n<=125', chk_C4_c)


def chk_C4_S():
    bad = [(m, n) for m in range(MMAX + 1) for n in range(KMAX + 1)
           if INVP[m][n] != sum(S2[s + m][m] * comb(n + m - 2 * s, m + s) for s in range(0, n // 3 + 1))]
    return not bad, first_bad(bad)


run('C4-S', '(C4) [x^n] 1/P_m = sum_{0<=s<=n/3} S(s+m,m) C(n+m-2s,m+s)，0<=m<=20, 0<=n<=60', chk_C4_S)


def chk_C4_pf():
    bad = []
    for m in range(MMAX + 1):
        fm = factorial(m)
        for n in range(-3 * m, KMAX + 1):
            tot = sum((-1) ** (m - i) * comb(m, i) * CT[i][n + 3 * m] for i in range(m + 1))
            if tot != (fm * INVP[m][n] if n >= 0 else 0):
                bad.append((m, n))
    return not bad, first_bad(bad)


run('C4-pf', '(C4) m!*[x^n]1/P_m = sum_i (-1)^{m-i}C(m,i) c_i(n+3m)，0<=m<=20, 0<=n<=60；'
    '且 -3m<=n<0 时右边为 0', chk_C4_pf)


def gen_binom(a, b):
    """广义二项式系数 a(a-1)...(a-b+1)/b!（b>=0 整数，a 任意整数），用来说明求和范围约定的必要性。"""
    num = 1
    for i in range(b):
        num *= (a - i)
    return Fraction(num, factorial(b))


def chk_C4_convention():
    t1 = S2[2][1] * gen_binom(-1, 2)            # m=1,n=0,s=1：S(2,1)*C(-1,2)
    t2 = S2[3][1] * gen_binom(-3, 3)            # m=1,n=0,s=2：S(3,1)*C(-3,3)
    c_gen = sum(gen_binom(1 - 2 * j, j) * 5 ** j for j in range(0, 2))   # c_5(1) 若对 j<=1 用广义二项式
    ok = (t1 == 1 and t2 == -10 and INVP[1][0] == 1 and c_gen == 1 - 5 and CT[5][1] == 1)
    return ok, 's=1 term=%s, s=2 term=%s, generalized c_5(1)=%s vs true %s' % (t1, t2, c_gen, CT[5][1])


run('C4-convention', '(C4 求和范围约定的必要性) 若按广义二项式把 s、j 求和到 n/3 以外：m=1,n=0 时 s=1 项 S(2,1)C(-1,2)=1、'
    's=2 项 S(3,1)C(-3,3)=-10（真值 [x^0]1/P_1=1 只来自 s=0 项）；c_5(1) 会变成 1-5=-4（真值 1）', chk_C4_convention)


def theta(m, t, n):
    return Fraction(sum((-1) ** r * comb(t, r) * CT[m - r][n] for r in range(t + 1)), factorial(t))


def chk_C4_theta():
    bad, nonint = [], 0
    for m in range(MMAX + 1):
        for k in range(KMAX + 1):
            th_main = theta(m, m, k + 1 + 3 * m)
            th_rest = [theta(m, t, k + 3 * t) for t in range(m)]
            nonint += sum(1 for v in [th_main] + th_rest if v.denominator != 1)
            if th_main - sum(th_rest) != TH[k][m]:
                bad.append((k, m))
    return not bad and nonint == 0, 'non-integer Theta values=%d %s' % (nonint, first_bad(bad))


run('C4-theta', '(C4) U_k(m) = Θ_m(k+1+3m) - sum_{t<m} Θ_t(k+3t)（Fraction 精确，对照参考实现 DP），'
    '0<=k<=60（含 k=0）, 0<=m<=20；所有 Θ 值均为整数', chk_C4_theta)


def chk_C4_theta_mid():
    bad = []
    for m in range(MMAX + 1):
        for t in range(m + 1):
            den = [1]
            for i in range(m - t, m + 1):
                den = pmul(den, b_poly(i))
            inv = sinv_int(den, KMAX + 1)
            if any(theta(m, t, k + 3 * t) != inv[k] for k in range(KMAX + 1)):
                bad.append((m, t))
    return not bad, first_bad(bad)


run('C4-theta-mid', '(C4 中间恒等式) Θ_t(k+3t) = [x^k] 1/prod_{i=m-t}^{m} b_i，0<=t<=m<=20, 0<=k<=60', chk_C4_theta_mid)


# ===========================================================================
# C5：一阶偏微分方程（逐项）
# ===========================================================================
def chk_C5():
    K, M = KMAX, MMAX
    F = [[TF[k][m] for m in range(M + 1)] for k in range(K + 1)]
    A = [[F[k][m] - (F[k - 1][m] if k >= 1 else 0) - (F[k][m - 1] if m >= 1 else 0)
          for m in range(M + 1)] for k in range(K + 1)]                        # (1-x-t)F
    B = [[(m * F[k - 3][m] if k >= 3 else 0) for m in range(M + 1)] for k in range(K + 1)]  # x^3 t dF/dt
    LHS = [[A[k][m] - B[k][m] for m in range(M + 1)] for k in range(K + 1)]
    inv2 = sinv_int([1, -2, 1], M + 1)                                         # 1/(1-t)^2
    RHS = [[0] * (M + 1) for _ in range(K + 1)]
    RHS[0][0] += 1
    for m in range(1, M + 1):
        RHS[2][m] += inv2[m - 1]                                               # x^2 * t/(1-t)^2
    bad = [(k, m) for k in range(K + 1) for m in range(M + 1) if LHS[k][m] != RHS[k][m]]
    return not bad, first_bad(bad)


run('C5-pde', '(C5) (1-x-t)F - x^3 t dF/dt = 1 + x^2 t/(1-t)^2 逐项成立（F 取 DP 表），0<=k<=60, 0<=m<=20', chk_C5)


# ===========================================================================
# C6：h 多项式
# ===========================================================================
def h_by_recurrence(kmax):
    H = {0: [1], 1: [1], 2: [1, 1]}
    for k in range(3, kmax + 1):
        h3 = H[k - 3]
        inner = padd(pmul([1, -1], pderiv(h3)), pscale(h3, k - 2))
        H[k] = padd(H[k - 1], pmul([0, 1, -1], inner))
    return H


HREC = h_by_recurrence(KMAX)


def chk_C6():
    pw = [[1]]
    for _ in range(KMAX + 2):
        pw.append(pmul(pw[-1], [1, -1]))
    bad = []
    for k in range(1, KMAX + 1):
        hN = []
        for q in range(1, k + 1):
            hN = padd(hN, pscale(pshift(pw[k - q], q - 1), NT[k][q]))
        if hN != HREC[k]:
            bad.append(('N', k))
    for k in range(0, KMAX + 1):
        if smul(pw[k + 1], [TF[k][m] for m in range(MP + 1)], MP + 1) != pad(HREC[k], MP + 1):
            bad.append(('DP', k))
    return not bad, first_bad(bad)


run('C6-h', '(C6) 三种 h_k 一致：递推（h_0=1,h_1=1,h_2=1+t 起步，k>=3）== sum_q N(k,q)t^{q-1}(1-t)^{k-q}（1<=k<=60）'
    '== (1-t)^{k+1} sum_{m<=62} U_k(m)t^m 截断到 t^62（其 t^k..t^62 系数为 0），0<=k<=60', chk_C6)


def chk_C6_explicit():
    given = {3: [1, 2, -1], 4: [1, 4, -3], 5: [1, 8, -5, -2], 6: [1, 14, -7, -8, 2]}
    ok = all(HREC[k] == v for k, v in given.items())
    ok2 = all(peval(HREC[k], 1) == 2 for k in range(2, KMAX + 1))
    ok3 = any(c < 0 for c in HREC[3])
    return ok and ok2 and ok3, 'explicit=%s h_k(1)=2:%s' % (ok, ok2)


run('C6-explicit', '(C6) h_3=1+2t-t^2, h_4=1+4t-3t^2, h_5=1+8t-5t^2-2t^3, h_6=1+14t-7t^2-8t^3+2t^4；'
    '另 h_k(1)=N(k,k)=2（2<=k<=60）', chk_C6_explicit)

# ===========================================================================
# C7：固定 q 的分子
# ===========================================================================
KQ = 90
NUM = {}


def chk_C7():
    bad = []
    for q in range(1, MMAX + 1):
        ser = [N_from_U(TL, k, q) for k in range(KQ + 1)]
        num = smul(P_poly(q - 1), ser, KQ + 1)
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
    return not bad, first_bad(bad)


run('C7-poly', '(C7) P_{q-1}*sum_k N(k,q)x^k（N 由 DP 容斥，k<=90）是多项式：x^{3q-1}..x^90 系数全 0，'
    '次数恰 3q-2，首项 (q-1)!，最低项 2x^q（q>=2；q=1 为 x），1<=q<=20', chk_C7)


def chk_C7_given():
    given = {1: [0, 1], 2: [0, 0, 2, 0, 1], 3: [0, 0, 0, 2, 2, 7, 0, 2], 4: [0, 0, 0, 0, 2, 8, 13, 15, 29, 0, 6]}
    return all(NUM[q] == v for q, v in given.items()), ''


run('C7-given', '(C7) q=1..4 的分子：x；2x^2+x^4；2x^3+2x^4+7x^5+2x^7；2x^4+8x^5+13x^6+15x^7+29x^8+6x^10', chk_C7_given)


def chk_C7_ie_rec():
    bad = []
    for q in range(1, MMAX + 1):
        tot = []
        for i in range(0, q + 1):
            pr = [1]
            for v in range(i, q):
                pr = pmul(pr, b_poly(v))
            tot = padd(tot, pscale(pmul(W_poly(i - 1), pr), (-1) ** (q - i) * comb(q, i)))
        if tot != NUM[q]:
            bad.append(('ie', q))
    for q in range(3, MMAX + 1):
        rhs = padd(pmul([0, 1, 0, 2 * (q - 1)], NUM[q - 1]), pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), NUM[q - 2]))
        if rhs != NUM[q]:
            bad.append(('rec', q))
    return not bad, first_bad(bad)


run('C7-ie-rec', '(C7 证明所用的两个恒等式) Num_q = sum_i (-1)^{q-i}C(q,i) W_{i-1} prod_{v=i}^{q-1} b_v（1<=q<=20）；'
    'Num_q = (x+2(q-1)x^3)Num_{q-1} + (q-1)x^3 b_{q-2} Num_{q-2}（3<=q<=20）', chk_C7_ie_rec)

# ===========================================================================
# C8：推导链中「a_k(n)=p(n)+(-1)^n q(n)，deg p=2k，deg q=2k-2」（轻量核对，A/B 的正式工作不在此）
# ===========================================================================
def chk_C8_pq():
    bad = []
    for k in range(1, 16):
        npts = 2 * k + 3
        E = interpolate([2 * j for j in range(npts)], [TF[k][j] ** 2 for j in range(npts)])
        O = interpolate([2 * j + 1 for j in range(npts)], [TF[k][j + 1] * TF[k][j] for j in range(npts)])
        p = pscale(padd(E, O), Fraction(1, 2))
        q = pscale(psub(E, O), Fraction(1, 2))
        if (len(E) - 1, len(O) - 1, len(p) - 1, len(q) - 1) != (2 * k, 2 * k, 2 * k, 2 * k - 2):
            bad.append(('deg', k))
            continue
        lead_u = Fraction(2 if k >= 2 else 1, factorial(k))      # (C1)：lc(u_k)=2/k!（k>=2），lc(u_1)=1
        if q[-1] != lead_u ** 2 * k / (2 * 4 ** k) or p[-1] != lead_u ** 2 / 4 ** k:
            bad.append(('lc', k))
        for n in range(0, 2 * npts + 6):
            if peval(p, n) + (-1) ** n * peval(q, n) != TF[k][(n + 1) // 2] * TF[k][n // 2]:
                bad.append(('val', k, n))
                break
    return not bad, first_bad(bad)


run('C8-pq', '(C8 推导链) 由 DP 数据插值：a_k(n)=U_k(ceil(n/2))U_k(floor(n/2)) = p(n)+(-1)^n q(n)，deg p=2k、deg q=2k-2，'
    'lc(p)=c^2/4^k、lc(q)=c^2 k/(2*4^k)（c=lc(u_k)），对 n<=4k+11 逐点成立，1<=k<=15', chk_C8_pq)

# ---------------------------------------------------------------------------
print('TIME c1 total %.1fs' % (time.time() - T_START), flush=True)
print('SUMMARY c1 pass=%d fail=%d' % (NPASS, NFAIL), flush=True)
sys.exit(0 if NFAIL == 0 else 1)
