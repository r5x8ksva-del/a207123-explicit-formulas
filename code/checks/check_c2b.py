# -*- coding: utf-8 -*-
"""check_c2b.py —— 任务 C-2 组合路线（块分解）的正式核对模块。

契约：从任意目录用 `py -3.14 <本文件>` 运行；sys.path 插入 code 目录导入 core / polylib；
每条结论打印一行 `PASS <id> <描述（含范围）>` 或 `FAIL <id> ...`，最后一行 `SUMMARY c2b pass=<n> fail=<n>`；
全部通过退出码 0。只用精确整数 / Fraction（本模块没有任何浮点检查）。

独立性：块分解相关检查只用原始三元组条件 good3(a,b,c) <=> b==c 或 a>=max(b,c)
（任务说明第 1 节 (b)），不调用 core 的计数函数；公式检查对照 core.U_fast_table（高度 DP）、
本模块自写的细化 DP（直接三元组条件）、DFS 枚举、core.U_multichain（多重链定义）。
"""
import sys, os, time
from fractions import Fraction
from math import comb, factorial
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(HERE)
sys.path.insert(0, CODE)
import core                      # noqa: E402
from polylib import P_poly, b_poly, pmul, series_inv, series_mul, padd, pshift, pscale, trim   # noqa: E402

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass

T_START = time.time()
RES = []


def report(cid, ok, desc):
    print(('PASS ' if ok else 'FAIL ') + cid + ' ' + desc, flush=True)
    RES.append(bool(ok))


# =====================================================================
# 0. 基本工具（全部自写，只用三元组条件）
# =====================================================================
def good3(a, b, c):
    return b == c or (a >= b and a >= c)


def is_legal(h):
    return all(good3(h[i], h[i + 1], h[i + 2]) for i in range(len(h) - 2))


def binom(n, r):
    if r < 0 or n < 0 or r > n:
        return 0
    return comb(n, r)


def dfs_legal(k, m):
    out = []
    seq = []

    def rec():
        if len(seq) == k:
            out.append(tuple(seq))
            return
        for v in range(m + 1):
            if len(seq) >= 2 and not good3(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec()
            seq.pop()
    rec()
    return out


def ascents(h):
    return sum(1 for i in range(len(h) - 1) if h[i] < h[i + 1])


_ST = core.stirling2_table(80)


def S2(n, k):
    if n < 0 or k < 0:
        return 0
    return _ST[n][k]


_HC = {}


def hcomp(s, lo, hi):
    """h_s(lo..hi)，空区间 h_0=1；s<0 时 0。"""
    if s < 0:
        return 0
    key = (s, lo, hi)
    if key not in _HC:
        _HC[key] = core.h_complete(s, lo, hi)
    return _HC[key]


def refined_dp(K, m):
    """直接三元组条件的细化 DP：tot[k][s]、asc[k][s]（以上升结尾），0<=k<=K。"""
    S = K + 2
    tot = [[0] * S for _ in range(K + 1)]
    asc = [[0] * S for _ in range(K + 1)]
    tot[0][0] = 1
    if K >= 1:
        tot[1][0] = m + 1
    cnt = {}
    for a in range(m + 1):
        for b in range(m + 1):
            v = [0] * S
            v[1 if a < b else 0] = 1
            cnt[(a, b)] = v
            if K >= 2:
                tot[2][1 if a < b else 0] += 1
                if a < b:
                    asc[2][1] += 1
    for k in range(3, K + 1):
        new = {}
        for (a, b), vec in cnt.items():
            for c in range(m + 1):
                if not good3(a, b, c):
                    continue
                inc = 1 if b < c else 0
                tgt = new.setdefault((b, c), [0] * S)
                if inc:
                    for s in range(S - 1):
                        if vec[s]:
                            tgt[s + 1] += vec[s]
                else:
                    for s in range(S):
                        if vec[s]:
                            tgt[s] += vec[s]
        cnt = new
        for (b, c), vec in cnt.items():
            for s in range(S):
                tot[k][s] += vec[s]
                if b < c:
                    asc[k][s] += vec[s]
    return tot, asc


def ending_dp(K, m):
    """end0[k] = 长 k、末项为 0 的合法序列数；endT[k] = 长 k(>=3)、末三项 h_{k-2}<h_{k-1}=h_k 的合法序列数。"""
    end0 = [0] * (K + 1)
    endT = [0] * (K + 1)
    if K >= 1:
        end0[1] = 1
    if K >= 2:
        end0[2] = m + 1
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    for k in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if good3(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
                    if c == 0:
                        end0[k] += v
                    if a < b == c:
                        endT[k] += v
        cnt = new
    return end0, endT


# ---------------- 块 ----------------
def block_values(b):
    if b[0] == 'S':
        return [b[1]]
    if b[0] == 'T':
        return [b[2], b[1], b[1]]
    return [b[2], b[1]]


def concat(blocks):
    out = []
    for b in blocks:
        out.extend(block_values(b))
    return tuple(out)


def parse_det(h):
    """定理 1 证明中的确定性解析。"""
    h = list(h)
    blocks = []
    p, n = 0, len(h)
    while p < n:
        M = max(h[p:])
        if h[p] == M:
            blocks.append(('S', M)); p += 1
        elif n - p == 2:
            if h[p + 1] != M:
                return None
            blocks.append(('E', M, h[p])); p += 2
        else:
            if not (h[p + 1] == M and h[p + 2] == M):
                return None
            blocks.append(('T', M, h[p])); p += 3
    return blocks


def is_block_word(blocks, m):
    prev = m
    for i, b in enumerate(blocks):
        v = b[1]
        if v > prev or v < 0:
            return False
        if b[0] in ('T', 'E') and not (0 <= b[2] < v):
            return False
        if b[0] == 'E' and i != len(blocks) - 1:
            return False
        prev = v
    return True


def count_parses(h, m):
    n = len(h)
    memo = {}

    def f(p, top):
        if p == n:
            return 1
        key = (p, top)
        if key in memo:
            return memo[key]
        tot = 0
        x = h[p]
        if x <= top:
            tot += f(p + 1, x)
        if p + 3 <= n and x < h[p + 1] == h[p + 2] <= top:
            tot += f(p + 3, h[p + 1])
        if p + 2 == n and x < h[p + 1] <= top:
            tot += 1
        memo[key] = tot
        return tot
    return f(0, m)


def gen_block_words(k, m):
    out = []
    cur = []

    def rec(rem, top):
        if rem == 0:
            out.append(list(cur))
            return
        for v in range(top, -1, -1):
            cur.append(('S', v)); rec(rem - 1, v); cur.pop()
            if rem >= 3:
                for a in range(v):
                    cur.append(('T', v, a)); rec(rem - 3, v); cur.pop()
            if rem == 2:
                for a in range(v):
                    out.append(list(cur) + [('E', v, a)])
    rec(k, m)
    return out


def all_sequences_parse_check(K, m):
    """{0..m}^k（1<=k<=K）全部序列：非确定性解析数 == [合法]。后缀树增量计算。"""
    sys.setrecursionlimit(10000)
    fails = [0]
    cnt = [0]
    ones = [1] * (m + 1)
    rng = range(m + 1)

    def rec(s, legal, V0, V1, V2):
        n = len(s)
        if n >= 1:
            cnt[0] += 1
            if V0[m] != (1 if legal else 0):
                fails[0] += 1
        if n == K:
            return
        for x in rng:
            lg = legal and (n < 2 or good3(x, s[0], s[1]))
            newV = [0] * (m + 1)
            tcase = n >= 2 and x < s[0] == s[1]
            ecase = n == 1 and x < s[0]
            for top in rng:
                t = V0[x] if x <= top else 0
                if tcase and s[0] <= top:
                    t += V2[s[0]]
                if ecase and s[0] <= top:
                    t += 1
                newV[top] = t
            rec((x,) + s, lg, newV, V0, V1)
    rec((), True, ones, None, None)
    return cnt[0], fails[0]


# ---------------- 公式 ----------------
def A_complete(k, m, s):
    return S2(m + s, m) * binom(k + m - 2 * s, k - 3 * s)


def E_asc(k, m, s):
    if s < 1:
        return 0
    return sum(j * hcomp(s - 1, j, m) * binom(k + m - j - 2 * s, k + 1 - 3 * s) for j in range(1, m + 1))


def U_explicit(k, m):
    return sum(A_complete(k, m, s) + E_asc(k, m, s) for s in range(0, k // 3 + 2))


def Aj_total(n, m, j):
    """[x^n] prod_{v=j}^m b_v^{-1} = sum_s H(m,s,j) C(n+m-j-2s, n-3s)。"""
    if n < 0:
        return 0
    return sum(hcomp(s, j, m) * binom(n + m - j - 2 * s, n - 3 * s) for s in range(0, n // 3 + 1))


# =====================================================================
K, M = 30, 12
T = core.U_fast_table(K + 1, M)
DP = {m: refined_dp(K + 1, m) for m in range(M + 1)}

# ---------------- 0. 锚点 ----------------
ok = all(sum(DP[m][0][k]) == T[k][m] for m in range(M + 1) for k in range(K + 2))
ok2 = True
for m in range(0, 4):
    for k in range(0, 10):
        tot = Counter(); asc = Counter()
        for h in dfs_legal(k, m):
            s = ascents(h); tot[s] += 1
            if k >= 2 and h[-2] < h[-1]:
                asc[s] += 1
        for s in range(k + 3):
            if tot[s] != DP[m][0][k][s] or asc[s] != DP[m][1][k][s]:
                ok2 = False
ok3 = all(core.U_multichain(k, m) == T[k][m] for k in range(0, 8) for m in range(0, 5))
report('c2b.anchor', ok and ok2 and ok3,
       '自写细化DP(三元组条件)总数==core.U_fast_table (k<=31,m<=12)；细化DP按(s,结尾)==DFS枚举 (k<=9,m<=3)；'
       'core.U_fast_table==core.U_multichain多重链定义 (k<=7,m<=4)')

# ---------------- T1 块分解 ----------------
KB, MB = 10, 4
ok_bij = ok_par = ok_st = True
nseq = 0
for m in range(0, MB + 1):
    for k in range(0, KB + 1):
        L = dfs_legal(k, m)
        Ls = set(L)
        W = gen_block_words(k, m)
        imgs = [concat(w) for w in W]
        if not (all(is_block_word(w, m) for w in W) and all(len(x) == k for x in imgs)
                and all(is_legal(x) for x in imgs) and len(set(imgs)) == len(imgs) and set(imgs) == Ls):
            ok_bij = False
        for h in L:
            nseq += 1
            bl = parse_det(h)
            if bl is None or not is_block_word(bl, m) or concat(bl) != h or count_parses(h, m) != 1:
                ok_par = False
                continue
            nT = sum(1 for b in bl if b[0] == 'T'); nE = sum(1 for b in bl if b[0] == 'E')
            asc_end = k >= 2 and h[-2] < h[-1]
            if ascents(h) != nT + nE or asc_end != (nE == 1):
                ok_st = False
            if k >= 1 and max(h) != bl[0][1]:
                ok_st = False
            if k >= 1 and not asc_end and h[-1] != bl[-1][1]:
                ok_st = False
report('c2b.T1.bijection', ok_bij,
       '块词(层次非增,E只在末尾)->拼接 是到合法序列的双射：全部块词拼接合法、两两不同、像集==DFS合法序列集 (k<=10,m<=4)')
report('c2b.T1.unique_parse', ok_par,
       '每个合法序列恰有 1 种块分解(非确定性解析计数==1)，且证明中的确定性解析复原原序列 (k<=10,m<=4,共%d个)' % nseq)
report('c2b.T1.stats', ok_st,
       '统计量：上升数==#T+#E；以上升结尾<=>末块为E；max==首块层次；不以上升结尾时末项==末块层次 (k<=10,m<=4)')
tot_seq = 0; tot_fail = 0
for m in range(0, MB + 1):
    c, f = all_sequences_parse_check(KB, m)
    tot_seq += c; tot_fail += f
report('c2b.T1.allseq', tot_fail == 0,
       '全部 (m+1)^k 个序列：块分解方式数==[合法] (1<=k<=10,m<=4,共%d个序列)' % tot_seq)
ok = all(good3(a, v, c) == (c == v) for m in range(0, 13) for v in range(m + 1) for a in range(v) for c in range(m + 1))
report('c2b.T1.Eend', ok, '截断块只能在末尾：a<v 时 good3(a,v,c) <=> c==v（于是 [a,v] 后若再有项必构成T块），m<=12')

# ---------------- T2 母函数 ----------------
def gf_xy(Mx, Kx):
    """G_m(x,y) 由 (1-x-m y x^3) G_m = G_{m-1} + m y x^2 递推，G_{-1}=1；G[k] 为 y 的多项式。"""
    G = [[1]] + [[0] for _ in range(Kx)]
    out = []
    for m in range(0, Mx + 1):
        num = [list(c) for c in G]
        if Kx >= 2:
            c = num[2] + [0] * max(0, 2 - len(num[2]))
            c[1] += m
            num[2] = c
        H = []
        for k in range(Kx + 1):
            c = list(num[k])
            if k >= 1:
                a = H[k - 1]
                c = [(c[i] if i < len(c) else 0) + (a[i] if i < len(a) else 0) for i in range(max(len(c), len(a)))]
            if k >= 3:
                sh = [0] + [m * v for v in H[k - 3]]
                c = [(c[i] if i < len(c) else 0) + (sh[i] if i < len(sh) else 0) for i in range(max(len(c), len(sh)))]
            H.append(c)
        G = H
        out.append(H)
    return out

GS = gf_xy(M, K)
ok = True
for m in range(M + 1):
    tot = DP[m][0]
    for k in range(K + 1):
        poly = GS[m][k]
        if any((poly[s] if s < len(poly) else 0) != tot[k][s] for s in range(len(tot[k]))):
            ok = False
        if any(poly[s] for s in range(len(tot[k]), len(poly))):
            ok = False
report('c2b.T2.gf_xy', ok,
       '双变量母函数 (1-x-m*y*x^3)G_m(x,y)=G_{m-1}(x,y)+m*y*x^2, G_{-1}=1 的系数==细化DP的 U_k(m,s) (k<=30,m<=12,全部s)')

ok = True
for m in range(M + 1):
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
    ser = series_mul(W, series_inv(P_poly(m), K + 1), K + 1)
    if [int(c) for c in ser] != [T[k][m] for k in range(K + 1)]:
        ok = False
    rhs = padd([1], pscale(P_poly(m), -1))
    for j in range(m):
        rhs = padd(rhs, pscale(pshift(P_poly(j), 1), -1))
    if trim(pshift(W, 1)) != trim(rhs):
        ok = False
    # G_m = 1/P_m + x^2 sum_j j / prod_{v=j}^m b_v
    ser2 = list(series_inv(P_poly(m), K + 1))
    for j in range(1, m + 1):
        den = [1]
        for v in range(j, m + 1):
            den = pmul(den, b_poly(v))
        sj = series_inv(den, K + 1)
        for k in range(2, K + 1):
            ser2[k] += j * sj[k - 2]
    if [int(c) for c in ser2] != [T[k][m] for k in range(K + 1)]:
        ok = False
report('c2b.T2.WP', ok,
       'G_m=W_m/P_m (W_m=1+x^2*sum_j j*P_{j-1})、G_m=1/P_m+x^2*sum_j j/prod_{v=j}^m b_v 的展开==core DP，且多项式恒等式 x*W_m=1-P_m-x*sum_{j<m}P_j (k<=30,m<=12)')

def Us(k, m, s):
    if k < 0 or m < 0 or s < 0:
        return 0
    row = DP[m][0][k]
    return row[s] if s < len(row) else 0

ok = True
for m in range(0, M + 1):
    for k in range(0, K + 1):
        for s in range(0, k // 3 + 3):
            lhs = Us(k, m, s) - Us(k - 1, m, s) - Us(k, m - 1, s) - m * Us(k - 3, m, s - 1)
            rhs = (1 if (k == 0 and m == 0 and s == 0) else 0) + (m if (k == 2 and s == 1) else 0)
            if lhs != rhs:
                ok = False
report('c2b.T2.pde_xty', ok,
       '三变量 F(x,t,y)=sum U_k(m,s)x^k t^m y^s 满足 (1-x-t)F - y*x^3*t*dF/dt = 1 + y*x^2*t/(1-t)^2，'
       '等价于引理1的s细化 U_k(m,s)=U_k(m-1,s)+U_{k-1}(m,s)+m*U_{k-3}(m,s-1)+m[k=2][s=1]（U_k(-1,s)=[k=s=0]；逐系数, k<=30,m<=12）')

# ---------------- T3 系数提取与 Stirling / r-Stirling ----------------
def prod_inv_xy(j, m, Kx):
    """prod_{v=j}^m (1-x-v*y*x^3)^{-1} 的系数（关于 y 的多项式列表）。"""
    G = [[1]] + [[0] for _ in range(Kx)]
    for v in range(j, m + 1):
        H = []
        for k in range(Kx + 1):
            c = list(G[k])
            if k >= 1:
                a = H[k - 1]
                c = [(c[i] if i < len(c) else 0) + (a[i] if i < len(a) else 0) for i in range(max(len(c), len(a)))]
            if k >= 3:
                sh = [0] + [v * t for t in H[k - 3]]
                c = [(c[i] if i < len(c) else 0) + (sh[i] if i < len(sh) else 0) for i in range(max(len(c), len(sh)))]
            H.append(c)
        G = H
    return G

ok = True
for m in range(0, M + 1):
    for j in range(0, m + 1):
        G = prod_inv_xy(j, m, K)
        for n in range(K + 1):
            for s in range(0, n // 3 + 2):
                val = G[n][s] if s < len(G[n]) else 0
                if val != hcomp(s, j, m) * binom(n + m - j - 2 * s, n - 3 * s):
                    ok = False
report('c2b.T3.coef', ok,
       '[x^n y^s] prod_{v=j}^m (1-x-v*y*x^3)^{-1} = H(m,s,j)*C(n+m-j-2s,n-3s)，H(m,s,j)=h_s(j..m) (n<=30,0<=j<=m<=12)')

ok = True
from itertools import combinations
for L in range(0, 6):
    for s in range(0, 6):
        for j in range(0, 4):
            tot = 0
            for Tpos in combinations(range(L + s), s):
                Tset = set(Tpos)
                w = 1
                for p in Tpos:
                    bars_right = sum(1 for q in range(p + 1, L + s) if q not in Tset)
                    w *= (j + bars_right)
                tot += w
            if tot != hcomp(s, j, j + L):
                ok = False
report('c2b.T3.tbar', ok,
       '竖线模型引理：s个T与L根竖线的全部排列上 prod_T (j+T右侧竖线数) 之和 == h_s(j..j+L)（暴力, L<=5,s<=5,j<=3）')

def rgs_partitions(n):
    """长度 n 的限制增长串（块编号从 1 开始）。"""
    out = []
    cur = []

    def rec(mx):
        if len(cur) == n:
            out.append(tuple(cur)); return
        for b in range(1, mx + 2):
            cur.append(b); rec(max(mx, b)); cur.pop()
    if n == 0:
        return [()]
    rec(0)
    return out

ok = True
for m in range(0, 13):
    for s in range(0, 13 - m):
        if hcomp(s, 1, m) != S2(m + s, m) or hcomp(s, 0, m) != hcomp(s, 1, m):
            ok = False
for n in range(1, 10):
    parts = rgs_partitions(n)
    for m in range(1, n + 1):
        for j in range(1, m + 1):
            cnt = sum(1 for r in parts if max(r) == m and all(r[i] == i + 1 for i in range(j)))
            if cnt != hcomp(n - m, j, m):
                ok = False
report('c2b.T3.stirling', ok,
       'h_s(1..m)==h_s(0..m)==S(m+s,m) (m+s<=12)；h_s(j..m)==Broder r-Stirling {m+s,m}_j(把[m+s]分成m块且1..j两两不同块，限制增长串暴力枚举, m+s<=9)')

# ---------------- T4 显式公式 ----------------
okA = okE = True
for m in range(M + 1):
    tot, asc = DP[m]
    for k in range(K + 1):
        for s in range(len(tot[k])):
            if tot[k][s] - asc[k][s] != A_complete(k, m, s):
                okA = False
            if asc[k][s] != E_asc(k, m, s):
                okE = False
report('c2b.T4.complete_s', okA,
       '不以上升结尾、恰有 s 个上升的合法序列数 == S(m+s,m)*C(k+m-2s,k-3s)（单项！）(k<=30,m<=12,全部s)')
report('c2b.T4.E_s', okE,
       '以上升结尾、恰有 s 个上升的合法序列数 == sum_{j=1}^m j*H(m,s-1,j)*C(k+m-j-2s,k+1-3s) (k<=30,m<=12,全部s)')
ok = all(U_explicit(k, m) == T[k][m] for m in range(M + 1) for k in range(K + 1))
ok2 = all(U_explicit(k, m) == core.U_multichain(k, m) for k in range(0, 8) for m in range(0, 5))
report('c2b.T4.U', ok and ok2,
       'U_k(m)=sum_s S(m+s,m)C(k+m-2s,k-3s)+sum_{j=1}^m j sum_s H(m,s,j)C(k-2+m-j-2s,k-2-3s) == core DP (k<=30,m<=12) 且 == 多重链定义 (k<=7,m<=4)')
ok = all(Us(k, m, 0) == binom(k + m, k) for m in range(M + 1) for k in range(K + 1))
ok = ok and all(DP[m][1][k][1] == binom(k + m - 1, k) for m in range(1, M + 1) for k in range(2, K + 1))
ok = ok and all(Us(k, m, 1) == binom(m + 1, 2) * binom(k + m - 2, k - 3) + binom(k + m - 1, k)
                for m in range(M + 1) for k in range(2, K + 1))
report('c2b.T4.small_s', ok,
       'U_k(m,0)=C(k+m,k) (0<=k<=30)；以上升结尾且只1个上升的个数=C(k+m-1,k)、U_k(m,1)=C(m+1,2)C(k+m-2,k-3)+C(k+m-1,k) (2<=k<=30；k<=1 时不成立)，m<=12')

# 集合划分双射：完整块词 -> (S 位置集合, [m+s] 分成 m 块的划分)
def to_letters(blocks, m):
    letters = []
    lev = m
    for b in blocks:
        v = b[1]
        letters.extend(['|'] * (lev - v)); lev = v
        letters.append('S' if b[0] == 'S' else ('T', b[2]))
    letters.extend(['|'] * lev)
    return letters

def psi(blocks, m):
    L = to_letters(blocks, m)
    Spos = tuple(i for i, x in enumerate(L) if x == 'S')
    nonS = [x for x in L if x != 'S'][::-1]      # 从右往左
    rgs = []
    nb = 0
    for x in nonS:
        if x == '|':
            nb += 1; rgs.append(nb)
        else:
            a = x[1]
            if a + 1 > nb:
                return None
            rgs.append(a + 1)
    return Spos, tuple(rgs)

ok = True
for m in range(0, 4):
    for k in range(0, 10):
        imgs = {}
        for h in dfs_legal(k, m):
            if k >= 2 and h[-2] < h[-1]:
                continue
            bl = parse_det(h)
            s = sum(1 for b in bl if b[0] == 'T')
            im = psi(bl, m)
            if im is None:
                ok = False; continue
            Spos, rgs = im
            # 合法的限制增长串、恰 m 块、S 个数 k-3s、总位置数 k-2s+m
            valid = (len(Spos) == k - 3 * s and len(rgs) == m + s and all(0 <= p < k - 2 * s + m for p in Spos)
                     and (not rgs or (rgs[0] == 1 and all(rgs[i] <= max(rgs[:i]) + 1 for i in range(1, len(rgs)))))
                     and (max(rgs) if rgs else 0) == m)
            if not valid:
                ok = False
            imgs.setdefault(s, set()).add(im)
        for s, st in imgs.items():
            if len(st) != binom(k - 2 * s + m, k - 3 * s) * S2(m + s, m):
                ok = False
report('c2b.T4.setpart', ok,
       '显式双射：长k、s个上升的完整合法序列 <-> (k+m-2s个位置中选k-3s个放S) x ([m+s]分成m块的集合划分)；像合法、单射且像集大小==C(k+m-2s,k-3s)S(m+s,m) (k<=9,m<=3)')

# ---------------- T5 映射 (a)、A(k+1) 形式、与 (C4) 比较 ----------------
ok = True
for m in range(M + 1):
    end0, endT = ending_dp(K + 1, m)
    tot, asc = DP[m]
    for k in range(0, K + 1):
        if end0[k + 1] != sum(tot[k]) - sum(asc[k]):
            ok = False
        if k >= 2 and endT[k + 1] != sum(asc[k]):
            ok = False
ok2 = True
for m in range(0, 4):
    for k in range(2, 9):
        L = dfs_legal(k, m); L1 = set(dfs_legal(k + 1, m))
        comp = [h for h in L if not (h[-2] < h[-1])]
        ascw = [h for h in L if h[-2] < h[-1]]
        im0 = {h + (0,) for h in comp}
        imT = {h + (h[-1],) for h in ascw}
        tgt0 = {g for g in L1 if g[-1] == 0}
        tgtT = {g for g in L1 if g[-3] < g[-2] == g[-1]}
        if im0 != tgt0 or imT != tgtT or len(im0) != len(comp) or len(imT) != len(ascw):
            ok2 = False
        if any(parse_det(g)[-1] != ('S', 0) for g in tgt0) or any(parse_det(g)[-1][0] != 'T' for g in tgtT):
            ok2 = False
report('c2b.T5.append', ok and ok2,
       '映射(a)：不以上升结尾的长k序列 --补0--> 长k+1、末块为S_0的序列；以上升结尾的 --补末项--> 长k+1、末块为T块的完整序列；'
       '计数(DP, k<=30,m<=12)与显式映射(DFS, 2<=k<=8,m<=3)均为双射')
ok = all(Aj_total(k + 1, m, 0) - sum(Aj_total(k, m, j) for j in range(1, m + 1)) == T[k][m]
         for m in range(M + 1) for k in range(K + 1))
report('c2b.T5.Aminus', ok,
       'U_k(m) = A_m(k+1) - sum_{j=1}^m A^{(j)}_m(k)，A^{(j)}_m(n)=sum_s H(m,s,j)C(n+m-j-2s,n-3s) (k<=30,m<=12)')

def c_i(i, n):
    if n < 0:
        return 0
    return sum(binom(n - 2 * j, j) * i ** j for j in range(0, n // 3 + 1))

def Theta(t, n, m):
    return Fraction(sum((-1) ** r * comb(t, r) * c_i(m - r, n) for r in range(t + 1)), factorial(t))

ok = ok2 = True
for m in range(0, M + 1):
    for k in range(0, K + 1):
        if Theta(m, k + 1 + 3 * m, m) - sum(Theta(t, k + 3 * t, m) for t in range(m)) != T[k][m]:
            ok = False
        for t in range(0, m + 1):
            if Theta(t, k + 3 * t, m) != Aj_total(k, m, m - t):
                ok2 = False
report('c2b.T5.theta', ok and ok2,
       '(C4) 的 U=Theta_m(k+1+3m)-sum_t Theta_t(k+3t) == core DP，且逐项 Theta_t(n+3t)==A^{(m-t)}_m(n)=[x^n]P_{m-t-1}/P_m（含 t=m 即 (C4) 第二式）(k,n<=30,m<=12)')

# ---------------- T6 u 型单和不存在（留数-范数证书） ----------------
def make_field(i):
    ii = Fraction(i)

    def red(p):
        p = [Fraction(a) for a in p] + [Fraction(0)] * max(0, 3 - len(p))
        for d in range(len(p) - 1, 2, -1):
            c = p[d]
            if c:
                p[d] = Fraction(0)
                p[d - 3] += c / ii          # x^3 = (1 - x)/i
                p[d - 2] -= c / ii
        return p[:3]

    def mul(a, b):
        r = [Fraction(0)] * 5
        for s in range(3):
            for t in range(3):
                r[s + t] += a[s] * b[t]
        return red(r)

    one = [Fraction(1), Fraction(0), Fraction(0)]
    X = [Fraction(0), Fraction(1), Fraction(0)]
    Xinv = [Fraction(1), Fraction(0), ii]  # x^{-1} = i*x^2 + 1

    def xpow(n):
        base = X if n >= 0 else Xinv
        r = one
        for _ in range(abs(n)):
            r = mul(r, base)
        return r

    def norm(a):
        cols = [a, mul(a, X), mul(mul(a, X), X)]
        Mt = [[cols[c][r] for c in range(3)] for r in range(3)]
        return (Mt[0][0] * (Mt[1][1] * Mt[2][2] - Mt[1][2] * Mt[2][1])
                - Mt[0][1] * (Mt[1][0] * Mt[2][2] - Mt[1][2] * Mt[2][0])
                + Mt[0][2] * (Mt[1][0] * Mt[2][1] - Mt[1][1] * Mt[2][0]))
    return mul, xpow, norm, X


def is_field(i):
    q = 2
    while q * q * (q - 1) <= i:
        if q * q * (q - 1) == i:
            return False
        q += 1
    return True


def residue(i, m, which):
    mul, xpow, norm, X = make_field(i)
    tot = [Fraction(0)] * 3
    js = {'U': range(0, i + 1), 'E': range(1, i + 1), 'A': range(0, 1)}[which]
    for j in js:
        cj = 1 if j == 0 else j
        e = 0 if j == 0 else 2
        n = m - j + 1
        coef = Fraction(cj) / Fraction(i) ** n           # (1-x)^{-n} = i^{-n} x^{-3n}
        for ip in range(j, m + 1):
            if ip != i:
                coef *= Fraction(i, i - ip)               # (1 - ip/i)^{-1}
        term = xpow(e - 3 * n)
        tot = [tot[r] + coef * term[r] for r in range(3)]
    return tot, norm(tot)


def small_primes(n):
    ps = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        ps.append(n)
    return ps


def icbrt(n):
    lo, hi = 0, 1
    while hi ** 3 <= n:
        hi *= 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** 3 <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo


def witness(Nv, i):
    """返回 (True, 证书串) 若 N(nu) 去掉 i 的素因子后不是有理立方。证书优先给小素数 p∤i 及 v_p mod 3。"""
    ps = small_primes(i)
    num, den = abs(Nv.numerator), Nv.denominator
    for p in ps:
        while num % p == 0:
            num //= p
        while den % p == 0:
            den //= p
    for side, val in (('num', num), ('den', den)):
        v = val
        for p in range(2, 20000):
            if v % p == 0:
                e = 0
                while v % p == 0:
                    v //= p; e += 1
                if e % 3:
                    return True, 'p=%d v_p=%s%d' % (p, '+' if side == 'num' else '-', e)
    if icbrt(num) ** 3 != num or icbrt(den) ** 3 != den:
        return True, 'i-free part not a cube'
    return False, ''


cert_rows = []
okE = okU = okA = True
MCERT = 30
for m in range(1, MCERT + 1):
    for which in ('E', 'U'):
        if which == 'E' and m == 1:
            continue
        found = None
        for i in range(m, 0, -1):
            if not is_field(i):
                continue
            nu, Nv = residue(i, m, which)
            if Nv == 0:
                continue
            w, desc = witness(Nv, i)
            if w:
                found = (i, Nv, desc)
                break
        if found is None:
            if which == 'E':
                okE = False
            else:
                okU = False
        else:
            cert_rows.append('%s m=%d: u=1/%d N=%s %s' % (which, m, found[0],
                             found[1] if len(str(found[1])) < 40 else str(found[1])[:37] + '...', found[2]))
    # 合理性对照：A_m 本身是 u 型单和，必须在每个域极点都通过必要条件
    for i in range(m, 0, -1):
        if is_field(i):
            nu, Nv = residue(i, m, 'A')
            if Nv == 0 or witness(Nv, i)[0]:
                okA = False
# m=1 时 E(k,1) 本身是 u 型单和：E(k,1)=sum_s C(k-2-2s,s)
okE1 = all(sum(DP[1][1][k]) == sum(binom(k - 2 - 2 * s, s) for s in range(0, k + 1)) for k in range(K + 1))
for row in cert_rows:
    print('    [cert] ' + row)
report('c2b.T6.ushape_E', okE and okE1,
       '对 2<=m<=30：不存在整数 c,d 与有理 A_s 使 E(k,m)=sum_s A_s C(k+c-2s,d+s) 对全部 k>=0 成立（留数-范数证书见 [cert] 行）；'
       'm=1 时确有 E(k,1)=sum_s C(k-2-2s,s)（k<=30 核对）')
report('c2b.T6.ushape_U', okU,
       '对 1<=m<=30：不存在整数 c,d 与有理 A_s 使 U_k(m)=sum_s A_s C(k+c-2s,d+s) 对全部 k>=0 成立（证书见 [cert] 行）')
report('c2b.T6.sanity_A', okA,
       '对照：完整部分 A_m(k)=sum_s S(m+s,m)C(k+m-2s,m+s) 本身是 u 型单和，判据在每个域极点 u=1/i 都不报阻碍 (m<=30)')

# ---------------- T7 单和形状穷举（盒内，精确增量消元） ----------------
def test_shape(V, c, g, d, e):
    Kk = len(V) - 1
    cols = []
    for s in range(0, 3 * Kk + 11):
        r = d + e * s
        if r < 0:
            if e >= 0:
                continue
            break
        kmin = max(0, r + g * s - c)
        if kmin <= Kk:
            cols.append(s)
        elif g + e > 0:
            break
    pivots = {}
    checks = 0
    for k in range(Kk + 1):
        row = {}
        for s in cols:
            v = binom(k + c - g * s, d + e * s)
            if v:
                row[s] = Fraction(v)
        rhs = Fraction(V[k])
        for pc in [p for p in row if p in pivots]:
            coef = row.get(pc)
            if not coef:
                continue
            prow, prhs = pivots[pc]
            for cc, vv in prow.items():
                nv = row.get(cc, 0) - coef * vv
                if nv:
                    row[cc] = nv
                else:
                    row.pop(cc, None)
            rhs -= coef * prhs
        nz = [cc for cc, vv in row.items() if vv]
        if not nz:
            if rhs != 0:
                return False, checks, None
            checks += 1
            continue
        pc = min(nz)
        inv = 1 / row[pc]
        prow = {cc: vv * inv for cc, vv in row.items() if vv}
        prhs = rhs * inv
        for qc in list(pivots.keys()):
            qrow, qrhs = pivots[qc]
            coef = qrow.get(pc)
            if coef:
                for cc, vv in prow.items():
                    nv = qrow.get(cc, 0) - coef * vv
                    if nv:
                        qrow[cc] = nv
                    else:
                        qrow.pop(cc, None)
                qrhs -= coef * prhs
                pivots[qc] = (qrow, qrhs)
        pivots[pc] = (prow, prhs)
    sol = {pc: prhs for pc, (prow, prhs) in pivots.items() if len(prow) == 1}
    return True, checks, sol


tabE = {m: [sum(DP[m][1][k]) for k in range(K + 1)] for m in range(M + 1)}
tabU = {m: [T[k][m] for k in range(K + 1)] for m in range(M + 1)}
tabA = {m: [tabU[m][k] - tabE[m][k] for k in range(K + 1)] for m in range(M + 1)}


def ie(tab, k, q, base):
    return sum((-1) ** (q - i) * comb(q, i) * ((base if k == 0 else 0) if i == 0 else tab[i - 1][k]) for i in range(q + 1))


tabN = {q: [ie(tabU, k, q, 1) for k in range(K + 1)] for q in range(1, M + 1)}
tabNc = {q: [ie(tabA, k, q, 1) for k in range(K + 1)] for q in range(1, M + 1)}
tabNE = {q: [ie(tabE, k, q, 0) for k in range(K + 1)] for q in range(1, M + 1)}
okN = all(tabN[q][k] == core.N_from_U(T, k, q) for q in range(1, M + 1) for k in range(K + 1))

FAM = [(a, b, g, dl, e, z) for a in range(-1, 3) for b in range(-3, 4) for g in range(0, 4)
       for dl in range(0, 3) for e in range(-1, 4) for z in range(-3, 4)]
INF = [f for f in FAM if f[2] + f[4] >= 2]
summary = {}
okbox = True
for name, tab in (('A', tabA), ('E', tabE), ('U', tabU), ('N', tabN), ('Nc', tabNc), ('NE', tabNE)):
    cache = {}
    surv = []
    for (a, b, g, dl, e, z) in INF:
        refuted = False
        for m in range(1, M + 1):
            key = (m, a * m + b, g, dl * m + z, e)
            if key not in cache:
                cache[key] = test_shape(tab[m], a * m + b, g, dl * m + z, e)[0]
            if not cache[key]:
                refuted = True
                break
        if not refuted:
            surv.append((a, b, g, dl, e, z))
    summary[name] = surv
    if name == 'A':
        if sorted(surv) != [(1, 0, 2, 1, 1, 0), (1, 2, 2, 1, 1, -1)]:
            okbox = False
    elif surv:
        okbox = False
okrec = True
for m in range(1, M + 1):
    ok_, ch, sol = test_shape(tabA[m], m, 2, m, 1)
    if not ok_ or ch < 15 or any(sol.get(s) != S2(m + s, m) for s in range(0, (K - 0) // 3 + 1) if s in sol):
        okrec = False
report('c2b.T7.box', okbox and okrec and okN,
       '单和形状 V(k)=sum_s A(m,s)C(k+alpha*m+beta-gamma*s, delta*m+eps*s+zeta)，参数盒 alpha∈[-1,2],beta∈[-3,3],gamma∈[0,3],delta∈[0,2],eps∈[-1,3],zeta∈[-3,3]'
       '（11760族，其中 gamma+eps>=2 有真检验的 %d 族）：对 E、U、N、N^c、N^E 无一族在 k<=30,m(或q)=1..12 上可解；'
       '对完整部分 A 只存活已知形状(1,0,2,1,1,0)及其指标平移(1,2,2,1,1,-1)，并找回 A(m,s)=S(m+s,m)（引擎对照）' % len(INF))

# E(k,m,s) 单项反例：(m,s)=(2,2)
V22 = [DP[2][1][k][2] for k in range(K + 1)]
ok22 = all(V22[k] == ((k - 4) * (3 * k - 1) // 2 if k >= 4 else 0) for k in range(K + 1))
none_single = True
for c in range(-40, 41):
    for d in range(0, 41):
        ratio = None; good = True
        for k in range(K + 1):
            bb = binom(k + c, d)
            if bb == 0:
                if V22[k] != 0:
                    good = False; break
            else:
                r = Fraction(V22[k], bb)
                if ratio is None:
                    ratio = r
                elif r != ratio:
                    good = False; break
        if good and ratio:
            none_single = False
report('c2b.T7.Es_single', ok22 and none_single,
       'E(k,2,2)=(k-4)(3k-1)/2 (k>=4, 否则0)，根 4 与 1/3 不是相邻整数，故不存在 A*C(k+c,d) 单项表示；数值上 c∈[-40,40],d∈[0,40] 全无解 (k<=30)')

# E(k,m,s) 的「最终」单项性：k>=3s-1 时是 k 的 m+s-2 次多项式；单项 <=> 根恰为 deg 个相邻整数
def interp_vals(ks, vs):
    """Newton 插值，返回求值函数（精确 Fraction）。"""
    n = len(ks)
    coef = [Fraction(v) for v in vs]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (ks[i] - ks[i - j])

    def ev(x):
        r = coef[-1]
        for i in range(n - 2, -1, -1):
            r = r * (x - ks[i]) + coef[i]
        return r
    return ev

single_ev = []
okfit = True
for m in range(1, 9):
    for s in range(1, 7):
        deg = m + s - 2
        ks = list(range(3 * s - 1, 3 * s + deg))            # deg+1 个点
        ev = interp_vals(ks, [E_asc(k, m, s) for k in ks])
        if not all(ev(k) == E_asc(k, m, s) for k in range(3 * s - 1, 3 * s + 45)):
            okfit = False
        if not all(E_asc(k, m, s) == DP[m][1][k][s] for k in range(3 * s - 1, K + 1) if s < len(DP[m][1][k])):
            okfit = False
        roots = [r for r in range(-300, 301) if ev(r) == 0]
        if len(roots) == deg and (deg == 0 or roots == list(range(roots[0], roots[0] + deg))):
            single_ev.append((m, s))
expect = sorted([(1, s) for s in range(1, 7)] + [(m, 1) for m in range(2, 9)])
report('c2b.T7.Es_eventual', okfit and sorted(single_ev) == expect,
       '对 k>=3s-1，E(k,m,s) 是 k 的 m+s-2 次多项式；它等于 A*C(k+c,deg)（根为相邻整数）当且仅当 s=1 或 m=1 (m<=8,s<=6)：'
       'E(k,m,1)=C(k+m-1,k)(k>=2)、E(k,1,s)=C(k-2s,s-1)；m>=2 且 s>=2 时连「大 k 成立」的单项表示都没有')

# 两项 u 型：V(k)=sum_s [A_s C(k+c1-2s,d1+s) + B_s C(k+c2-2s,d2+s)]
def test_two(V, c1, d1, c2, d2):
    Kk = len(V) - 1
    fams = [(c1, d1), (c2, d2)]
    cols = []
    for f, (c, d) in enumerate(fams):
        for s in range(0, Kk + 3):
            r = d + s
            if r < 0:
                continue
            if max(0, r + 2 * s - c) <= Kk:
                cols.append((f, s))
    pivots = {}
    for k in range(Kk + 1):
        row = {}
        for (f, s) in cols:
            c, d = fams[f]
            v = binom(k + c - 2 * s, d + s)
            if v:
                row[(f, s)] = Fraction(v)
        rhs = Fraction(V[k])
        for pc in [p for p in row if p in pivots]:
            coef = row.get(pc)
            if not coef:
                continue
            prow, prhs = pivots[pc]
            for cc, vv in prow.items():
                nv = row.get(cc, 0) - coef * vv
                if nv:
                    row[cc] = nv
                else:
                    row.pop(cc, None)
            rhs -= coef * prhs
        nz = [cc for cc, vv in row.items() if vv]
        if not nz:
            if rhs != 0:
                return False
            continue
        pc = min(nz)
        inv = 1 / row[pc]
        prow = {cc: vv * inv for cc, vv in row.items() if vv}
        prhs = rhs * inv
        for qc in list(pivots.keys()):
            qrow, qrhs = pivots[qc]
            coef = qrow.get(pc)
            if coef:
                for cc, vv in prow.items():
                    nv = qrow.get(cc, 0) - coef * vv
                    if nv:
                        qrow[cc] = nv
                    else:
                        qrow.pop(cc, None)
                qrhs -= coef * prhs
                pivots[qc] = (qrow, qrhs)
        pivots[pc] = (prow, prhs)
    return True

two_ok = True
two_counts = []
for name, m in (('E', 3), ('U', 2)):
    V = tabE[m] if name == 'E' else tabU[m]
    shapes = [(c, d) for c in range(-6, 3 * m + 7) for d in range(-3, 2 * m + 5)]
    npairs = 0; nsol = 0
    for i1, (c1, d1) in enumerate(shapes):
        for (c2, d2) in shapes[i1 + 1:]:
            if c1 + 2 * d1 == c2 + 2 * d2:
                continue          # 同一 N=c+2d+3 类，两族只差求和指标平移，归入单族情形（定理 6）
            npairs += 1
            if test_two(V, c1, d1, c2, d2):
                nsol += 1
    two_counts.append('%s m=%d: %d pairs, %d solvable' % (name, m, npairs, nsol))
    if nsol:
        two_ok = False
# 对照：m=2 的 E 与 m=1 的 U 确实是两项 u 型（引擎能找到真实存在的两项表示）
two_pos2 = any(test_two(tabE[2], c1, d1, c2, d2) for (c1, d1, c2, d2) in [(-2, 0, -2, 1), (-2, 0, -1, 1)])
two_pos3 = test_two(tabU[1], -2, 0, 1, 1)
report('c2b.T7.twoterm', two_ok and two_pos2 and two_pos3,
       '两项 u 型 sum_s[A_s C(k+c1-2s,d1+s)+B_s C(k+c2-2s,d2+s)]：E(k,3) 与 U_k(2) 在盒 c∈[-6,3m+6], d∈[-3,2m+4] 内全部形状对都不可解（%s；k<=30）；'
       '对照：E(k,2)、U_k(1) 在盒内确有两项表示' % '; '.join(two_counts))

# ---------------- T8 合法满射词：T 骨架 + 覆盖 ----------------
def arc_systems(p, s):
    out = []
    cur = []

    def rec(rem, top):
        if rem == 0:
            out.append(tuple(cur)); return
        for v in range(top, 0, -1):
            for a in range(v):
                cur.append((v, a)); rec(rem - 1, v); cur.pop()
    rec(s, p - 1)
    return out


def Hs(i, s):
    if i == 0:
        return 1 if s == 0 else 0
    return S2(i - 1 + s, i - 1)


def R_ie(p, s):
    return sum((-1) ** (p - i) * comb(p, i) * Hs(i, s) for i in range(p + 1))


okR = True
for p in range(0, 8):
    for s in range(0, 5):
        br = sum(1 for sy in arc_systems(p, s) if set(x for arc in sy for x in arc) == set(range(p)))
        if br != R_ie(p, s):
            okR = False
dfact = [1]
for s in range(1, 9):
    dfact.append(dfact[-1] * (2 * s - 1))
okR = okR and all(R_ie(2 * s, s) == dfact[s] for s in range(0, 9))
okR = okR and all(R_ie(p, s) == 0 for s in range(0, 9) for p in range(2 * s + 1, 2 * s + 6))
report('c2b.T8.R', okR,
       'R(p,s)(端点恰为{0..p-1}的s弧T骨架数) 暴力枚举==sum_i(-1)^{p-i}C(p,i)S(i-1+s,i-1) (p<=7,s<=4)；R(2s,s)=(2s-1)!!、p>2s 时 R=0 (s<=8)')

okb = True
for k in range(1, 9):
    cntc = Counter(); cnte = Counter()
    for h in dfs_legal(k, k - 1):
        st = set(h); q = len(st)
        if st != set(range(q)):
            continue
        if k >= 2 and h[-2] < h[-1]:
            cnte[q] += 1
        else:
            cntc[q] += 1
    for q in range(1, min(k, M) + 1):
        if cntc[q] != tabNc[q][k] or cnte[q] != tabNE[q][k]:
            okb = False
report('c2b.T8.Nsplit', okb and okN,
       'N=N^c+N^E：按结尾拆分的满射词数（容斥自细化DP）==DFS暴力枚举 (k<=8)；N 容斥==core.N_from_U (k<=30,q<=12)')

Rc = {}
def Rm(p, s):
    if (p, s) not in Rc:
        Rc[(p, s)] = R_ie(p, s)
    return Rc[(p, s)]

def Nc_formula(k, q):
    tot = 0
    for s in range(0, k // 3 + 1):
        for p in range(0, 2 * s + 1):
            r = Rm(p, s)
            if r:
                tot += comb(q, p) * r * binom(k - 2 * s + p - 1, s + q - 1)
    return tot

ok = all(Nc_formula(k, q) == tabNc[q][k] for q in range(1, M + 1) for k in range(0, K + 1))
report('c2b.T8.Nc', ok,
       'N^c(k,q)=sum_{s>=0} sum_{p=0}^{2s} C(q,p) R(p,s) C(k-2s+p-1, s+q-1)（正项双和；N^c=不以上升结尾的合法满射词）(k<=30,q<=12)')

# N^E 的骨架三重和：需记录骨架最小头 h0。R'(p,s,h0) 用容斥公式，并与骨架暴力枚举对照（s<=4）
def Rprime(p, s, h0):
    tot = 0
    for z1 in range(0, h0 + 1):
        for z2 in range(0, p - h0):
            w = p - z1 - z2
            r0 = h0 - z1
            tot += (-1) ** (z1 + z2) * comb(h0, z1) * comb(p - 1 - h0, z2) * (hcomp(s, r0, w - 1) - hcomp(s, r0 + 1, w - 1))
    return tot

okRp = True
for s in range(1, 5):
    for p in range(2, 2 * s + 1):
        cntp = Counter()
        for sy in arc_systems(p, s):
            if set(x for arc in sy for x in arc) == set(range(p)):
                cntp[min(v for v, a in sy)] += 1
        for h0 in range(0, p):
            if cntp[h0] != Rprime(p, s, h0):
                okRp = False
okRp = okRp and all(sum(Rprime(p, s, h0) for h0 in range(p)) == R_ie(p, s) for s in range(1, 11) for p in range(2, 2 * s + 1))
RP = {}
for s in range(1, (K + 1) // 3 + 1):
    for p in range(2, 2 * s + 1):
        for h0 in range(1, p):
            v = Rprime(p, s, h0)
            if v:
                RP[(p, s, h0)] = v

def NE_formula(k, q):
    return sum(r * binom(q - 1 - h0, p - 1 - h0) * binom(k - 1 - 2 * s + p - h0, s + q - 2 - h0)
               for (p, s, h0), r in RP.items())

ok = all(NE_formula(k, q) == tabNE[q][k] for q in range(1, M + 1) for k in range(0, K + 1))
report('c2b.T8.NE', ok and okRp,
       "N^E(k,q)=sum_{s>=1,p,h0} R'(p,s,h0) C(q-1-h0,p-1-h0) C(k-1-2s+p-h0, s+q-2-h0) (k<=30,q<=12)；"
       "R'(端点恰为{0..p-1}且最小头为h0的s弧骨架数)=sum_{z1,z2}(-1)^{z1+z2}C(h0,z1)C(p-1-h0,z2)[h_s(h0-z1..p-1-z1-z2)-h_s(h0-z1+1..p-1-z1-z2)]"
       "，与骨架暴力枚举一致(s<=4)且 sum_h0 R'=R (s<=10)")

E2c = {}
def eul2(n, kk):
    if n == 0:
        return 1 if kk == 0 else 0
    if kk < 0 or kk >= n:
        return 0
    if (n, kk) not in E2c:
        E2c[(n, kk)] = (kk + 1) * eul2(n - 1, kk) + (2 * n - 1 - kk) * eul2(n - 1, kk - 1)
    return E2c[(n, kk)]

ok = all(R_ie(p, s) == sum(eul2(s, kk) * binom(2 * s - 2 - kk, 2 * s - p) for kk in range(0, s))
         for s in range(1, 12) for p in range(0, 2 * s + 3))
report('c2b.T8.Reul', ok, 'R(p,s)=sum_k <<s,k>> C(2s-2-k,2s-p)（<<s,k>> 为二阶 Euler 数）(1<=s<=11, 0<=p<=2s+2)')

# ---------------- T9 失败方向里用到的两个恒等式（级数核对） ----------------
def ser_prod_inv(j, m, n):
    den = [1]
    for v in range(j, m + 1):
        den = pmul(den, b_poly(v))
    return series_inv(den, n)

NS = 25
okt = okp = True
for m in range(1, 9):
    Q = {j: ser_prod_inv(j, m, NS) for j in range(0, m + 1)}
    lhs = [0] * NS
    for j in range(1, m + 1):
        for k in range(NS):
            if k >= 1:
                lhs[k] += Q[j][k - 1]
            if k >= 3:
                lhs[k] += j * Q[j][k - 3]
    rhs = list(Q[1]); rhs[0] -= 1
    if [Fraction(a) for a in lhs] != [Fraction(a) for a in rhs]:
        okt = False
    Lser = [sum(Q[i][k] for i in range(0, m + 1)) for k in range(NS)]
    Rser = [Fraction(0)] * NS
    for v in range(1, m + 1):
        bv = series_inv(b_poly(v), NS)
        inner = [Fraction(0)] * NS
        for r in range(0, v + 1):
            n = m - v + r
            c = Fraction(v ** n, factorial(r))
            for k in range(NS):
                inner[k] += c * (binom(k + n - 1, k) if n > 0 else (1 if k == 0 else 0))
        pr = series_mul(bv, inner, NS)
        cf = Fraction((-1) ** (m - v), factorial(m - v))
        for k in range(NS):
            Rser[k] += cf * pr[k]
    if [Fraction(a) for a in Lser] != Rser:
        okp = False
report('c2b.T9.misc', okt and okp,
       '望远镜关系 x*sum_{j=1}^m Q_j + x^3*sum_j j*Q_j = Q_1 - 1（Q_j=prod_{v=j}^m b_v^{-1}）；部分分式 sum_{i=0}^m Q_i = '
       'sum_{v=1}^m (-1)^{m-v}/((m-v)! b_v) * sum_{r=0}^{v} v^{m-v+r}(1-x)^{-(m-v+r)}/r!（截断指数和）；级数核对到 x^24，m<=8')

npass = sum(RES); nfail = len(RES) - npass
print('[time] %.1fs' % (time.time() - T_START), flush=True)
print('SUMMARY c2b pass=%d fail=%d' % (npass, nfail), flush=True)
sys.exit(0 if nfail == 0 else 1)
