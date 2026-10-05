# -*- coding: utf-8 -*-
"""r-c2b 复核脚本 1：块分解、按上升数细化的公式、竖线模型、集合划分双射、补0/补末项映射。

全部自写，只用原始三元组条件 good(a,b,c) <=> b==c or a>=max(b,c)；
只从 core 取 U_multichain / a_direct 作为原始定义的独立对照（不用 c2b 的任何代码）。
解析算法与 c2b 不同：c2b 用「当前后缀最大值」确定首块，这里用「谷 = 上升起点」的局部规则。
"""
import sys, os, time, itertools
from math import comb
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, CODE)
import core  # noqa

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass

T0 = time.time()
RESULTS = []


def rep(name, ok, msg=''):
    RESULTS.append((name, ok))
    print(('OK   ' if ok else 'BAD  ') + name + ('  ' + msg if msg else ''), flush=True)


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def C(n, r):
    if n < 0 or r < 0 or r > n:
        return 0
    return comb(n, r)


# ---------- 自写 Stirling / 完全齐次 ----------
def stirling_table(N):
    S = [[0] * (N + 1) for _ in range(N + 1)]
    S[0][0] = 1
    for n in range(1, N + 1):
        for k in range(1, n + 1):
            S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
    return S


ST = stirling_table(90)


def hsym(s, lo, hi):
    """h_s(lo..hi) 用生成函数系数：prod 1/(1-v t) 的 t^s 系数。"""
    if s < 0:
        return 0
    row = [1] + [0] * s
    for v in range(lo, hi + 1):
        for t in range(1, s + 1):
            row[t] += v * row[t - 1]
    return row[s]


# ---------- 自写细化 DP：按 (末尾是否上升, s) 计数 ----------
def refined(K, m):
    """返回 comp[k][s], ascend[k][s]（k=0..K）。"""
    SM = K + 2
    comp = [[0] * SM for _ in range(K + 1)]
    ascd = [[0] * SM for _ in range(K + 1)]
    comp[0][0] = 1
    if K >= 1:
        comp[1][0] = m + 1
    if K < 2:
        return comp, ascd
    st = {}
    for a in range(m + 1):
        for b in range(m + 1):
            vec = [0] * SM
            vec[1 if a < b else 0] = 1
            st[(a, b)] = vec
    def tally(k, st):
        for (a, b), vec in st.items():
            tgt = ascd[k] if a < b else comp[k]
            for s, v in enumerate(vec):
                tgt[s] += v
    tally(2, st)
    for k in range(3, K + 1):
        nst = {}
        for (a, b), vec in st.items():
            for c in range(m + 1):
                if not good(a, b, c):
                    continue
                key = (b, c)
                tv = nst.get(key)
                if tv is None:
                    tv = [0] * SM
                    nst[key] = tv
                if b < c:
                    for s in range(SM - 1):
                        tv[s + 1] += vec[s]
                else:
                    for s in range(SM):
                        tv[s] += vec[s]
        st = nst
        tally(k, st)
    return comp, ascd


# ---------- 1. 细化 DP 本身对照全序列暴力 ----------
ok = True
for m in range(0, 4):
    for k in range(0, 8 if m <= 2 else 7):
        comp, ascd = refined(k, m)
        bc = {}
        ba = {}
        for h in itertools.product(range(m + 1), repeat=k):
            if not all(good(h[i], h[i + 1], h[i + 2]) for i in range(k - 2)):
                continue
            s = sum(1 for i in range(k - 1) if h[i] < h[i + 1])
            if k >= 2 and h[-2] < h[-1]:
                ba[s] = ba.get(s, 0) + 1
            else:
                bc[s] = bc.get(s, 0) + 1
        for s in range(k + 2):
            if comp[k][s] != bc.get(s, 0) or ascd[k][s] != ba.get(s, 0):
                ok = False
rep('dp_vs_brute', ok, '自写细化 DP == 全序列暴力枚举 (m<=3, k<=7/6)')

# ---------- 2. 原始矩阵定义对照（a_direct / 多重链） ----------
KK, MM = 40, 14
TAB = {m: refined(KK, m) for m in range(MM + 1)}
Utot = {m: [sum(TAB[m][0][k]) + sum(TAB[m][1][k]) for k in range(KK + 1)] for m in range(MM + 1)}
ok = all(core.U_multichain(k, m) == Utot[m][k] for k in range(0, 9) for m in range(0, 6))
rep('dp_vs_multichain', ok, 'U_k(m)(自写DP) == core.U_multichain 多重链定义 (k<=8, m<=5)')
ok = True
for k in range(1, 6):
    for n in range(1, 9):
        a = core.a_direct(n, k)
        if a != Utot[(n + 1) // 2][k] * Utot[n // 2][k]:
            ok = False
rep('dp_vs_matrix', ok, 'a_k(n)=U_k(ceil(n/2))U_k(floor(n/2)) 用自写DP == core.a_direct 原题矩阵计数 (k<=5, n<=8)')
FT = core.U_fast_table(KK, MM)
ok = all(FT[k][m] == Utot[m][k] for k in range(KK + 1) for m in range(MM + 1))
rep('dp_vs_coreDP', ok, '自写DP == core.U_fast_table (k<=40, m<=14)')


# ---------- 3. 块分解：独立的「谷」解析 ----------
def parse_valley(h):
    """局部规则：p 是谷 <=> h[p] < h[p+1]；谷后若还有两项则为 T，否则为 E。返回块列表或 None（若规则不自洽）。"""
    out = []
    p, n = 0, len(h)
    while p < n:
        if p + 1 < n and h[p] < h[p + 1]:
            if p + 2 < n:
                if h[p + 2] != h[p + 1]:
                    return None
                out.append(('T', h[p + 1], h[p]))
                p += 3
            else:
                out.append(('E', h[p + 1], h[p]))
                p += 2
        else:
            out.append(('S', h[p]))
            p += 1
    return out


def is_blockword(bl, m):
    top = m
    for i, b in enumerate(bl):
        v = b[1]
        if v > top or v < 0:
            return False
        if b[0] != 'S' and not (0 <= b[2] < v):
            return False
        if b[0] == 'E' and i != len(bl) - 1:
            return False
        top = v
    return True


def concat(bl):
    out = []
    for b in bl:
        if b[0] == 'S':
            out.append(b[1])
        elif b[0] == 'T':
            out += [b[2], b[1], b[1]]
        else:
            out += [b[2], b[1]]
    return tuple(out)


def all_blockwords(k, m):
    """独立生成长度恰为 k、层次<=m 的全部块词（迭代版）。"""
    res = []
    stack = [((), k, m)]
    while stack:
        pre, rem, top = stack.pop()
        if rem == 0:
            res.append(pre)
            continue
        for v in range(0, top + 1):
            stack.append((pre + (('S', v),), rem - 1, v))
            for a in range(v):
                if rem >= 3:
                    stack.append((pre + (('T', v, a),), rem - 3, v))
                if rem == 2:
                    res.append(pre + (('E', v, a),))
    return res


ok_parse = ok_bij = ok_illegal = True
nleg = 0
for m in range(0, 5):
    for k in range(0, 9):
        legal = set()
        for h in itertools.product(range(m + 1), repeat=k):
            lg = all(good(h[i], h[i + 1], h[i + 2]) for i in range(k - 2))
            bl = parse_valley(h)
            if lg:
                legal.add(h)
                nleg += 1
                if bl is None or not is_blockword(bl, m) or concat(bl) != h:
                    ok_parse = False
            else:
                # 非法序列：要么谷规则不自洽，要么解析出的不是块词（层次上升 / E 不在末尾不可能）
                if bl is not None and is_blockword(bl, m) and concat(bl) == h:
                    ok_illegal = False
        W = all_blockwords(k, m)
        imgs = [concat(w) for w in W]
        if len(set(imgs)) != len(imgs) or set(imgs) != legal:
            ok_bij = False
        if any(not all(good(x[i], x[i + 1], x[i + 2]) for i in range(len(x) - 2)) for x in imgs):
            ok_bij = False
rep('block_bijection', ok_bij and ok_parse and ok_illegal,
    '块词->拼接是到合法序列的双射；谷规则解析对每个合法序列给出块词且复原；非法序列不能解析成块词 (m<=4,k<=8, 合法序列共%d个)' % nleg)

# 统计量：上升数 = #T+#E；末尾上升 <=> 末块 E；值集 = 层次 ∪ 谷
ok = True
for m in range(0, 5):
    for k in range(1, 9):
        for w in all_blockwords(k, m):
            h = concat(w)
            asc = sum(1 for i in range(k - 1) if h[i] < h[i + 1])
            nT = sum(1 for b in w if b[0] == 'T'); nE = sum(1 for b in w if b[0] == 'E')
            if asc != nT + nE:
                ok = False
            if (k >= 2 and h[-2] < h[-1]) != (nE == 1):
                ok = False
            vals = set(b[1] for b in w) | set(b[2] for b in w if b[0] != 'S')
            if vals != set(h) or max(h) != w[0][1]:
                ok = False
rep('block_stats', ok, '上升数=#T+#E、末尾上升<=>末块E、值集=层次∪谷值、max=首块层次 (m<=4, 1<=k<=8)')

# ---------- 4. 定理 4：按 s 分层公式，扩大到 k<=40, m<=14 ----------
def A_s(k, m, s):
    return ST[m + s][m] * C(k + m - 2 * s, k - 3 * s)


def E_s(k, m, s):
    if s < 1:
        return 0
    return sum(j * hsym(s - 1, j, m) * C(k + m - j - 2 * s, k + 1 - 3 * s) for j in range(1, m + 1))


okA = okE = True
for m in range(0, MM + 1):
    comp, ascd = TAB[m]
    for k in range(0, KK + 1):
        for s in range(0, KK + 2):
            if comp[k][s] != A_s(k, m, s):
                okA = False
            if ascd[k][s] != E_s(k, m, s):
                okE = False
rep('T4a_complete_s', okA, '完整序列、恰 s 个上升 == S(m+s,m)C(k+m-2s,k-3s) (k<=40, m<=14, 全部 s)')
rep('T4b_ascend_s', okE, '以上升结尾、恰 s 个上升 == sum_j j H(m,s-1,j) C(k+m-j-2s,k+1-3s) (k<=40, m<=14, 全部 s)')


def U_thm4(k, m):
    t1 = sum(ST[m + s][m] * C(k + m - 2 * s, k - 3 * s) for s in range(0, k // 3 + 1))
    t2 = 0
    for j in range(1, m + 1):
        for s in range(0, max(0, (k - 2) // 3) + 1):
            t2 += j * hsym(s, j, m) * C(k - 2 + m - j - 2 * s, k - 2 - 3 * s)
    return t1 + t2


ok = all(U_thm4(k, m) == Utot[m][k] for k in range(KK + 1) for m in range(MM + 1))
rep('T4c_U', ok, '定理4 U_k(m) 公式 == 自写DP (k<=40, m<=14)')

# 推论 4.1
ok = all(TAB[m][0][k][0] + TAB[m][1][k][0] == C(k + m, k) for m in range(MM + 1) for k in range(KK + 1))
ok2 = all(TAB[m][1][k][1] == C(k + m - 1, k) for m in range(0, MM + 1) for k in range(2, KK + 1))
ok3 = all(TAB[m][0][k][1] + TAB[m][1][k][1] == C(m + 1, 2) * C(k + m - 2, k - 3) + C(k + m - 1, k)
          for m in range(MM + 1) for k in range(2, KK + 1))
fail01 = [(k, m) for m in range(1, 4) for k in range(0, 2)
          if TAB[m][1][k][1] != C(k + m - 1, k)]
rep('C4.1_small_s', ok and ok2 and ok3 and len(fail01) == 6,
    'U_k(m,0)=C(k+m,k)；k>=2 时 E(k,m,1)=C(k+m-1,k)、U_k(m,1)=C(m+1,2)C(k+m-2,k-3)+C(k+m-1,k) (k<=40,m<=14)；k<=1 且 m>=1 时确实不成立：%s' % fail01)

# ---------- 5. s-细化递推与三变量 PDE（直接从 DP 表取系数） ----------
def Uks(k, m, s):
    if k < 0 or s < 0:
        return 0
    if m < 0:
        return 1 if (k == 0 and s == 0) else 0
    if s >= KK + 2:
        return 0
    return TAB[m][0][k][s] + TAB[m][1][k][s]


ok = True
for m in range(0, MM + 1):
    for k in range(0, KK + 1):
        for s in range(0, KK + 1):
            lhs = Uks(k, m, s)
            rhs = Uks(k, m - 1, s) + Uks(k - 1, m, s) + m * Uks(k - 3, m, s - 1) + (m if (k == 2 and s == 1) else 0)
            if lhs != rhs:
                ok = False
rep('T2c_srefined_recursion', ok, 'U_k(m,s)=U_k(m-1,s)+U_{k-1}(m,s)+m U_{k-3}(m,s-1)+m[k=2][s=1] (k<=40,m<=14,全部 s)')

# PDE：(1-x-t)F - y x^3 t dF/dt = 1 + y x^2 t/(1-t)^2，取 [x^k t^m y^s] 逐系数（独立展开右边）
ok = True
for k in range(0, 25):
    for m in range(0, MM + 1):
        for s in range(0, 10):
            lhs = Uks(k, m, s) - Uks(k - 1, m, s) - Uks(k, m - 1, s) * (1 if m >= 1 else 0) - (m * Uks(k - 3, m, s - 1))
            # [x^k t^m y^s] of RHS: 1 -> k=m=s=0 ; y x^2 t/(1-t)^2 = y x^2 sum_m m t^m
            rhs = (1 if (k == 0 and m == 0 and s == 0) else 0) + (m if (k == 2 and s == 1) else 0)
            if lhs != rhs:
                ok = False
rep('T2c_pde', ok, '三变量 PDE 逐系数成立 (k<=24, m<=14, s<=9)；注意 t*F 项在 m=0 时为 0')

# ---------- 6. 定理 2：G_m(x,y) = W_m/P_m（带 y 的版本，直接用多项式乘法核对，而不是递推） ----------
def poly2_mul(A, B, K):
    """二元多项式 dict[(k,s)] 截断到 x^K。"""
    R = {}
    for (k1, s1), a in A.items():
        for (k2, s2), b in B.items():
            if k1 + k2 <= K:
                R[(k1 + k2, s1 + s2)] = R.get((k1 + k2, s1 + s2), 0) + a * b
    return {key: v for key, v in R.items() if v}


def bv(v):
    d = {(0, 0): 1, (1, 0): -1}
    if v:
        d[(3, 1)] = -v
    return d


ok = True
KP = 30
for m in range(0, 11):
    P = {(0, 0): 1}
    for v in range(0, m + 1):
        P = poly2_mul(P, bv(v), KP)
    W = {(0, 0): 1}
    for j in range(1, m + 1):
        Pj_full = {(0, 0): 1}
        for v in range(0, j):
            Pj_full = poly2_mul(Pj_full, bv(v), KP)
        for (k, s), c in Pj_full.items():
            if k + 2 <= KP:
                W[(k + 2, s + 1)] = W.get((k + 2, s + 1), 0) + j * c
    # 检查 P_m * G_m == W_m（截断到 x^KP），G_m 来自 DP 表
    G = {(k, s): Uks(k, m, s) for k in range(KP + 1) for s in range(KP + 1) if Uks(k, m, s)}
    PG = poly2_mul(P, G, KP)
    W = {key: v for key, v in W.items() if v}
    if PG != W:
        ok = False
    # x*W_m = 1 - P_m - x*sum_{j<m} P_j（带 y，精确多项式）
    lhs = {(k + 1, s): c for (k, s), c in W.items()}
    Pfull = {(0, 0): 1}
    for v in range(0, m + 1):
        Pfull = poly2_mul(Pfull, bv(v), 99)
    rhs = {(0, 0): 1}
    for key, c in Pfull.items():
        rhs[key] = rhs.get(key, 0) - c
    for j in range(0, m):
        Pj = {(0, 0): 1}
        for v in range(0, j + 1):
            Pj = poly2_mul(Pj, bv(v), 99)
        for (k, s), c in Pj.items():
            rhs[(k + 1, s)] = rhs.get((k + 1, s), 0) - c
    rhs = {key: v for key, v in rhs.items() if v}
    if m >= 0 and lhs != rhs:
        ok = False
rep('T2b_WP_with_y', ok, '带 y 的 P_m(x,y)G_m(x,y)=W_m(x,y)（G 取自 DP，截断 x^30）与 xW_m=1-P_m-x sum_{j<m}P_j（带 y 的精确多项式恒等式）m<=10')

# ---------- 7. 竖线模型引理 3.1 与定理 3（扩大暴力范围） ----------
ok = True
for L in range(0, 7):
    for s in range(0, 7):
        for j in range(0, 5):
            tot = 0
            for pos in itertools.combinations(range(L + s), s):
                ps = set(pos)
                w = 1
                for p in pos:
                    w *= j + sum(1 for q in range(p + 1, L + s) if q not in ps)
                tot += w
            if tot != hsym(s, j, j + L):
                ok = False
rep('L3.1_bars', ok, '竖线模型：sum prod(j+右侧竖线数) == h_s(j..j+L) (L<=6, s<=6, j<=4 暴力)')


# 定理 3：[x^n y^s] prod_{v=j}^m (1-x-v y x^3)^{-1}，用逐个因子的级数除法（不同于 c2b 的递推实现）
def prod_inv_coeffs(j, m, N, SM):
    G = [[0] * SM for _ in range(N + 1)]
    G[0][0] = 1
    for v in range(j, m + 1):
        H = [[0] * SM for _ in range(N + 1)]
        for n in range(N + 1):
            for s in range(SM):
                val = G[n][s]
                if n >= 1:
                    val += H[n - 1][s]
                if n >= 3 and s >= 1:
                    val += v * H[n - 3][s - 1]
                H[n][s] = val
        G = H
    return G


ok = True
for m in range(0, 15):
    for j in range(0, m + 1):
        G = prod_inv_coeffs(j, m, 36, 14)
        for n in range(37):
            for s in range(14):
                if G[n][s] != hsym(s, j, m) * C(n + m - j - 2 * s, n - 3 * s):
                    ok = False
rep('T3_coef', ok, '[x^n y^s] prod_{v=j}^m b_v^{-1} == H(m,s,j)C(n+m-j-2s,n-3s) (n<=36, s<=13, 0<=j<=m<=14)')


# 引理 3.2：r-Stirling 用集合划分直接枚举（不用限制增长串的「r_i=i」刻画）
def set_partitions(n):
    if n == 0:
        yield []
        return
    for p in set_partitions(n - 1):
        for i in range(len(p)):
            yield p[:i] + [p[i] + [n]] + p[i + 1:]
        yield p + [[n]]


ok = True
for n in range(1, 10):
    parts = list(set_partitions(n))
    for mm in range(1, n + 1):
        for r in range(1, mm + 1):
            cnt = 0
            for p in parts:
                if len(p) != mm:
                    continue
                blk = {}
                for bi, b in enumerate(p):
                    for e in b:
                        blk[e] = bi
                if len(set(blk[e] for e in range(1, r + 1))) == r:
                    cnt += 1
            if cnt != hsym(n - mm, r, mm):
                ok = False
ok = ok and all(hsym(s, 1, m) == ST[m + s][m] == hsym(s, 0, m) for m in range(0, 20) for s in range(0, 20))
rep('L3.2_rstirling', ok, 'h_s(j..m) == r-Stirling（直接枚举集合划分，n<=9）；h_s(0..m)=h_s(1..m)=S(m+s,m) (m,s<20)')


# ---------- 8. 推论 4.2：集合划分双射，完整的正反两向核对 ----------
def to_word(bl, m):
    w = []
    lev = m
    for b in bl:
        v = b[1]
        w += ['|'] * (lev - v)
        lev = v
        w.append('S' if b[0] == 'S' else ('T', b[2]))
    w += ['|'] * lev
    return w


def forward(h, m):
    bl = parse_valley(h)
    w = to_word(bl, m)
    spos = tuple(i for i, x in enumerate(w) if x == 'S')
    nonS = [x for x in w if x != 'S'][::-1]
    rgs = []
    nb = 0
    for x in nonS:
        if x == '|':
            nb += 1
            rgs.append(nb)
        else:
            if x[1] + 1 > nb:
                return None
            rgs.append(x[1] + 1)
    return spos, tuple(rgs)


def inverse(spos, rgs, k, m, s):
    """由 (S 位置, 限制增长串) 复原序列；不合格返回 None。"""
    total = k + m - 2 * s
    nonS_rev = []
    seen = set()
    for b in rgs:            # 从右往左的非 S 字母
        if b not in seen:
            seen.add(b)
            nonS_rev.append('|')
        else:
            nonS_rev.append(('T', b - 1))
    nonS = nonS_rev[::-1]
    w = []
    it = iter(nonS)
    sp = set(spos)
    for i in range(total):
        w.append('S' if i in sp else next(it))
    # 字 -> 序列：层次 = 右侧竖线数
    out = []
    for i, x in enumerate(w):
        if x == '|':
            continue
        lev = sum(1 for y in w[i + 1:] if y == '|')
        if x == 'S':
            out.append(lev)
        else:
            a = x[1]
            if not (a < lev):
                return None
            out += [a, lev, lev]
    return tuple(out)


def rgs_list(n, mx):
    res = []
    def rec(cur, top):
        if len(cur) == n:
            if top == mx:
                res.append(tuple(cur))
            return
        for b in range(1, min(top + 1, mx) + 1):
            rec(cur + [b], max(top, b))
    rec([], 0)
    return res


ok = True
for m in range(0, 4):
    for k in range(0, 10):
        legal = [h for h in itertools.product(range(m + 1), repeat=k)
                 if all(good(h[i], h[i + 1], h[i + 2]) for i in range(k - 2))]
        comp = [h for h in legal if not (k >= 2 and h[-2] < h[-1])]
        bys = {}
        for h in comp:
            s = sum(1 for i in range(k - 1) if h[i] < h[i + 1])
            im = forward(h, m)
            if im is None or inverse(im[0], im[1], k, m, s) != h:
                ok = False
            bys.setdefault(s, []).append(im)
        for s in range(0, k // 3 + 1):
            targets = [(sp, r) for sp in itertools.combinations(range(k + m - 2 * s), k - 3 * s)
                       for r in rgs_list(m + s, m)]
            got = bys.get(s, [])
            if len(set(got)) != len(got) or set(got) != set(targets):
                ok = False
            for (sp, r) in targets:
                h = inverse(sp, r, k, m, s)
                if h is None or len(h) != k or not all(good(h[i], h[i + 1], h[i + 2]) for i in range(k - 2)):
                    ok = False
                    continue
                if k >= 2 and h[-2] < h[-1]:
                    ok = False
                if sum(1 for i in range(k - 1) if h[i] < h[i + 1]) != s:
                    ok = False
rep('C4.2_setpartition_bijection', ok,
    '完整、s 上升序列 <-> (S 位置子集) x (RGS, max=m)：正向单射、像集==目标集，逆映射对每个目标给出合法完整 s 上升序列 (m<=3, k<=9)')

# ---------- 9. 命题 5.1 / 5.2 / 5.3 ----------
ok = True
for m in range(0, 4):
    for k in range(0, 8):
        L = [h for h in itertools.product(range(m + 1), repeat=k) if all(good(h[i], h[i + 1], h[i + 2]) for i in range(k - 2))]
        L1 = [g for g in itertools.product(range(m + 1), repeat=k + 1) if all(good(g[i], g[i + 1], g[i + 2]) for i in range(k - 1))]
        comp = [h for h in L if not (k >= 2 and h[-2] < h[-1])]
        asc = [h for h in L if k >= 2 and h[-2] < h[-1]]
        tgt0 = set(g for g in L1 if g[-1] == 0)
        tgtT = set(g for g in L1 if k + 1 >= 3 and g[-3] < g[-2] == g[-1])
        if set(h + (0,) for h in comp) != tgt0 or set(h + (h[-1],) for h in asc) != tgtT:
            ok = False
        # 末块分类：末块 S_0 / T / S_v(v>=1)
        cS0 = cT = cSv = 0
        for g in L1:
            if k + 1 >= 2 and g[-2] < g[-1]:
                continue      # 不完整
            bl = parse_valley(g)
            last = bl[-1]
            if last == ('S', 0):
                cS0 += 1
            elif last[0] == 'T':
                cT += 1
            else:
                cSv += 1
        if cS0 != len(comp) or cT != len(asc):
            ok = False
rep('P5.1_maps', ok, '补0: 完整长k <-> 长k+1末项0；补末项: 上升结尾长k <-> 长k+1末三项 a<v=v；且末块分别为 S_0 / T (m<=3, k<=7 暴力)')


def Aj(n, m, j):
    if n < 0:
        return 0
    return sum(hsym(s, j, m) * C(n + m - j - 2 * s, n - 3 * s) for s in range(0, n // 3 + 1))


ok = all(Aj(k + 1, m, 0) - sum(Aj(k, m, j) for j in range(1, m + 1)) == Utot[m][k] for m in range(MM + 1) for k in range(KK))
rep('P5.2_Aminus', ok, 'U_k(m)=A_m(k+1)-sum_j A^{(j)}_m(k) (k<=39, m<=14)')


def ci(i, N):
    return sum(C(N - 2 * p, p) * i ** p for p in range(0, N // 3 + 1))


def Theta(t, N, m):
    return Fraction(sum((-1) ** r * comb(t, r) * ci(m - r, N) for r in range(t + 1)), 1) / Fraction(__import__('math').factorial(t))


ok = True
for m in range(0, 13):
    for n in range(0, 36):
        for t in range(0, m + 1):
            if Theta(t, n + 3 * t, m) != Aj(n, m, m - t):
                ok = False
rep('P5.3_theta_termwise', ok, 'Theta_t(n+3t) == A^{(m-t)}_m(n) 逐项 (n<=35, m<=12)')

# 主 Agent 草稿 §2 的「逐项相同」只在内层成立：Theta 公式的项 != 定理 4 的项
diff_found = False
for m in range(1, 5):
    for k in range(2, 12):
        thm4_E_terms = [j * sum(hsym(s, j, m) * C(k - 2 + m - j - 2 * s, k - 2 - 3 * s) for s in range(0, k)) for j in range(1, m + 1)]
        theta_terms = [Aj(k, m, j) for j in range(1, m + 1)]
        if thm4_E_terms != theta_terms:
            diff_found = True
rep('draft_termwise_note', diff_found,
    '对照：Theta 公式的外层项 A^{(j)}_m(k) 与定理4第二项的 j*sum_s H C(k-2..) 不是同一组数（只在内层 Theta_t=A^{(m-t)} 对应）')

print('[time] %.1fs' % (time.time() - T0))
nb = sum(1 for _, o in RESULTS if not o)
print('SUMMARY r1 ok=%d bad=%d' % (len(RESULTS) - nb, nb))
