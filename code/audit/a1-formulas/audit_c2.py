# -*- coding: utf-8 -*-
"""审计 a1-formulas：报告 C-2 部分（T2.1–T2.9）与 ③ 推荐公式的显式公式/数值。"""
import time
from itertools import product
from fractions import Fraction
from common import *  # noqa

t0 = time.time()
K, M = 60, 20
T = own_U_table(K, M)

# ---------------- 自写：按上升数细化的定义 DP ----------------
def asc_table(K, M):
    """A[k][m] = dict s -> 合法序列数（上升数 s）；E[k][m][j] = 以上升结尾且末值为 j 的序列数。"""
    A = [[None] * (M + 1) for _ in range(K + 1)]
    E = [[None] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        n = m + 1
        A[0][m] = {0: 1}
        E[0][m] = [0] * n
        if K >= 1:
            A[1][m] = {0: n}
            E[1][m] = [0] * n
        # 状态 (a,b) -> dict s->cnt
        st = {}
        for a in range(n):
            for b in range(n):
                s = 1 if a < b else 0
                st[(a, b)] = {s: 1}
        def collect(st):
            tot = {}
            ej = [0] * n
            for (a, b), d in st.items():
                for s, v in d.items():
                    tot[s] = tot.get(s, 0) + v
                    if a < b:
                        ej[b] += v
            return tot, ej
        if K >= 2:
            A[2][m], E[2][m] = collect(st)
        for k in range(3, K + 1):
            new = {}
            for (a, b), d in st.items():
                for c in range(n):
                    if not good(a, b, c):
                        continue
                    inc = 1 if b < c else 0
                    tgt = new.setdefault((b, c), {})
                    for s, v in d.items():
                        tgt[s + inc] = tgt.get(s + inc, 0) + v
            st = new
            A[k][m], E[k][m] = collect(st)
    return A, E

KA, MA = 30, 10
A, E = asc_table(KA, MA)
report(all(sum(A[k][m].values()) == T[k][m] for k in range(KA + 1) for m in range(MA + 1)), 'base.asc-total', '上升数细化 DP 求和 == 定义 DP, k<=30, m<=10')

# ---------------- T2.1 块分解 ----------------
def n_parses(h, m):
    """把 h 写成「层弱降、只有最后一块可为 E」的块词的方式数（穷举所有分法）。"""
    k = len(h)
    from functools import lru_cache
    @lru_cache(maxsize=None)
    def f(i, lev):  # 从位置 i 开始，前一块层为 lev（上界）
        if i == k:
            return 1
        tot = 0
        v = h[i]
        if v <= lev:                                   # S_v
            tot += f(i + 1, v)
        if i + 2 < k + 0 and i + 2 <= k - 1:            # T_{v,a}=[a,v,v]
            a, v2, v3 = h[i], h[i + 1], h[i + 2]
            if v2 == v3 and a < v2 and v2 <= lev:
                tot += f(i + 3, v2)
        if i + 2 == k:                                  # E_{v,a}=[a,v] 末块
            a, v2 = h[i], h[i + 1]
            if a < v2 and v2 <= lev:
                tot += 1
        return tot
    return f(0, m)

def legal(h):
    return all(good(h[i], h[i + 1], h[i + 2]) for i in range(len(h) - 2))

ok = True
cnt = 0
stat_ok = True
for m in range(0, 4):
    for k in range(1, 9):
        for h in product(range(m + 1), repeat=k):
            cnt += 1
            np_ = n_parses(h, m)
            if np_ != (1 if legal(h) else 0):
                ok = False
report(ok, 'T2.1.bijection', '块分解方式数 == [合法]，全部 (m+1)^k 序列，1<=k<=8, m<=3（共 %d 个）' % cnt)
total = sum((m + 1) ** k for m in range(0, 5) for k in range(1, 11))
report(total == 13695758, 'T2.1.count', 'sum_{k=1..10,m=0..4}(m+1)^k = %d（报告 13,695,758）' % total)
# 统计：上升数 = #T + #E；以上升结尾 ⇔ 末块为 E（用贪心解析）
def greedy(h):
    blocks = []
    i = 0
    k = len(h)
    while i < k:
        if i + 1 < k and h[i] < h[i + 1]:
            if i + 2 < k:
                blocks.append('T'); i += 3
            else:
                blocks.append('E'); i += 2
        else:
            blocks.append('S'); i += 1
    return blocks
for m in range(0, 4):
    for k in range(1, 9):
        for h in product(range(m + 1), repeat=k):
            if not legal(h):
                continue
            bl = greedy(h)
            asc = sum(1 for i in range(k - 1) if h[i] < h[i + 1])
            if asc != bl.count('T') + bl.count('E'):
                stat_ok = False
            if (k >= 2 and h[-2] < h[-1]) != (bl[-1] == 'E'):
                stat_ok = False
report(stat_ok, 'T2.1.stats', '上升数=#T+#E；以上升结尾 ⇔ 末块为 E（k<=8, m<=3 全部合法序列）')

# ---------------- T2.2 含上升数的母函数 ----------------
# G_m[k][s] 递推：G_m=(G_{m-1}+m y x^2)/(1-x-m y x^3)
def Gxy(MM, KK):
    prev = [[1] + [0] * (KK + 2)] + [[0] * (KK + 3) for _ in range(KK)]   # G_{-1}=1：prev[k][s]
    out = []
    for m in range(0, MM + 1):
        g = [[0] * (KK + 3) for _ in range(KK + 1)]
        for k in range(0, KK + 1):
            for s in range(0, KK + 2):
                v = prev[k][s]
                if k == 2 and s == 1:
                    v += m
                if k >= 1:
                    v += g[k - 1][s]
                if k >= 3 and s >= 1:
                    v += m * g[k - 3][s - 1]
                g[k][s] = v
        out.append(g)
        prev = g
    return out
GX = Gxy(MA, KA)
ok = all(GX[m][k][s] == A[k][m].get(s, 0) for m in range(MA + 1) for k in range(KA + 1) for s in range(KA + 2))
report(ok, 'T2.2.gf-xy', 'G_m(x,y)=(G_{m-1}+m y x^2)/(1-x-m y x^3) 与按上升数细化 DP 一致, k<=30, m<=10')
# W_m/P_m 与 1/P_m + y x^2 sum_j j/prod_{v=j}^m b_v（二元：用 y 的多项式 × x 的截断级数）
def bxy(v):  # 1 - x - v y x^3 作为 {(i_x,i_y):c}
    d = {(0, 0): 1, (1, 0): -1}
    if v:
        d[(3, 1)] = -v
    return d
def bmul(p, q, KX):
    r = {}
    for (a, b), c in p.items():
        for (e, f), d in q.items():
            if a + e <= KX:
                r[(a + e, b + f)] = r.get((a + e, b + f), 0) + c * d
    return {k: v for k, v in r.items() if v}
def binv(p, KX):
    """1/p，p 常数项 1，截断 x^KX；返回 dict。"""
    # 逐 x 次数求：inv_k = -sum_{i>=1} p_i inv_{k-i}，其中 p_i, inv 是 y 的多项式
    pk = {}
    for (a, b), c in p.items():
        pk.setdefault(a, {})[b] = c
    inv = [dict() for _ in range(KX + 1)]
    inv[0] = {0: 1}
    for k in range(1, KX + 1):
        acc = {}
        for i in range(1, k + 1):
            if i not in pk:
                continue
            for b, c in pk[i].items():
                for bb, cc in inv[k - i].items():
                    acc[b + bb] = acc.get(b + bb, 0) - c * cc
        inv[k] = {b: v for b, v in acc.items() if v}
    return {(k, b): v for k in range(KX + 1) for b, v in inv[k].items()}
KX = 24
ok = True
for m in range(0, 9):
    Pm = {(0, 0): 1}
    for v in range(0, m + 1):
        Pm = bmul(Pm, bxy(v), KX)
    Wm = {(0, 0): 1}
    for j in range(1, m + 1):
        Pj = {(0, 0): 1}
        for v in range(0, j):
            Pj = bmul(Pj, bxy(v), KX)
        for (a, b), c in Pj.items():
            if a + 2 <= KX:
                Wm[(a + 2, b + 1)] = Wm.get((a + 2, b + 1), 0) + j * c
    lhs = bmul(Wm, binv(Pm, KX), KX)
    alt = binv(Pm, KX)
    for j in range(1, m + 1):
        Q = {(0, 0): 1}
        for v in range(j, m + 1):
            Q = bmul(Q, bxy(v), KX)
        Qi = binv(Q, KX)
        for (a, b), c in Qi.items():
            if a + 2 <= KX:
                alt[(a + 2, b + 1)] = alt.get((a + 2, b + 1), 0) + j * c
    for k in range(0, KX + 1):
        for s in range(0, KX + 1):
            want = A[k][m].get(s, 0)
            if lhs.get((k, s), 0) != want or alt.get((k, s), 0) != want:
                ok = False
report(ok, 'T2.2.WP-xy', 'G_m(x,y)=W_m/P_m=1/P_m+y x^2 sum_j j/prod_{v=j}^m b_v（b_v=1-x-v y x^3），k<=24, m<=8')
# s-细化引理 1：两种 U_{-1} 约定
def Ums(k, m, s, conv):
    if s < 0:
        return 0
    if k == 0:
        return 1 if s == 0 else 0
    if k == -1:
        return (1 if s == 0 else 0) if conv == 'one' else 0
    if k == -2:
        return 0
    if m == -1:
        return 0
    return A[k][m].get(s, 0)
res = {}
for conv in ('zero', 'one'):
    ok = True
    for k in range(1, KA + 1):
        for m in range(0, MA + 1):
            for s in range(0, KA + 1):
                rhs = Ums(k, m - 1, s, conv) + Ums(k - 1, m, s, conv) + m * Ums(k - 3, m, s - 1, conv) + (m if (k == 2 and s == 1) else 0)
                if Ums(k, m, s, conv) != rhs:
                    ok = False
    res[conv] = ok
report(res['zero'] and not res['one'], 'T2.2.lemma1-s',
       's-细化引理 1 U_k(m,s)=U_k(m-1,s)+U_{k-1}(m,s)+m U_{k-3}(m,s-1)+m[k=2][s=1]：取 U_{-1}(·,s)=0 时成立=%s；若沿用 T1.1 的 U_{-1}≡1（即 [s=0]）则成立=%s' % (res['zero'], res['one']))
# 三变量 PDE 逐系数
ok = True
for k in range(0, KA + 1):
    for m in range(0, MA + 1):
        for s in range(0, KA + 1):
            def g(kk, mm, ss):
                if kk < 0 or mm < 0 or ss < 0:
                    return 0
                return A[kk][mm].get(ss, 0)
            lhs = g(k, m, s) - g(k - 1, m, s) - g(k, m - 1, s) - m * g(k - 3, m, s - 1)
            rhs = (1 if (k == 0 and m == 0 and s == 0) else 0) + (m if (k == 2 and s == 1) else 0)
            if lhs != rhs:
                ok = False
report(ok, 'T2.2.pde-xty', '(1-x-t)F-y x^3 t F_t=1+y x^2 t/(1-t)^2 逐系数, k<=30, m<=10, 全部 s')

# ---------------- T2.3 系数提取与 r-Stirling ----------------
ok = True
for m in range(0, 8):
    for j in range(0, m + 1):
        Q = {(0, 0): 1}
        for v in range(j, m + 1):
            Q = bmul(Q, bxy(v), 24)
        Qi = binv(Q, 24)
        for n in range(0, 25):
            for s in range(0, 10):
                want = hcomp(s, j, m) * C(n + m - j - 2 * s, n - 3 * s)
                if Qi.get((n, s), 0) != want:
                    ok = False
report(ok, 'T2.3.1-coef', '[x^n y^s]prod_{v=j}^m(1-x-v y x^3)^{-1}=H(m,s,j)C(n+m-j-2s,n-3s), n<=24, 0<=j<=m<=7')
# r-Stirling 暴力：[n] 分成 m 块且 1..j 两两异块
def set_partitions(n):
    def rec(i, blocks):
        if i == n:
            yield blocks
            return
        for b in range(len(blocks)):
            blocks[b].append(i)
            yield from rec(i + 1, blocks)
            blocks[b].pop()
        blocks.append([i])
        yield from rec(i + 1, blocks)
        blocks.pop()
    yield from rec(0, [])
ok = True
from collections import Counter
for n in range(1, 10):
    parts = [[list(b) for b in p] for p in set_partitions(n)]
    for mm in range(1, n + 1):
        s = n - mm
        for j in range(0, mm + 1):
            cntp = 0
            for p in parts:
                if len(p) != mm:
                    continue
                blk = {}
                for bi, b in enumerate(p):
                    for e in b:
                        blk[e] = bi
                if len(set(blk[e] for e in range(j))) == j:
                    cntp += 1
            want = hcomp(s, j, mm) if j >= 1 else hcomp(s, 0, mm)
            if cntp != want:
                ok = False
report(ok, 'T2.3.2-rstirling', 'H(m,s,j)=r-Stirling {m+s ⧵ m}_j（暴力集合划分，m+s<=9，含 j=0,1 时 =S(m+s,m)）')
report(all(hcomp(s, 0, m) == hcomp(s, 1, m) == stirling2(m + s, m) for m in range(0, 15) for s in range(0, 15)), 'T2.3.2-H01', 'H(m,s,0)=H(m,s,1)=S(m+s,m), m,s<15')
ok = True
for m in range(0, 13):
    for t in range(0, m + 1):
        for p in range(t, 31):
            lhs = Fraction(sum((-1) ** r * comb(t, r) * (m - r) ** p for r in range(t + 1)), factorial(t))
            if lhs != hcomp(p - t, m - t, m):
                ok = False
report(ok, 'T2.3.3-nabla', '(1/t!)∇^t i^p|_{i=m}=h_{p-t}(m-t..m)，t<=m<=12, p<=30')
ok = True
for m in range(0, 9):
    for t in range(0, m + 1):
        lhs = [0] * 30
        for r in range(t + 1):
            for n in range(30):
                lhs[n] += (-1) ** r * comb(t, r) * (m - r) ** n
        den = [1]
        for r in range(t + 1):
            den = pmul(den, [1, -(m - r)])
        rhs = smul(pshift([factorial(t)], t), sinv(den, 30), 30)
        if any(lhs[n] != rhs[n] for n in range(30)):
            ok = False
report(ok, 'T2.3.3-series', 'sum_r(-1)^rC(t,r)/(1-(m-r)z)=t! z^t/prod_{r=0}^t(1-(m-r)z) 到 z^29, t<=m<=8')

# ---------------- T2.4 / ③ 推荐公式 ----------------
def H_rec_table(m):
    """按 ③ 的递推 H(m,s,j)=H(m,s,j+1)+j H(m,s-1,j)，H(m,0,j)=1，H(m,s,m+1)=[s=0]。"""
    Smax = 25
    Ht = {}
    for s in range(0, Smax + 1):
        Ht[(s, m + 1)] = 1 if s == 0 else 0
    for j in range(m, -1, -1):
        Ht[(0, j)] = 1
        for s in range(1, Smax + 1):
            Ht[(s, j)] = Ht[(s, j + 1)] + j * Ht[(s - 1, j)]
    return Ht
ok_rec = True
ok_expl = True
for m in range(0, 16):
    Ht = H_rec_table(m)
    for j in range(0, m + 1):
        for s in range(0, 20):
            if Ht[(s, j)] != hcomp(s, j, m):
                ok_rec = False
            n = m - j
            ex = Fraction(sum((-1) ** (n - i) * comb(n, i) * (j + i) ** (s + n) for i in range(n + 1)), factorial(n))
            if ex != hcomp(s, j, m):
                ok_expl = False
report(ok_rec, '③.H-rec', 'H 递推 H(m,s,j)=H(m,s,j+1)+jH(m,s-1,j)，H(m,0,j)=1，H(m,s,m+1)=[s=0]，m<=15,s<20')
report(ok_expl, '③.H-explicit', 'H(m,s,j)=(1/(m-j)!)sum_i(-1)^{m-j-i}C(m-j,i)(j+i)^{s+m-j}（0^0=1），0<=j<=m<=15, s<20')
def U_rec_formula(k, m):
    a = sum(stirling2(m + s, m) * C(k + m - 2 * s, k - 3 * s) for s in range(0, k // 3 + 1))
    b = 0
    if k >= 2:
        for j in range(1, m + 1):
            b += j * sum(hcomp(s, j, m) * C(k - 2 + m - j - 2 * s, k - 2 - 3 * s) for s in range(0, (k - 2) // 3 + 1))
    return a, b
ok = all(sum(U_rec_formula(k, m)) == T[k][m] for k in range(0, K + 1) for m in range(0, M + 1))
report(ok, 'T2.4.U', '推荐公式（③ 的显式求和上界 floor(k/3)、floor((k-2)/3)）== 定义 DP, 0<=k<=60, 0<=m<=20')
# 第一项 = 不以上升结尾；第二项按 j = 以 E_j 结尾（末值 j 且末步上升）
ok = True
for k in range(0, KA + 1):
    for m in range(0, MA + 1):
        a, b = U_rec_formula(k, m)
        ends_asc = sum(E[k][m])
        if a != T[k][m] - ends_asc or b != ends_asc:
            ok = False
        if k >= 2:
            for j in range(1, m + 1):
                bj = j * sum(hcomp(s, j, m) * C(k - 2 + m - j - 2 * s, k - 2 - 3 * s) for s in range(0, (k - 2) // 3 + 1))
                if bj != E[k][m][j]:
                    ok = False
report(ok, 'T2.4.split', '第一项=不以上升结尾的序列数；第二项第 j 项=以上升结尾且末值 j 的序列数, k<=30, m<=10')
ok = True
for k in range(0, KA + 1):
    for m in range(0, MA + 1):
        for s in range(0, KA + 1):
            v = stirling2(m + s, m) * C(k + m - 2 * s, k - 3 * s)
            v += sum(j * hcomp(s - 1, j, m) * C(k + m - j - 2 * s, k + 1 - 3 * s) for j in range(1, m + 1))
            if v != A[k][m].get(s, 0):
                ok = False
report(ok, 'T2.4.U-s', 'U_k(m,s)=S(m+s,m)C(k+m-2s,k-3s)+sum_j j H(m,s-1,j)C(k+m-j-2s,k+1-3s) 与细化 DP 一致, k<=30, m<=10, 全部 s')

# ---------------- T2.5 ----------------
ok = True
for k in range(0, K + 1):
    for m in range(0, M + 1):
        a = sum(stirling2(m + s, m) * C(k + 1 + m - 2 * s, m + s) for s in range(0, (k + 1) // 3 + 1))
        b = sum(hcomp(s, j, m) * C(k + m - j - 2 * s, m - j + s) for j in range(1, m + 1) for s in range(0, k // 3 + 1))
        if a - b != T[k][m]:
            ok = False
report(ok, 'T2.5.1-F3', 'F3 型 U_k(m)=sum_s S(m+s,m)C(k+1+m-2s,m+s)-sum_j sum_s H(m,s,j)C(k+m-j-2s,m-j+s), k<=60, m<=20')
# 望远镜恒等式（级数核对）
ok = True
for m in range(1, 9):
    for j in range(0, m + 1):
        Qj = [1]
        for v in range(j, m + 1):
            Qj = pmul(Qj, b_poly(v))
        Qj1 = [1]
        for v in range(j + 1, m + 1):
            Qj1 = pmul(Qj1, b_poly(v))
        sj = sinv(Qj, 40)
        sj1 = sinv(Qj1, 40)
        lhs = [0, 0, 0] + [j * c for c in sj[:37]]
        rhs = [sj[n] - (sj[n - 1] if n else 0) - sj1[n] for n in range(40)]
        if lhs != rhs:
            ok = False
report(ok, 'T2.5.1-telescope', 'j x^3 Q_j=(1-x)Q_j-Q_{j+1}（Q_j=prod_{v=j}^m b_v^{-1}），级数到 x^39, m<=8')
# (2) Θ_t 内层
cache = {}
def cs(i):
    if i not in cache:
        cache[i] = c_seq(i, 500)
    return cache[i]
def Theta(t, n, m):
    s = sum((-1) ** r * comb(t, r) * (cs(m - r)[n] if n >= 0 else 0) for r in range(t + 1))
    assert s % factorial(t) == 0
    return s // factorial(t)
ok = all(Theta(t, n + 3 * t, m) == sum(hcomp(s, m - t, m) * C(n + t - 2 * s, n - 3 * s) for s in range(0, n // 3 + 1))
         for m in range(0, 13) for t in range(0, m + 1) for n in range(0, 31))
report(ok, 'T2.5.2-theta-H', 'Θ_t(n+3t)=sum_s H(m,s,m-t)C(n+t-2s,n-3s), m<=12, n<=30')
th = (Theta(1, 3 + 1 + 3, 1), -Theta(0, 3, 1))
hh = (sum(stirling2(1 + s, 1) * C(3 + 1 - 2 * s, 3 - 3 * s) for s in range(0, 2)), 1 * sinv(b_poly(1), 5)[1])
report(th == (8, -2) and hh == (5, 1) and sum(th) == sum(hh) == T[3][1], 'T2.5.2-cex', 'm=1,k=3：Θ 两项 %s，H 两项 %s，和 %d' % (th, hh, T[3][1]))
# (3) c_i 偏分式型
def cval(i, n):
    return cs(i)[n] if n >= 0 else 0
ok = True
for k in range(0, K + 1):
    for m in range(0, M + 1):
        tot = 0
        for i in range(0, m + 1):
            inner = cval(i, k + 3 * m) + sum(j * falling(i, j) * cval(i, k + 3 * m - 3 * j - 2) for j in range(1, i + 1))
            tot += (-1) ** (m - i) * comb(m, i) * inner
        if tot != factorial(m) * T[k][m]:
            ok = False
report(ok, 'T2.5.3-F4', 'm!U_k(m)=sum_i(-1)^{m-i}C(m,i)[c_i(k+3m)+sum_{j<=i} j i^(j下降) c_i(k+3m-3j-2)]（c_i(n<0)=0），k<=60, m<=20')
ok = True
for m in range(0, 13):
    Wm = W_poly(m)
    for i in range(0, m + 1):
        rhs = [1]
        for j in range(1, i + 1):
            rhs = padd(rhs, pshift([j * falling(i, j)], 3 * j + 2))
        _, r = pdivmod(psub(Wm, rhs), b_poly(i))
        if r:
            ok = False
report(ok, 'T2.5.3-Wmod', 'W_m ≡ 1+sum_{j<=i} j i^(j下降) x^{3j+2} (mod b_i)，0<=i<=m<=12')
report(all(T[k][1] == cval(1, k + 3) + cval(1, k - 2) - 1 for k in range(0, K + 1)), 'T2.5.3-Rk', 'R_k=c_1(k+3)+c_1(k-2)-1, 0<=k<=60')

# ---------------- T2.6 证明中的代数事实（Q(ξ) 精确，ξ^3+ξ-1=0） ----------------
class Qxi:
    """Q[ξ]/(ξ^3+ξ-1) 元素 a0+a1ξ+a2ξ^2。"""
    def __init__(self, a):
        a = [Fraction(v) for v in a] + [Fraction(0)] * 3
        self.a = a[:3]
    def __add__(s, o):
        o = o if isinstance(o, Qxi) else Qxi([o])
        return Qxi([s.a[i] + o.a[i] for i in range(3)])
    __radd__ = __add__
    def __sub__(s, o):
        o = o if isinstance(o, Qxi) else Qxi([o])
        return Qxi([s.a[i] - o.a[i] for i in range(3)])
    def __rsub__(s, o):
        return Qxi([o]) - s
    def __mul__(s, o):
        o = o if isinstance(o, Qxi) else Qxi([o])
        r = [Fraction(0)] * 5
        for i in range(3):
            for j in range(3):
                r[i + j] += s.a[i] * o.a[j]
        # ξ^3 = 1 - ξ, ξ^4 = ξ - ξ^2
        for d in (4, 3):
            c = r[d]
            r[d] = 0
            r[d - 3] += c
            r[d - 2] -= c
        return Qxi(r[:3])
    __rmul__ = __mul__
    def mat(s):
        cols = []
        for b in (Qxi([1]), Qxi([0, 1]), Qxi([0, 0, 1])):
            cols.append((s * b).a)
        return [[cols[j][i] for j in range(3)] for i in range(3)]
    def norm(s):
        m = s.mat()
        return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
                + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))
    def inv(s):
        m = s.mat()
        # 解 m * v = e0
        import copy
        aug = [row[:] + [Fraction(1 if i == 0 else 0)] for i, row in enumerate(m)]
        for c in range(3):
            p = next(r for r in range(c, 3) if aug[r][c] != 0)
            aug[c], aug[p] = aug[p], aug[c]
            pv = aug[c][c]
            aug[c] = [v / pv for v in aug[c]]
            for r in range(3):
                if r != c and aug[r][c] != 0:
                    f = aug[r][c]
                    aug[r] = [aug[r][i] - f * aug[c][i] for i in range(4)]
        return Qxi([aug[i][3] for i in range(3)])
    def __truediv__(s, o):
        o = o if isinstance(o, Qxi) else Qxi([o])
        return s * o.inv()
    def __eq__(s, o):
        o = o if isinstance(o, Qxi) else Qxi([o])
        return s.a == o.a
    def __pow__(s, e):
        if e < 0:
            return s.inv() ** (-e)
        r = Qxi([1])
        for _ in range(e):
            r = r * s
        return r

xi = Qxi([0, 1])
def pev(p, z):
    r = Qxi([0])
    for c in reversed(p):
        r = r * z + c
    return r
ok = True
for m in range(1, 13):
    if not (pev(W_poly(m), xi) == xi * (1 + xi) == 1 + xi ** 5):
        ok = False
for w in range(0, 20):
    if not pev(b_poly(w), xi) == (1 - w) * xi ** 3:
        ok = False
report(ok and xi.norm() == 1 and (1 + xi).norm() == 3, 'T2.6.facts', 'Q(ξ)：W_m(ξ)=ξ(1+ξ)=1+ξ^5 (m<=12)、b_w(ξ)=(1-w)ξ^3、N(ξ)=%s、N(1+ξ)=%s' % (xi.norm(), (1 + xi).norm()))
ok = True
for m in range(1, 13):
    Pm = P_poly(m)
    res_ = pev(W_poly(m), xi) / pev(pderiv(Pm), xi)
    uprime = xi ** 2 * (3 - 2 * xi) / ((1 - xi) ** 2)
    want = Fraction((-1) ** m, factorial(m - 1)) * (1 + xi) * xi ** (-3 * m - 2)
    if not (res_ * uprime == want):
        ok = False
report(ok, 'T2.6.residue', 'ρ_i u\'(ξ_i)=(-1)^m(1+ξ)ξ^{-3m-2}/(m-1)!（留数 W_m/P_m\'，Q(ξ) 精确，1<=m<=12）')

# ---------------- T2.7 ----------------
ok = True
for m in range(0, 13):
    Pm = P_poly(m)
    sumP = []
    for j in range(m):
        sumP = padd(sumP, P_poly(j))
    inv = sinv(Pm, 42)
    lhs = [inv[n + 1] for n in range(40)]          # (1/P_m - 1)/x
    t2 = smul(sumP, inv, 41)
    g = [lhs[n] - t2[n] for n in range(40)]
    if any(g[n] != T[n][m] for n in range(40)):
        ok = False
report(ok, 'T2.7.G', 'G_m=(1/P_m-1)/x-(sum_{j<m}P_j)/P_m（到 x^39, m<=12）')

# ---------------- T2.8 ----------------
NT = N_table_from_U(T, 21)
ok = all(NT[k][q] == sum((-1) ** (q - i) * comb(q, i) * T[k][i - 1] for i in range(1, q + 1)) for k in range(1, 21) for q in range(0, 21))
k0 = [sum((-1) ** (q - i) * comb(q, i) * 1 for i in range(1, q + 1)) for q in range(0, 5)]
report(ok, 'T2.8.1-inv', 'N(k,q)=sum_{i=1}^q(-1)^{q-i}C(q,i)U_k(i-1) 对 k>=1 成立 (k<=20)；但 k=0 时该式给 %s（真值 1,0,0,0,0）' % k0)
# N^c：DFS
def Nc_dfs(k):
    res = {}
    if k == 0:
        return {0: 1}
    seq = []
    def rec():
        if len(seq) == k:
            q = len(set(seq))
            if max(seq) == q - 1 and not (k >= 2 and seq[-2] < seq[-1]):
                res[q] = res.get(q, 0) + 1
            return
        for v in range(k):
            if len(seq) >= 2 and not good(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec()
            seq.pop()
    rec()
    return res
def S_conv(n, k, conv):
    if n == -1 and k == -1:
        return 1 if conv == 'S(-1,-1)=1' else 0
    if n < 0 or k < 0:
        return 0
    return stirling2(n, k)
def Rps(p, s, conv):
    return sum((-1) ** (p - i) * comb(p, i) * S_conv(i - 1 + s, i - 1, conv) for i in range(0, p + 1))
def Nc_formula(k, q, conv):
    return sum(comb(q, p) * Rps(p, s, conv) * C(k - 2 * s + p - 1, s + q - 1) for s in range(0, k + 1) for p in range(0, 2 * s + 1))
out = {}
for conv in ('S(-1,-1)=1', 'S(-1,-1)=0'):
    ok = True
    for k in range(1, 10):
        d = Nc_dfs(k)
        for q in range(1, k + 1):
            if Nc_formula(k, q, conv) != d.get(q, 0):
                ok = False
    out[conv] = ok
report(out['S(-1,-1)=1'], 'T2.8.2-Nc', 'N^c(k,q)=sum_s sum_p C(q,p)R(p,s)C(k-2s+p-1,s+q-1) 与 DFS 一致 (1<=q<=k<=9)，需 R(0,0)=1 即 S(-1,-1)=1；若按 S(n,k)=0 (k<0) 则成立=%s' % out['S(-1,-1)=0'])
report(Nc_formula(0, 0, 'S(-1,-1)=1') == 0, 'T2.8.2-Nc00', '(k,q)=(0,0) 时公式给 0（真值 1），与报告注一致')
from math import prod
report(all(Rps(2 * s, s, 'S(-1,-1)=1') == prod(range(1, 2 * s, 2)) for s in range(1, 12)), 'T2.8.2-R2s', 'R(2s,s)=(2s-1)!!, 1<=s<=11')

# ---------------- T2.9 / ③ 表中数值 ----------------
UL = lemma1_table(100, 100)
dig = len(str(UL[100][100]))
mx = 0
mxinfo = None
m = 100
k = 100
for t in range(0, m + 1):
    n = k + 1 + 3 * m if t == m else k + 3 * t
    for r in range(0, t + 1):
        v = comb(t, r) * cs(m - r)[n]
        if v > mx:
            mx = v
            mxinfo = (t, r)
report(dig == 99, 'T2.9.digits-U', 'U_100(100) 位数=%d（报告 99）' % dig)
report(len(str(mx)) == 289, 'T2.9.digits-theta', 'Θ 型 k=m=100 最大中间单项 C(t,r)c_{m-r}(n) 位数=%d，(t,r)=%s（报告 289）' % (len(str(mx)), mxinfo))
# 项数估计
kk, mm = 100, 100
nH = (kk // 3 + 1) + mm * ((kk - 2) // 3 + 1)
nTheta_c = sum(t + 1 for t in range(mm + 1))
nTheta_terms = sum((t + 1) * (((kk + 1 + 3 * mm) if t == mm else (kk + 3 * t)) // 3 + 1) for t in range(mm + 1))
print('INFO counts k=m=100: H 项数=%d (≈(m+1)k/3=%.0f); Θ c 值个数=%d (≈m^2/2=%d); c 总项数=%d (≈m^2k/6=%.0f)' % (nH, (mm + 1) * kk / 3, nTheta_c, mm * mm // 2, nTheta_terms, mm * mm * kk / 6))
kk, mm = 1500, 30
nTheta_terms2 = sum((t + 1) * (((kk + 1 + 3 * mm) if t == mm else (kk + 3 * t)) // 3 + 1) for t in range(mm + 1))
print('INFO counts k=1500,m=30: c 总项数=%d (≈m^2k/6=%.0f)' % (nTheta_terms2, mm * mm * kk / 6))

summary('audit_c2')
print('elapsed %.1fs' % (time.time() - t0))
