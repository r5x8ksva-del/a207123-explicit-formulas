# -*- coding: utf-8 -*-
"""r-c2a 复核脚本 2：r-Stirling 识别与各恒等式的独立核对（不导入 core / polylib / c2a_lib）。
  - Broder r-Stirling 的集合分拆暴力定义（n<=10）vs h_{n-k}(r..k)；
  - 定理 2：(1/t!) nabla^t i^p |_{i=m} = h_{p-t}(m-t..m)（更大范围 + 有理系数检查整除）；
  - 「带权 j 的塌缩」 sum_{j=1}^m j h_{s-1}(j..m) = S(m+s,m)（s>=1）以及 s=0 的边界；
  - Broder 跨层恒等式；
  - 定理 3(i) 的多项式恒等式（m<=25），望远镜恒等式，F4 的模 b_i 同余与商次数；
  - 定理 1 块分解 + 双射 phi 的暴力核对（m<=4, k<=8，自写分块器，按「最大值首现」递归切块，与 c2a 的贪心切法不同）；
  - 反例 m=1,k=3 的项。
"""
import time
from math import comb, factorial
from itertools import product
from fractions import Fraction as Fr

T0 = time.time()
RES = []


def rep(tag, ok, msg):
    RES.append(bool(ok))
    print(('PASS ' if ok else 'FAIL ') + tag + ' ' + msg, flush=True)


def C(a, b):
    if b < 0 or a < 0 or b > a:
        return 0
    return comb(a, b)


def hfun(s, lo, hi):
    if s < 0:
        return 0
    row = [1] + [0] * s
    for v in range(lo, hi + 1):
        for t in range(1, s + 1):
            row[t] += v * row[t - 1]
    return row[s]


def stirling2(N):
    S = [[0] * (N + 1) for _ in range(N + 1)]
    S[0][0] = 1
    for n in range(1, N + 1):
        for k in range(1, n + 1):
            S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
    return S


S = stirling2(140)

# ---------------------------------------------------------------- r-Stirling 暴力
def set_partitions(n):
    """生成 {0..n-1} 的全部集合分拆（块的列表）。"""
    if n == 0:
        yield []
        return
    for p in set_partitions(n - 1):
        for i in range(len(p)):
            yield p[:i] + [p[i] + [n - 1]] + p[i + 1:]
        yield p + [[n - 1]]


t0 = time.time()
cnt = {}
for n in range(0, 11):
    for p in set_partitions(n):
        k = len(p)
        blk = {}
        for bi, b in enumerate(p):
            for e in b:
                blk[e] = bi
        for r in range(0, n + 1):
            if len(set(blk[e] for e in range(r))) == r:
                cnt[(n, k, r)] = cnt.get((n, k, r), 0) + 1
ok = True
for n in range(0, 11):
    for r in range(0, n + 1):
        for k in range(0, n + 1):
            want = hfun(n - k, r, k) if r <= k else 0
            ok = ok and cnt.get((n, k, r), 0) == want
rep('rS_brute', ok, 'Broder r-Stirling (set partitions of [n], 1..r in distinct blocks, own generator) == h_{n-k}(r..k) (0 if k<r), 0<=r,k<=n<=10 (%.1fs)' % (time.time() - t0))

# ---------------------------------------------------------------- 定理 2
ok = True
for m in range(0, 31):
    for t in range(0, m + 1):
        for p in range(0, 61):
            s = Fr(sum((-1) ** r * comb(t, r) * (m - r) ** p for r in range(t + 1)), factorial(t))
            want = hfun(p - t, m - t, m) if p >= t else 0
            ok = ok and s == want
rep('nabla_h', ok, '(1/t!) sum_r (-1)^r C(t,r) (m-r)^p == h_{p-t}(m-t..m) (0 if p<t), as rationals, 0<=t<=m<=30, p<=60 (0^0=1)')
# 与 r-Stirling 暴力表的交叉（小范围）
ok = True
for m in range(0, 8):
    for t in range(0, m + 1):
        for p in range(0, 11 - m + t):
            n = p + m - t
            if n > 10:
                continue
            s = sum((-1) ** r * comb(t, r) * (m - r) ** p for r in range(t + 1)) // factorial(t)
            ok = ok and s == cnt.get((n, m, m - t), 0)
rep('nabla_rS_brute', ok, '(1/t!) nabla^t i^p |_{i=m} == brute-force r-Stirling {p+m-t \\ m}_{m-t} for p+m-t<=10')

# ---------------------------------------------------------------- 带权 j 的塌缩
ok_pos = all(sum(j * hfun(s - 1, j, m) for j in range(1, m + 1)) == S[m + s][m]
             for m in range(0, 31) for s in range(1, 41))
ok_s0 = all(sum(j * hfun(-1, j, m) for j in range(1, m + 1)) == 0 for m in range(0, 31))
s0_literal = [(m, S[m][m]) for m in range(0, 3)]
rep('weighted_collapse', ok_pos and ok_s0, 'sum_{j=1}^m j h_{s-1}(j..m) == S(m+s,m) for 1<=s<=40, 0<=m<=30; at s=0 LHS=0 while S(m,m)=1 (identity needs s>=1, i.e. RHS is S(m+s,m)-[s=0])')

# ---------------------------------------------------------------- 跨层恒等式
ok = all(sum(C(m - j + s, m - j + t) * S[m - j + t][m - j] * j ** (s - t) for t in range(s + 1)) == hfun(s, j, m)
         for m in range(0, 26) for j in range(0, m + 1) for s in range(0, 31))
rep('cross_identity', ok, 'h_s(j..m) == sum_t C(m-j+s,m-j+t) S(m-j+t,m-j) j^(s-t), 0<=j<=m<=25, s<=30')


# ---------------------------------------------------------------- 多项式工具（整数系数）
def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def padd(p, q, c=1):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + c * (q[i] if i < len(q) else 0) for i in range(n)]


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def b(v):
    return [1, -1, 0, -v]


def prod_b(lo, hi, skip=None):
    p = [1]
    for v in range(lo, hi + 1):
        if v != skip:
            p = pmul(p, b(v))
    return p


def pdivmod(p, q):
    """有理系数带余除法。"""
    p = [Fr(a) for a in trim(p)]
    q = [Fr(a) for a in trim(q)]
    out = [Fr(0)] * max(len(p) - len(q) + 1, 0)
    while len(p) >= len(q) and p:
        c = p[-1] / q[-1]
        d = len(p) - len(q)
        out[d] = c
        for i, a in enumerate(q):
            p[i + d] -= c * a
        p = trim(p)
    return trim(out), p


ok = True
for m in range(0, 26):
    for t in range(0, m + 1):
        lhs = [0]
        for r in range(t + 1):
            lhs = padd(lhs, prod_b(m - t, m, skip=m - r), (-1) ** r * comb(t, r))
        ok = ok and trim(lhs) == trim([0] * (3 * t) + [factorial(t)])
rep('thm3i_poly', ok, 'sum_r (-1)^r C(t,r) prod_{v in [m-t,m], v != m-r} b_v == t! x^{3t}, 0<=t<=m<=25')

ok = True
for m in range(0, 26):
    lhs = [0]
    sP = [0]
    for j in range(1, m + 1):
        Pj1 = prod_b(0, j - 1)
        lhs = padd(lhs, [0, 0, 0] + Pj1, j)
        sP = padd(sP, Pj1)
    rhs = padd(padd(prod_b(0, 0), prod_b(0, m), -1), [0] + sP, -1)
    ok = ok and trim(lhs) == trim(rhs)
rep('telescoping_poly', ok, 'x^3 sum_{j=1}^m j P_{j-1} == P_0 - P_m - x sum_{j=1}^m P_{j-1}, m<=25')

ok = True
for m in range(0, 16):
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, [0, 0] + prod_b(0, j - 1), j)
    for i in range(0, m + 1):
        V = [1]
        ff = 1
        for j in range(1, i + 1):
            ff *= (i - j + 1)
            V = padd(V, [0] * (3 * j + 2) + [1], j * ff)
        q, r = pdivmod(padd(W, V, -1), b(i) if i > 0 else [1, -1])
        ok = ok and r == [] and (len(q) - 1 <= 3 * m - 1)
        for j in range(1, m + 1):
            ffj = 1
            for tt in range(j):
                ffj *= (i - tt)
            q2, r2 = pdivmod(padd(prod_b(0, j - 1), [0] * (3 * j) + [ffj], -1), b(i) if i > 0 else [1, -1])
            ok = ok and r2 == []
rep('F4_congruences', ok, 'W_m == 1+sum_{j<=i} j i^(j) x^{3j+2} and P_{j-1} == i^(j) x^{3j} (mod b_i), deg quotient <= 3m-1, 0<=i<=m<=15')


# ---------------------------------------------------------------- 块分解 + phi（自写递归分块，按最大值首现）
def good(a, b_, c):
    return b_ == c or (a >= b_ and a >= c)


def legal(h):
    return all(good(h[i], h[i + 1], h[i + 2]) for i in range(len(h) - 2))


def parse_maxfirst(h, cap=None):
    """按定理 1 证明 (b)(c) 的思路递归：取 M = max h（并要求 <= cap），首块由 M 首现位置决定。
    返回块列表 [(type, level, a)] 或 None。"""
    if not h:
        return []
    M = max(h)
    if cap is not None and M > cap:
        return None
    if h[0] == M:
        rest = parse_maxfirst(h[1:], M)
        return None if rest is None else [('S', M, None)] + rest
    if len(h) >= 2 and h[1] == M:
        if len(h) == 2:
            return [('E', M, h[0])]
        if h[2] == M:
            rest = parse_maxfirst(h[3:], M)
            return None if rest is None else [('T', M, h[0])] + rest
        return None
    return None


def blocks_to_seq(bl):
    out = []
    for (tp, lv, a) in bl:
        out += [lv] if tp == 'S' else ([a, lv, lv] if tp == 'T' else [a, lv])
    return tuple(out)


def enum_blockstrings(k, m):
    """枚举全部合法块串（等级弱减，S/T 块，末尾可选一个 E 块），长度恰为 k，等级 <= m。"""
    res = []

    def rec(rem, cap, acc):
        if rem == 0:
            res.append(list(acc))
            return
        for lv in range(cap, -1, -1):
            acc.append(('S', lv, None))
            rec(rem - 1, lv, acc)
            acc.pop()
            if rem >= 3:
                for a in range(lv):
                    acc.append(('T', lv, a))
                    rec(rem - 3, lv, acc)
                    acc.pop()
            if rem == 2:
                for a in range(lv):
                    acc.append(('E', lv, a))
                    rec(0, lv, acc)
                    acc.pop()
    rec(k, m, [])
    return res


t0 = time.time()
ok = True
for m in range(0, 5):
    for k in range(0, 9):
        legal_set = set(h for h in product(range(m + 1), repeat=k) if legal(h))
        bs = enum_blockstrings(k, m)
        seqs = [blocks_to_seq(x) for x in bs]
        # 串联都合法、互不相同（唯一性）、且覆盖全部合法序列（存在性）
        ok = ok and all(len(s) == k for s in seqs) and len(set(seqs)) == len(seqs) and set(seqs) == legal_set
        ok = ok and all(parse_maxfirst(h) is not None and blocks_to_seq(parse_maxfirst(h)) == h for h in legal_set)
        ok = ok and all(parse_maxfirst(h) is None for h in product(range(m + 1), repeat=k) if h not in legal_set)
rep('block_factorization', ok, 'enumerated block strings (S/T weakly decreasing + optional final E) are pairwise distinct and their set == legal sequences; recursive max-first parser agrees; m<=4, k<=8 (%.1fs)' % (time.time() - t0))


def gam(n, j, m):
    if n < 0:
        return 0
    return sum(hfun(s, j, m) * C(n + m - j - 2 * s, m - j + s) for s in range(n // 3 + 1))


t0 = time.time()
ok = True
for m in range(0, 5):
    leg = {k: [h for h in product(range(m + 1), repeat=k) if legal(h)] for k in range(0, 10)}
    for k in range(0, 9):
        img = []
        for h in leg[k]:
            if k >= 2 and h[-1] > h[-2]:
                g = h + (h[-1],)
            else:
                g = h + (0,)
            assert legal(g)
            img.append(g)
        tgt = set()
        for g in leg[k + 1]:
            bl = parse_maxfirst(g)
            if bl[-1][0] == 'T' or (bl[-1][0] == 'S' and bl[-1][1] == 0):
                tgt.add(g)
        ok = ok and len(set(img)) == len(img) and set(img) == tgt
        noasc = sum(1 for h in leg[k] if not (k >= 2 and h[-1] > h[-2]))
        ok = ok and noasc == gam(k, 0, m)
        for j in range(1, m + 1):
            ok = ok and sum(1 for h in leg[k] if k >= 2 and h[-1] == j and h[-2] < j) == j * gam(k - 2, j, m)
        # F3 外层的组合含义：长 k+1 的 S/T 串 - 末块为 S_v (v>=1) 的串
        st_strings = [g for g in leg[k + 1] if not (len(g) >= 2 and g[-1] > g[-2])]
        endSv = [g for g in st_strings if parse_maxfirst(g)[-1][0] == 'S' and parse_maxfirst(g)[-1][1] >= 1]
        ok = ok and len(st_strings) == gam(k + 1, 0, m) and len(st_strings) - len(endSv) == len(leg[k])
rep('phi_bijection', ok, 'phi injective, image == {len k+1 legal, last block T or [0]}; no-ascent count == Gamma(k;0); E_j-ending == j Gamma(k-2;j); #ST(k+1) - #(last block S_v, v>=1) == U_k; m<=4, k<=8 (%.1fs)' % (time.time() - t0))

# 反例
P1 = pmul(b(0), b(1))


def ser_inv(p, N):
    r = [0] * N
    r[0] = 1
    for n in range(1, N):
        r[n] = -sum(p[i] * r[n - i] for i in range(1, min(n, len(p) - 1) + 1))
    return r


inv1 = ser_inv(P1, 10)
invb1 = ser_inv(b(1), 10)
theta_terms = (inv1[4], -invb1[3])
h_terms = (inv1[3], invb1[1])
rep('counterexample_m1k3', theta_terms == (8, -2) and h_terms == (5, 1) and sum(theta_terms) == sum(h_terms) == 6,
    'm=1,k=3: Theta-form terms (%d,%d), H-form terms (%d,%d), both sum to 6 = U_3(1)' % (theta_terms + h_terms))

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY r2 pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
