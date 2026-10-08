# -*- coding: utf-8 -*-
"""复核者 s15-b13 的公共工具（只用标准库；不导入项目里的任何代码）。

真值一律从原始定义出发：U_k(m) = 高度向量 (h_1..h_k)∈{0..m}^k 的个数，
每个相邻三元组 (a,b,c) 满足 b==c 或 a>=max(b,c)（原始任务说明 §1(b)）。
"""
import sys
from fractions import Fraction as Fr
from itertools import product
from math import comb, factorial


def setup_stdout():
    try:
        sys.stdout.reconfigure(encoding='utf-8')
    except Exception:
        pass


class Reporter:
    def __init__(self, tag):
        self.tag = tag
        self.rows = []

    def check(self, cid, ok, desc):
        self.rows.append((cid, bool(ok)))
        print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)

    def info(self, msg):
        print('INFO ' + msg, flush=True)

    def summary(self):
        p = sum(1 for _, ok in self.rows if ok)
        f = len(self.rows) - p
        print('SUMMARY %s pass=%d fail=%d' % (self.tag, p, f), flush=True)
        return 0 if f == 0 else 1


# ------------------------------------------------------------------ 原始定义
def good(a, b, c):
    return b == c or (a >= b and a >= c)


def U_brute(k, m):
    """逐个枚举高度向量（只用于很小的 k、m）。"""
    cnt = 0
    for h in product(range(m + 1), repeat=k):
        if all(good(h[i], h[i + 1], h[i + 2]) for i in range(k - 2)):
            cnt += 1
    return cnt


def U_dp_naive(K, m):
    """以最后两个值为状态的 DP，逐个三元组字面检查。返回 [U_0(m),...,U_K(m)]。"""
    out = [1]
    if K >= 1:
        out.append(m + 1)
    if K >= 2:
        cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
        out.append(sum(cnt.values()))
        for _ in range(3, K + 1):
            new = {}
            for (a, b), v in cnt.items():
                for c in range(m + 1):
                    if good(a, b, c):
                        new[(b, c)] = new.get((b, c), 0) + v
            cnt = new
            out.append(sum(cnt.values()))
    return out[:K + 1]


def U_dp_fast(K, m):
    """压缩 DP（我自己推的）：从 (a,b) 出发，a>=b 时 c 可取 0..a；a<b 时只能 c=b。
    于是 new[b][c] = Σ_{a>=max(b,c)} cnt[a][b] + [c==b]·Σ_{a<b} cnt[a][b]。O(m^2)/步。"""
    M = m + 1
    out = [1]
    if K >= 1:
        out.append(M)
    if K < 2:
        return out[:K + 1]
    cnt = [[1] * M for _ in range(M)]   # cnt[a][b]
    out.append(M * M)
    for _ in range(3, K + 1):
        # 对每个 b，suffix[b][s] = Σ_{a>=s} cnt[a][b]
        new = [[0] * M for _ in range(M)]
        for b in range(M):
            suf = [0] * (M + 1)
            for a in range(M - 1, -1, -1):
                suf[a] = suf[a + 1] + cnt[a][b]
            low = suf[0] - suf[b]          # Σ_{a<b}
            for c in range(M):
                v = suf[max(b, c)]
                if c == b:
                    v += low
                new[b][c] = v
        cnt = new
        out.append(sum(sum(r) for r in cnt))
    return out[:K + 1]


def U_table_lemma1(K, M):
    """引理 1（三项递推，T1.1，已形式化）：U_k(m)=U_k(m-1)+U_{k-1}(m)+m·U_{k-3}(m)，
    U_0≡1，U_{-1}≡1，U_{-2}≡0，U_k(-1)=0（k>=1）。返回 T[k][m]，0<=k<=K，0<=m<=M。"""
    def get(T, k, m):
        if k == -1:
            return 1
        if k == -2:
            return 0
        if m < 0:
            return 1 if k == 0 else 0
        return T[k][m]
    T = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        T[0][m] = 1
    for k in range(1, K + 1):
        for m in range(M + 1):
            T[k][m] = get(T, k, m - 1) + get(T, k - 1, m) + m * get(T, k - 3, m)
    return T


def N_from_U(Ucol):
    """由 V(n)=U_k(n-1)（n 个字母上的合法词数）做容斥得 N(k,q)=Σ_n (-1)^{q-n} C(q,n) V(n)。
    Ucol[m]=U_k(m)，m=0..Q-1；返回 [N(k,0..Q)]（V(0)=U_k(-1)，k>=1 时为 0）。"""
    Q = len(Ucol)
    V = [0] + list(Ucol)          # V[n] = U_k(n-1)
    return [sum((-1) ** (q - n) * comb(q, n) * V[n] for n in range(q + 1)) for q in range(Q + 1)]


def N_rows(K):
    """原始任务说明 (C3) 的三角形递推；逐行产生 (k, row)，row[q]=N(k,q)，q=0..k。"""
    rows = {0: [1], 1: [0, 1], 2: [0, 1, 2]}
    for k in range(0, min(K, 2) + 1):
        yield k, rows[k]
    for k in range(3, K + 1):
        a, b = rows[k - 1], rows[k - 3]

        def g(row, q):
            return row[q] if 0 <= q < len(row) else 0
        row = [0] * (k + 1)
        for r in range(0, k):
            row[r + 1] = g(a, r) + g(a, r + 1) + r * (g(b, r - 1) + 2 * g(b, r) + g(b, r + 1))
        rows[k] = row
        del rows[k - 3]
        yield k, row


# ------------------------------------------------------------------ λ 的整系数多项式
def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pscale(a, c):
    return [c * v for v in a]


def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def pshift(a, s):
    return [0] * s + list(a)


def ptrim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def pderiv(a):
    return [i * a[i] for i in range(1, len(a))]


def peval(a, x):
    v = 0
    for c in reversed(a):
        v = v * x + c
    return v


def lam_minus_1_powers(C):
    """(λ-1)^c，c=0..C，整系数。"""
    out = [[1]]
    for _ in range(C):
        out.append(pmul(out[-1], [-1, 1]))
    return out


# ------------------------------------------------------------------ Stirling 数
def stirling2_table(N):
    """S2[n][k]，0<=n,k<=N。"""
    S = [[0] * (N + 1) for _ in range(N + 1)]
    S[0][0] = 1
    for n in range(1, N + 1):
        for k in range(1, n + 1):
            S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
    return S


def stirling2_ge2_table(N):
    """S≥2[n][c]：n 元集分成 c 块、每块大小>=2 的方式数。
    递推 S(n,c)=c·S(n-1,c)+(n-1)·S(n-2,c-1)，S(0,0)=1。"""
    S = [[0] * (N + 1) for _ in range(N + 1)]
    S[0][0] = 1
    for n in range(1, N + 1):
        for c in range(0, N + 1):
            v = c * S[n - 1][c]
            if n >= 2 and c >= 1:
                v += (n - 1) * S[n - 2][c - 1]
            S[n][c] = v
    return S


FACT = [1]


def fact(n):
    while len(FACT) <= n:
        FACT.append(FACT[-1] * len(FACT))
    return FACT[n]
