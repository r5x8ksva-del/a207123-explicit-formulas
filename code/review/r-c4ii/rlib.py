# -*- coding: utf-8 -*-
"""r-c4ii 复核用的独立小工具（不 import 被复核者的 c4lib / check_c4；core 只用于交叉对照）。

多项式：系数列表 p[i] = [x^i]，int 或 Fraction。
"""
import os
import sys
from fractions import Fraction
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
CODE = os.path.join(ROOT, 'code')
LOGS = os.path.join(ROOT, 'logs')


# ---------------------------------------------------------------- 多项式
def tr(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    n = max(len(p), len(q))
    return tr([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def sub(p, q):
    n = max(len(p), len(q))
    return tr([(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(n)])


def scl(p, c):
    return tr([c * a for a in p])


def mul(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    r[i + j] += a * b
    return tr(r)


def mul_trunc(p, q, n):
    """p*q mod x^n。"""
    r = [0] * n
    for i, a in enumerate(p[:n]):
        if a:
            for j in range(min(len(q), n - i)):
                b = q[j]
                if b:
                    r[i + j] += a * b
    return r


def shift(p, k):
    return ([0] * k + list(p)) if p else []


def ev(p, x):
    r = 0
    for a in reversed(p):
        r = r * x + a
    return r


def divmod_poly(p, q):
    """有理系数带余除法。"""
    p = [Fraction(a) for a in tr(p)]
    q = [Fraction(a) for a in tr(q)]
    out = [Fraction(0)] * max(len(p) - len(q) + 1, 0)
    while len(p) >= len(q) and p:
        c = p[-1] / q[-1]
        d = len(p) - len(q)
        out[d] = c
        for i, b in enumerate(q):
            p[i + d] -= c * b
        p = tr(p)
    return tr(out), p


def bpoly(i):
    return tr([1, -1, 0, -i])


def Ppoly(m):
    p = [1]
    for i in range(m + 1):
        p = mul(p, bpoly(i))
    return p


def falling(n, t):
    r = 1
    for u in range(t):
        r *= (n - u)
    return r


# ---------------------------------------------------------------- 原始定义：自写高度 DP
def good(a, b, c):
    return b == c or (a >= b and a >= c)


def U_column_mine(m, K):
    """[U_0(m),...,U_K(m)]：长度 k、取值 {0..m}、每个相邻三元组满足 good 的序列数。
    自写实现：状态 (a,b)=最后两项；用 good 的定义直接分情况（b==c 全取；否则 a>=max(b,c)）。"""
    n = m + 1
    out = [1]
    if K >= 1:
        out.append(n)
    if K >= 2:
        out.append(n * n)
    cnt = [[1] * n for _ in range(n)]   # cnt[a][b]
    for _k in range(3, K + 1):
        # col_suffix[b][t] = sum_{a>=t} cnt[a][b]
        new = [[0] * n for _ in range(n)]
        for b in range(n):
            s = [0] * (n + 1)
            for a in range(n - 1, -1, -1):
                s[a] = s[a + 1] + cnt[a][b]
            for c in range(n):
                new[b][c] = s[0] if c == b else s[max(b, c)]
        cnt = new
        out.append(sum(sum(r) for r in cnt))
    return out[:K + 1]


def U_column_naive(m, K):
    """最朴素版本（逐个 a 检查 good），只用于小规模交叉对照。"""
    n = m + 1
    out = [1, n, n * n][:K + 1]
    cnt = {(a, b): 1 for a in range(n) for b in range(n)}
    for _k in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in range(n):
                if good(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
        cnt = new
        out.append(sum(cnt.values()))
    return out


def words_brute(k, maxval):
    """按定义暴力：所有 {1..maxval}^k 的词，返回 dict q -> 值域恰为 {1..q} 的合法词数。"""
    from itertools import product
    res = {}
    for w in product(range(1, maxval + 1), repeat=k):
        if all(good(w[i], w[i + 1], w[i + 2]) for i in range(k - 2)):
            s = set(w)
            q = len(s)
            if s == set(range(1, q + 1)):
                res[q] = res.get(q, 0) + 1
    return res


def N_table_from_U(Ucols, K, Q):
    """N[k][q]（0<=k<=K, 0<=q<=Q），Ucols[m] = [U_0(m)..U_K(m)]，需要 m<=Q-1。
    N(k,q) = sum_{i=0}^q (-1)^{q-i} C(q,i) U_k(i-1)，U_k(-1)=[k==0]。"""
    N = [[0] * (Q + 1) for _ in range(K + 1)]
    for k in range(K + 1):
        for q in range(Q + 1):
            s = 0
            for i in range(q + 1):
                u = (1 if k == 0 else 0) if i == 0 else Ucols[i - 1][k]
                s += (-1) ** (q - i) * comb(q, i) * u
            N[k][q] = s
    return N


# ---------------------------------------------------------------- Num_q（自写三项递推）
def num_by_recurrence(QM):
    Num = {0: [1], 1: [0, 1], 2: [0, 0, 2, 0, 1]}
    for q in range(3, QM + 1):
        t1 = mul([0, 1, 0, 2 * (q - 1)], Num[q - 1])
        t2 = scl(mul(shift(bpoly(q - 2), 3), Num[q - 2]), q - 1)
        Num[q] = add(t1, t2)
    return Num


def W_poly(m):
    """W_m = 1 + x^2 sum_{j=1}^m j P_{j-1}，W_{-1}=1。"""
    w = [1]
    P = bpoly(0)          # P_0
    for j in range(1, m + 1):
        w = add(w, shift(scl(P, j), 2))   # + j x^2 P_{j-1}
        P = mul(P, bpoly(j))              # 更新为 P_j
    return w


def stirling1(nmax):
    c = [[0] * (nmax + 2) for _ in range(nmax + 1)]
    c[0][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            c[n][k] = (n - 1) * c[n - 1][k] + c[n - 1][k - 1]
    return c


class Log:
    def __init__(self, name):
        self.path = os.path.join(LOGS, 'review_r-c4ii_%s.log' % name)
        self.f = open(self.path, 'w', encoding='utf-8')
        self.npass = 0
        self.nfail = 0

    def out(self, s):
        print(s, flush=True)
        self.f.write(s + '\n')
        self.f.flush()

    def check(self, cid, ok, desc):
        self.out(('PASS ' if ok else 'FAIL ') + cid + ' ' + desc)
        if ok:
            self.npass += 1
        else:
            self.nfail += 1

    def close(self, t0=None):
        import time
        if t0 is not None:
            self.out('# runtime %.1fs' % (time.time() - t0))
        self.out('SUMMARY pass=%d fail=%d' % (self.npass, self.nfail))
        self.f.close()
