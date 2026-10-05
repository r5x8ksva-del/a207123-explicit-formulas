# -*- coding: utf-8 -*-
"""r-c2a 复核脚本 5：零散补充核对（独立实现）。
  - N(k,q) 反演式对照 DFS 定义扩到 k=10；
  - 定理 3 附注：sum_i (-1)^{m-i} C(m,i) c_i(N) = 0 (0<=N<3m)，且 N=3m 时 = m!；
  - 别名：(x+r)^n = sum_k {n+r \\ k+r}_r x^(k)（r-Whitney W_{1,r}(n,k) 的定义式）；
  - F4 的 m=1 例：R_k = c_1(k+3) + c_1(k-2) - 1。
"""
import time
from math import comb, factorial

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


def U_col(m, K):
    out = [1, m + 1]
    n = m + 1
    cnt = [[1] * n for _ in range(n)]
    out.append(n * n)
    for _ in range(3, K + 1):
        new = [[0] * n for _ in range(n)]
        for b in range(n):
            suf = [0] * (n + 1)
            for a in range(n - 1, -1, -1):
                suf[a] = suf[a + 1] + cnt[a][b]
            for c in range(n):
                new[b][c] = suf[0] if b == c else suf[max(b, c)]
        cnt = new
        out.append(sum(map(sum, cnt)))
    return out


def stirling2(N):
    S = [[0] * (N + 1) for _ in range(N + 1)]
    S[0][0] = 1
    for n in range(1, N + 1):
        for k in range(1, n + 1):
            S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
    return S


S = stirling2(60)


def UH(k, m):
    tot = sum(S[m + s][m] * C(k + m - 2 * s, m + s) for s in range(k // 3 + 1))
    if k >= 2:
        for j in range(1, m + 1):
            tot += j * sum(hfun(s, j, m) * C(k - 2 + m - j - 2 * s, m - j + s) for s in range((k - 2) // 3 + 1))
    return tot


# N 的 DFS（迭代栈，值域 0..k-1，只保留合法前缀）
def N_dfs(k):
    res = [0] * (k + 1)
    stack = [()]
    while stack:
        seq = stack.pop()
        if len(seq) == k:
            st = set(seq)
            q = len(st)
            if max(seq) == q - 1:
                res[q] += 1
            continue
        L = len(seq)
        for v in range(k):
            if L >= 2:
                a, b = seq[-2], seq[-1]
                if not (b == v or (a >= b and a >= v)):
                    continue
            stack.append(seq + (v,))
    return res


t0 = time.time()
k = 10
br = N_dfs(k)
inv = [sum((-1) ** (q - i) * comb(q, i) * UH(k, i - 1) for i in range(1, q + 1)) for q in range(k + 1)]
rep('N_inversion_k10', br == inv, 'N(10,q), q=0..10: DFS %s == inversion of H form (%.1fs)' % (br, time.time() - t0))


def c_rec(i, N):
    c = [0] * (N + 1)
    for n in range(N + 1):
        c[n] = (1 if n == 0 else 0) + (c[n - 1] if n >= 1 else 0) + (i * c[n - 3] if n >= 3 else 0)
    return c


ok = True
for m in range(0, 21):
    cs = [c_rec(i, 3 * m + 2) for i in range(m + 1)]
    for N in range(0, 3 * m + 1):
        val = sum((-1) ** (m - i) * comb(m, i) * cs[i][N] for i in range(m + 1))
        ok = ok and val == (factorial(m) if N == 3 * m else 0)
rep('alt_sum_vanish', ok, 'sum_i (-1)^(m-i) C(m,i) c_i(N) == 0 for 0<=N<3m and == m! at N=3m, m<=20')


# r-Whitney 别名：(x+r)^n = sum_k {n+r \ k+r}_r x^(k)，{n+r \ k+r}_r = h_{n-k}(r..k+r)
def falling(x, k):
    p = 1
    for i in range(k):
        p *= (x - i)
    return p


ok = all((x + r) ** n == sum(hfun(n - kk, r, kk + r) * falling(x, kk) for kk in range(n + 1))
         for r in range(0, 8) for n in range(0, 12) for x in range(-5, 15))
rep('rWhitney_alias', ok, '(x+r)^n == sum_k h_{n-k}(r..k+r) x^(k) (x integer in [-5,14], r<=7, n<=11)')

c1 = c_rec(1, 80)
col = U_col(1, 70)
ok = all(col[k] == c1[k + 3] + (c1[k - 2] if k >= 2 else 0) - 1 for k in range(0, 71))
rep('F4_m1_example', ok, 'R_k = U_k(1) == c_1(k+3) + c_1(k-2) - 1 (c_1(n<0)=0), k<=70')

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY r5 pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
