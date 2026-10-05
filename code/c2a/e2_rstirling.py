# -*- coding: utf-8 -*-
"""探索 2：Broder r-Stirling 数 —— 定义（分拆暴力计数）/ 递推 / 母函数 / h_complete / 差分恒等式。"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c2a_lib import *  # noqa
from core import h_complete, stirling2_table
from polylib import series_inv, pmul


def set_partitions_rgs(n):
    """生成 {1..n} 的所有集合分拆（受限增长串 a[0..n-1]，块号从 0 起）。"""
    if n == 0:
        yield []
        return
    a = [0] * n

    def rec(i, mx):
        if i == n:
            yield a
            return
        for v in range(mx + 2):
            a[i] = v
            yield from rec(i + 1, max(mx, v))

    a[0] = 0
    yield from rec(1, 0)


def rstirling_brute(nmax):
    """B[(n,k,r)] = #{ {1..n} 分成 k 块，且 1..r 两两不同块 }，0<=r<=n<=nmax。"""
    B = {}
    for n in range(nmax + 1):
        cnt = {}
        for a in set_partitions_rgs(n):
            k = (max(a) + 1) if n else 0
            for r in range(n + 1):
                if len(set(a[:r])) == r:
                    cnt[(k, r)] = cnt.get((k, r), 0) + 1
        for (k, r), v in cnt.items():
            B[(n, k, r)] = v
    return B


def rstirling_rec(nmax):
    R = {}
    for r in range(nmax + 1):
        for n in range(r, nmax + 1):
            for k in range(0, n + 1):
                if n == r:
                    R[(n, k, r)] = 1 if k == r else 0
                else:
                    R[(n, k, r)] = k * R.get((n - 1, k, r), 0) + R.get((n - 1, k - 1, r), 0)
    return R


t0 = time.time()
NB = 10
B = rstirling_brute(NB)
ok = True
for n in range(NB + 1):
    for r in range(n + 1):
        for k in range(r, n + 1):
            if B.get((n, k, r), 0) != h_complete(n - k, r, k):
                ok = False
                print('brute vs h mismatch', n, k, r)
print('r-Stirling brute (n<=%d, 0<=r<=k<=n) == h_{n-k}(r..k):' % NB, ok, '%.1fs' % (time.time() - t0))

NR = 40
R = rstirling_rec(NR)
ok = all(R[(n, k, r)] == h_complete(n - k, r, k) for r in range(NR + 1) for n in range(r, NR + 1) for k in range(r, n + 1))
ok2 = all(R[(n, k, r)] == B.get((n, k, r), 0) for r in range(NB + 1) for n in range(r, NB + 1) for k in range(0, n + 1))
print('r-Stirling recurrence (n<=%d) == h_complete:' % NR, ok, '; == brute incl. k<r zeros (n<=%d):' % NB, ok2)

# 母函数：sum_n {n\k}_r z^n = z^k / prod_{i=r}^k (1 - i z)
ok = True
L = 30
for r in range(0, 12):
    for k in range(r, 12):
        den = [1]
        for i in range(r, k + 1):
            den = pmul(den, [1, -i])
        ser = series_inv(den, L)
        for n in range(k, k + L):
            if R[(n, k, r)] != ser[n - k]:
                ok = False
print('GF z^k/prod(1-iz) (r<=k<=11, n<k+30):', ok)

# 差分恒等式：(1/t!) nabla^t i^p |_{i=m} = h_{p-t}(m-t..m) = {p+m-t \ m}_{m-t}
ok = True
for m in range(0, 21):
    for t in range(0, m + 1):
        for p in range(0, 41):
            s = sum((-1) ** r * comb(t, r) * (m - r) ** p for r in range(t + 1))
            q, rem = divmod(s, factorial(t))
            if rem != 0 or q != h_complete(p - t, m - t, m) if p >= t else (s != 0):
                ok = False
                print('nabla mismatch', m, t, p)
            if p >= t and q != R.get((p + m - t, m, m - t), None) and p + m - t <= NR:
                ok = False
                print('nabla vs rstirling mismatch', m, t, p)
print('nabla identity (m<=20, t<=m, p<=40):', ok)

# 显式式 rstirling_explicit 与 Stirling 第二类
S = stirling2_table(40)
ok = all(rstirling_explicit(n, k, r) == R[(n, k, r)] for r in range(0, 15) for n in range(r, 30) for k in range(r, n + 1))
ok2 = all(h_complete(s, 0, m) == S[m + s][m] == h_complete(s, 1, m) for m in range(0, 20) for s in range(0, 20))
print('r-Stirling explicit formula ok:', ok, '; h_s(0..m)=h_s(1..m)=S(m+s,m):', ok2)
print('total %.1fs' % (time.time() - t0))
