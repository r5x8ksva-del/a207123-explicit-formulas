# -*- coding: utf-8 -*-
"""c2b 公式与细化 DP 工具。

细化 DP 只用原始三元组条件（与块分解无关）：
  状态 = (倒数第二项 a, 最后一项 b)，并记录已有上升次数 s。
返回 tables：
  tot[k][m][s]  —— 全部合法序列中上升次数为 s 的个数
  asc[k][m][s]  —— 以上升结尾（h_{k-1} < h_k）的个数
  comp = tot - asc —— 不以上升结尾（"完整"）的个数
"""
import sys, os
from math import comb
from functools import lru_cache

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))


def good3(a, b, c):
    return b == c or (a >= b and a >= c)


def binom(n, r):
    if r < 0 or n < 0 or r > n:
        return 0
    return comb(n, r)


@lru_cache(maxsize=None)
def stirling2(n, k):
    if n == 0 and k == 0:
        return 1
    if n <= 0 or k <= 0:
        return 0
    return k * stirling2(n - 1, k) + stirling2(n - 1, k - 1)


@lru_cache(maxsize=None)
def hcomp(s, lo, hi):
    """h_s(lo, lo+1, ..., hi)；区间空时 h_0 = 1，h_s = 0 (s>0)；s<0 时为 0。"""
    if s < 0:
        return 0
    if s == 0:
        return 1
    if lo > hi:
        return 0
    # h_s(lo..hi) = h_s(lo..hi-1) + hi * h_{s-1}(lo..hi)
    return hcomp(s, lo, hi - 1) + hi * hcomp(s - 1, lo, hi)


def refined_dp(K, m):
    """返回 (tot, asc)，tot[k][s]、asc[k][s]，0<=k<=K。直接三元组条件。"""
    S = K + 2
    tot = [[0] * S for _ in range(K + 1)]
    asc = [[0] * S for _ in range(K + 1)]
    tot[0][0] = 1
    if K >= 1:
        tot[1][0] = m + 1
    if K >= 2:
        for a in range(m + 1):
            for b in range(m + 1):
                s = 1 if a < b else 0
                tot[2][s] += 1
                if a < b:
                    asc[2][s] += 1
    # cnt[(a,b)] = list over s
    cnt = {}
    for a in range(m + 1):
        for b in range(m + 1):
            v = [0] * S
            v[1 if a < b else 0] = 1
            cnt[(a, b)] = v
    for k in range(3, K + 1):
        new = {}
        for (a, b), vec in cnt.items():
            for c in range(m + 1):
                if not good3(a, b, c):
                    continue
                inc = 1 if b < c else 0
                key = (b, c)
                tgt = new.get(key)
                if tgt is None:
                    tgt = [0] * S
                    new[key] = tgt
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
    """另一种直接 DP：返回 dict 计数（全部 k<=K）
    end0[k]   = 长 k、最后一项为 0 的合法序列数
    endTpat[k]= 长 k (k>=3)、末三项满足 h_{k-2} < h_{k-1} = h_k 的合法序列数
    """
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


# ---------------- 公式 ----------------
def A_complete(k, m, s):
    """不以上升结尾、上升次数 s 的个数 = S(m+s,m) C(k+m-2s, k-3s)。"""
    return stirling2(m + s, m) * binom(k + m - 2 * s, k - 3 * s)


def E_asc(k, m, s):
    """以上升结尾、上升次数 s（s>=1）的个数 = sum_{j=1}^m j H(m,s-1,j) C(k+m-j-2s, k+1-3s)。"""
    if s < 1:
        return 0
    return sum(j * hcomp(s - 1, j, m) * binom(k + m - j - 2 * s, k + 1 - 3 * s) for j in range(1, m + 1))


def U_explicit(k, m):
    smax = k // 3 + 2
    return sum(A_complete(k, m, s) + E_asc(k, m, s) for s in range(0, smax + 1))


def A_total(n, m):
    """[x^n] 1/P_m = sum_s S(m+s,m) C(n+m-2s, n-3s)，n<0 时为 0。"""
    if n < 0:
        return 0
    return sum(A_complete(n, m, s) for s in range(0, n // 3 + 1))


def Aj_total(n, m, j):
    """[x^n] prod_{i=j}^m b_i^{-1} = sum_s H(m,s,j) C(n+m-j-2s, n-3s)。"""
    if n < 0:
        return 0
    return sum(hcomp(s, j, m) * binom(n + m - j - 2 * s, n - 3 * s) for s in range(0, n // 3 + 1))
