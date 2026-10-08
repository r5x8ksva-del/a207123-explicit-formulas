# -*- coding: utf-8 -*-
"""复核者 s14-b9 的公共函数（只用标准库；不 import 项目里的任何代码）。

真值：U_k(m) = 长 k、取值于 {0..m}、每个相邻三元组 (a,b,c) 满足「b=c 或 a>=max(b,c)」的序列个数。
  brute_U      逐个枚举（只用于很小的 k、m）
  pair_dp_U    以「最后两个值 (a,b)」为状态、逐个检查三元组条件的朴素 DP
  rt_dp_U      我自己由状态机压缩得到的 O(m)/步 DP（见下面的推导），与 pair_dp_U 对照后用于大 k
压缩 DP 的推导（复核者自推）：长度 >=2 的序列按最后两个值 (p,v) 分两类：
  p>=v（「自由」）：下一个值 c 可取 [0,p] 中任意值；p<v（「强制」）：下一个值只能是 v。
  记 S_k(v,p)（p>=v）为自由态个数，R_k(v)=sum_{p>=v} S_k(v,p)，T_k(v)=sum_{p<v}（强制态个数）。
  追加 c：自由态 (v,p) -> c<=v 时到自由态 (c, 上限 v)；v<c<=p 时到强制态 c；强制态 v -> c=v 到自由态 (v,v)。
  于是 S_{k+1}(c,v)=R_k(v)+[c=v]T_k(v)（c<=v），R_{k+1}(c)=sum_{v>=c}R_k(v)+T_k(c)，
  T_{k+1}(c)=sum_{v<c} sum_{p>=c} S_k(v,p)=c*sum_{p>=c}R_{k-1}(p)（v<p 时 S_k(v,p)=R_{k-1}(p)；k=2 时取 R_1≡1）。
  初值 R_2(v)=m-v+1，T_2(v)=v；U_k(m)=sum_v(R_k(v)+T_k(v))（k>=2），U_0=1，U_1=m+1。
"""
from itertools import product
from math import comb


def brute_U(k, m):
    cnt = 0
    for s in product(range(m + 1), repeat=k):
        ok = True
        for i in range(k - 2):
            a, b, c = s[i], s[i + 1], s[i + 2]
            if not (b == c or a >= max(b, c)):
                ok = False
                break
        if ok:
            cnt += 1
    return cnt


def pair_dp_U(K, m):
    """[U_0(m),...,U_K(m)]，状态为最后两个值 (a,b)，逐个检查三元组条件。"""
    out = [1, m + 1, (m + 1) ** 2]
    cnt = [[1] * (m + 1) for _ in range(m + 1)]
    for _k in range(3, K + 1):
        new = [[0] * (m + 1) for _ in range(m + 1)]
        for a in range(m + 1):
            row = cnt[a]
            for b in range(m + 1):
                x = row[b]
                if x == 0:
                    continue
                nb = new[b]
                for c in range(m + 1):
                    if b == c or a >= max(b, c):
                        nb[c] += x
        cnt = new
        out.append(sum(map(sum, cnt)))
    return out[:K + 1]


def rt_dp_U(K, m):
    """[U_0(m),...,U_K(m)]，压缩 DP（推导见模块说明）。"""
    out = [1, m + 1]
    if K < 2:
        return out[:K + 1]
    R_prev = [1] * (m + 1)                     # R_1
    R = [m - v + 1 for v in range(m + 1)]      # R_2
    T = list(range(m + 1))                     # T_2
    out.append(sum(R) + sum(T))
    for _k in range(2, K):
        sR = [0] * (m + 2)
        sP = [0] * (m + 2)
        for v in range(m, -1, -1):
            sR[v] = sR[v + 1] + R[v]
            sP[v] = sP[v + 1] + R_prev[v]
        Rn = [sR[c] + T[c] for c in range(m + 1)]
        Tn = [c * sP[c] for c in range(m + 1)]
        R_prev, R, T = R, Rn, Tn
        out.append(sum(R) + sum(T))
    return out


def U_table(M, K):
    """U[m][k] = U_k(m)，0<=m<=M，0<=k<=K（压缩 DP）。"""
    return [rt_dp_U(K, m) for m in range(M + 1)]


def h_coef(U, k, i):
    """h_{k,i} = sum_{r=0}^{i} (-1)^r C(k+1,r) U_k(i-r)（由 sum_m U_k(m) t^m = h_k/(1-t)^{k+1}）。"""
    return sum((-1) ** r * comb(k + 1, r) * U[i - r][k] for r in range(i + 1))


def h_poly_from_Ucol(Uk, k):
    """给定 Uk[m]=U_k(m)（m=0..len-1，len>=d+1），返回 h_k 的系数列表（截到最后一个非零系数）。"""
    n = len(Uk)
    h = [sum((-1) ** r * comb(k + 1, r) * Uk[i - r] for r in range(i + 1)) for i in range(n)]
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


def h_rec_iter(K):
    """自写的 T1.7 递推 h_k = h_{k-1} + t(1-t)[(1-t)h'_{k-3} + (k-2)h_{k-3}]（k>=3），初值 h_0=1,h_1=1,h_2=1+t。
    逐个产出 (k, h_k)。只在与 DP 得到的 h 对照过的前提下用于大 k。"""
    hist = {0: [1], 1: [1], 2: [1, 1]}
    for k in range(K + 1):
        if k >= 3:
            g = hist[k - 3]
            # A = (1-t) g' + (k-2) g
            gp = [i * g[i] for i in range(1, len(g))]          # g'
            A = [0] * (len(g) + 1)
            for i, x in enumerate(gp):
                A[i] += x
                A[i + 1] -= x
            for i, x in enumerate(g):
                A[i] += (k - 2) * x
            # B = t(1-t) A = t A - t^2 A
            B = [0] * (len(A) + 2)
            for i, x in enumerate(A):
                B[i + 1] += x
                B[i + 2] -= x
            prev = hist[k - 1]
            n = max(len(prev), len(B))
            h = [(prev[i] if i < len(prev) else 0) + (B[i] if i < len(B) else 0) for i in range(n)]
            while len(h) > 1 and h[-1] == 0:
                h.pop()
            hist[k] = h
            del hist[k - 3]
        yield k, hist[k]


def sign_changes(seq):
    s = [x for x in seq if x != 0]
    return sum(1 for a, b in zip(s, s[1:]) if (a > 0) != (b > 0))
