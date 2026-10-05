# -*- coding: utf-8 -*-
"""探索 2：p_d 在各种二项式基下的系数；Q_d(x)=(1-x)^{2d+1} sum_k D(k,d) x^k；缺陷多项式。"""
from math import factorial
from c4lib import *

KR = 140
NR = N_table_rec(KR)
DMAX = 9


def fit(d):
    ks = list(range(KR - 2 * d, KR + 1))
    return interpolate(ks, [Dval(NR, k, d) for k in ks])


def series_D(d, n):
    return [Dval(NR, k, d) for k in range(n)]


def mul_1mx_pow(ser, e, n):
    s = list(ser[:n])
    for _ in range(e):
        s = [s[i] - (s[i - 1] if i > 0 else 0) for i in range(n)]
    return s


P = {d: fit(d) for d in range(DMAX + 1)}
for d in range(DMAX + 1):
    p = P[d]
    n = 6 * d + 10
    ser = series_D(d, n)
    Q = trim(mul_1mx_pow(ser, 2 * d + 1, n))
    # 多项式部分 A_d：(1-x)^{2d+1} sum_{k>=0} p(k) x^k
    pser = [pval(p, k) for k in range(n)]
    A = trim(mul_1mx_pow(pser, 2 * d + 1, n))
    E = [ser[k] - pser[k] for k in range(n)]
    E = trim(E)
    print('=== d=%d' % d)
    print(' Q_d (full seq numerator, deg %d):' % (len(Q) - 1), Q)
    print(' A_d (poly part numerator, deg %d):' % (len(A) - 1), [str(a) for a in A])
    print(' E_d (D - p_d, k=0..):', [str(e) for e in E])
    # Newton 展开于基点 2d+1, 2d+2
    for base in (2 * d + 1, 2 * d + 2, d + 1):
        vals = [pval(p, base + i) for i in range(2 * d + 1)]
        diffs = []
        row = vals[:]
        for i in range(2 * d + 1):
            diffs.append(row[0])
            row = [row[j + 1] - row[j] for j in range(len(row) - 1)]
        print(' Newton at base %d:' % base, [str(x) for x in diffs])
    # 以 C(k+c-j, 2d) 为基，c 取若干值
    for c in range(-2, 2 * d + 1):
        # p(k) = sum_j a_j C(k+c-j, 2d)  <=> 生成函数里 a_j 对应 x^{j-c+2d}...
        # 直接解：令 k=j-c+2d ... 用 A 平移：A_d 是 c=2d 的系数；c 变化相当于整体平移下标
        pass
    # C(k+c-j,2d) 基的系数：a^{(c)}_j = A_{j + 2d - c}（需 0<=j+2d-c<=2d 范围外为 0 才是有限展开）
    print(' (c=2d basis) p_d(k) = sum_j A_j C(k-j+2d, 2d);  A_j:', [str(a) for a in A])
