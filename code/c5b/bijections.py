# -*- coding: utf-8 -*-
"""c5b 探索：U_3 与 U_4 的显式双射（按原始定义枚举合法高度序列，穷举核对）。

U_3：合法三元组 (a,b,c)（b==c 或 a>=max(b,c)）<-> {0..m}^3 中单调三元组（非增或非减）。
U_4：合法 4 元组 <-> {0..m+1} 上「不交叉也不嵌套」的有序边对（A326247 的对象，n=m+2 个顶点）。
"""
import os
import sys
from itertools import product, combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import good, U_fast_column, binom  # noqa: E402


def legal(seq):
    return all(good(seq[i], seq[i + 1], seq[i + 2]) for i in range(len(seq) - 2))


# ---------------- U_3 ----------------
def f3(t):
    a, b, c = t
    if a >= b >= c:
        return (a, b, c)            # 非增：不动
    if b == c:                       # 此时 a < b
        return (a, a, b)
    return (b, c, a)                 # b != c => a >= max(b,c)；又非非增 => b < c <= a


def monotone(t):
    a, b, c = t
    return (a <= b <= c) or (a >= b >= c)


def check_U3(M):
    for m in range(M + 1):
        L = [t for t in product(range(m + 1), repeat=3) if legal(t)]
        img = [f3(t) for t in L]
        mono = {t for t in product(range(m + 1), repeat=3) if monotone(t)}
        assert len(L) == U_fast_column(m, 3)[3]
        assert len(set(img)) == len(img), m               # 单射
        assert set(img) == mono, m                         # 满射到单调三元组
        assert all(set(f3(t)) == set(t) for t in L)        # 保持取值集合
        assert len(mono) == 2 * binom(m + 3, 3) - (m + 1)
    return True


# ---------------- U_4 ----------------
def type4(h):
    h1, h2, h3, h4 = h
    if h1 >= h2 >= h3 >= h4:
        return 'SSSS'
    if h3 == h4 > h2 and h1 >= h3:
        return 'ST'
    if h2 == h3 > h1 and h4 <= h3:
        return 'TS'
    if h1 >= h2 >= h4 > h3:
        return 'SSE'
    return None


def Phi(h):
    """合法 4 元组 -> 区间对 ([x1,y1],[x2,y2])，0<=x<=y<=m。"""
    h1, h2, h3, h4 = h
    t = type4(h)
    if t == 'SSSS':
        if h3 < h2:
            return ((h2, h1), (h4, h3))     # D2：第二个区间整体在左
        return ((h4, h3), (h4, h1))         # L<=：同左端点，y1<=y2
    if t == 'ST':                           # (v,a,w,w), v>=w>a
        v, a, w = h1, h2, h3
        if w < v:
            return ((a, v), (a, w))         # L>：同左端点，y1>y2
        return ((a, w), (a, a))
    if t == 'TS':                           # (a,v,v,w), a<v, w<=v
        a, v, w = h1, h2, h4
        if w != a:
            return ((a, v), (w, v))         # R'：同右端点，左端点不同
        return ((v, v), (a, v))
    if t == 'SSE':                          # (v,w,a,j), v>=w>=j>a
        v, w, a, j = h1, h2, h3, h4
        if j < w:
            return ((a, j), (w, v))         # D1：第一个区间整体在左
        return ((a, a), (j, v))
    raise ValueError(h)


def interval_class(I1, I2):
    (x1, y1), (x2, y2) = I1, I2
    if x1 == x2:
        return 'L'
    if y1 == y2:
        return "R'"
    if y1 < x2:
        return 'D1'
    if y2 < x1:
        return 'D2'
    return None   # 相交且两端点都不同：交叉或嵌套


def to_edges(I1, I2):
    (x1, y1), (x2, y2) = I1, I2
    return ((x1, y1 + 1), (x2, y2 + 1))


def crossing_or_nesting(e1, e2):
    """A326247 %C 的原文条件：{a,b},{c,d} 交叉 a<c<b<d 或 c<a<d<b；嵌套 a<c<d<b 或 c<a<b<d。"""
    a, b = e1
    c, d = e2
    cross = (a < c < b < d) or (c < a < d < b)
    nest = (a < c < d < b) or (c < a < b < d)
    return cross or nest


def A326247_objects(n):
    E = list(combinations(range(n), 2))
    return [(e1, e2) for e1 in E for e2 in E if not crossing_or_nesting(e1, e2)]


def check_U4(M):
    for m in range(M + 1):
        L = [h for h in product(range(m + 1), repeat=4) if legal(h)]
        assert len(L) == U_fast_column(m, 4)[4]
        assert all(type4(h) is not None for h in L)
        img = []
        for h in L:
            I1, I2 = Phi(h)
            assert 0 <= I1[0] <= I1[1] <= m and 0 <= I2[0] <= I2[1] <= m
            assert interval_class(I1, I2) is not None
            assert {I1[0], I1[1], I2[0], I2[1]} == set(h)           # 保持取值集合
            img.append(to_edges(I1, I2))
        assert len(set(img)) == len(img)
        objs = set(A326247_objects(m + 2))
        assert set(img) == objs, (m, len(objs), len(img))
        # 类型对应
        pair = {}
        for h in L:
            key = (type4(h), interval_class(*Phi(h)))
            pair[key] = pair.get(key, 0) + 1
        if m == 3:
            print('type -> class counts (m=3):', sorted(pair.items()))
    return True


if __name__ == '__main__':
    print('U3 bijection m<=20:', check_U3(20))
    print('U4 bijection m<=10:', check_U4(10))
    # 不交叉不嵌套的无序/有序计数，与条目数据对照
    for n in range(0, 8):
        ordered = len(A326247_objects(n))
        E = list(combinations(range(n), 2))
        unordered = sum(1 for i in range(len(E)) for j in range(i, len(E)) if not crossing_or_nesting(E[i], E[j]))
        print(n, 'ordered', ordered, 'unordered(multiset)', unordered, 'closed', binom(n, 2) ** 2 - 4 * binom(n, 4))
