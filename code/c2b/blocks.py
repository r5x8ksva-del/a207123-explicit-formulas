# -*- coding: utf-8 -*-
"""c2b 探索工具：块分解（只按三元组条件判定合法性，不调用 core 的任何计数函数）。

块的表示：
  ('S', v)      单块 [v]
  ('T', v, a)   三块 [a, v, v]，0 <= a < v
  ('E', v, a)   截断块 [a, v]，0 <= a < v，只能是最后一块
块词：块的有限序列，层次（level = v）从左到右非增，E 只能出现在最后。
"""
import sys


def good3(a, b, c):
    """原始三元组条件（任务说明第 1 节 (b)）：b == c 或 a >= max(b, c)。"""
    return b == c or (a >= b and a >= c)


def is_legal(h):
    return all(good3(h[i], h[i + 1], h[i + 2]) for i in range(len(h) - 2))


def dfs_legal(k, m):
    """按三元组条件 DFS 枚举 {0..m}^k 中全部合法序列（元组）。"""
    out = []
    seq = []

    def rec():
        if len(seq) == k:
            out.append(tuple(seq))
            return
        for v in range(m + 1):
            if len(seq) >= 2 and not good3(seq[-2], seq[-1], v):
                continue
            seq.append(v)
            rec()
            seq.pop()

    rec()
    return out


def block_values(b):
    if b[0] == 'S':
        return [b[1]]
    if b[0] == 'T':
        return [b[2], b[1], b[1]]
    return [b[2], b[1]]


def concat(blocks):
    out = []
    for b in blocks:
        out.extend(block_values(b))
    return tuple(out)


def parse_det(h):
    """证明里的确定性解析：首块层次 = max(剩余部分)；首项 = max 则为 S，否则看剩余长度取 T 或 E。
    某一步不满足块的形状则返回 None（只对合法序列保证成功）。"""
    h = list(h)
    blocks = []
    p = 0
    n = len(h)
    while p < n:
        M = max(h[p:])
        if h[p] == M:
            blocks.append(('S', M))
            p += 1
        elif n - p == 2:
            if h[p + 1] != M:
                return None
            blocks.append(('E', M, h[p]))
            p += 2
        else:
            if not (h[p + 1] == M and h[p + 2] == M):
                return None
            blocks.append(('T', M, h[p]))
            p += 3
    return blocks


def is_block_word(blocks, m):
    """块词定义：层次 <= m、非增、E 只在最后、0 <= a < v。"""
    prev = m
    for i, b in enumerate(blocks):
        v = b[1]
        if v > prev or v < 0:
            return False
        if b[0] in ('T', 'E') and not (0 <= b[2] < v):
            return False
        if b[0] == 'E' and i != len(blocks) - 1:
            return False
        prev = v
    return True


def count_parses(h, m):
    """非确定性解析计数：把 h 写成块词（层次 <= m）的方式数。不使用合法性判定。"""
    n = len(h)
    memo = {}

    def f(p, top):
        if p == n:
            return 1
        key = (p, top)
        if key in memo:
            return memo[key]
        tot = 0
        x = h[p]
        if x <= top:                                        # S 块
            tot += f(p + 1, x)
        if p + 3 <= n and x < h[p + 1] == h[p + 2] <= top:  # T 块 [a,v,v]
            tot += f(p + 3, h[p + 1])
        if p + 2 == n and x < h[p + 1] <= top:              # E 块 [a,v]，恰为最后两项
            tot += 1
        memo[key] = tot
        return tot

    return f(0, m)


def gen_block_words(k, m):
    """生成全部总长为 k、层次 <= m 的块词（不做任何合法性判定）。"""
    out = []
    cur = []

    def rec(rem, top):
        if rem == 0:
            out.append(list(cur))
            return
        for v in range(top, -1, -1):
            cur.append(('S', v))
            rec(rem - 1, v)
            cur.pop()
            if rem >= 3:
                for a in range(v):
                    cur.append(('T', v, a))
                    rec(rem - 3, v)
                    cur.pop()
            if rem == 2:
                for a in range(v):
                    out.append(list(cur) + [('E', v, a)])

    rec(k, m)
    return out


def ascents(h):
    return sum(1 for i in range(len(h) - 1) if h[i] < h[i + 1])


def all_sequences_parse_check(K, m):
    """对 {0..m}^k（1<=k<=K）的全部序列检查：parse 计数 == [合法]。
    从右往左前置元素构造全部后缀；携带 V0=vec(s), V1=vec(s[1:]), V2=vec(s[2:])，
    vec(s)[top] = s 写成层次 <= top 的块词的方式数。返回 (检查的序列数, 失败列表)。"""
    sys.setrecursionlimit(10000)
    fails = []
    cnt = [0]
    ones = [1] * (m + 1)
    rng = range(m + 1)

    def rec(s, legal, V0, V1, V2):
        n = len(s)
        if n >= 1:
            cnt[0] += 1
            if V0[m] != (1 if legal else 0):
                fails.append(s)
        if n == K:
            return
        for x in rng:
            lg = legal and (n < 2 or good3(x, s[0], s[1]))
            newV = [0] * (m + 1)
            tcase = n >= 2 and x < s[0] == s[1]
            ecase = n == 1 and x < s[0]
            for top in rng:
                t = V0[x] if x <= top else 0                 # S 块：剩余 s，上限 x
                if tcase and s[0] <= top:
                    t += V2[s[0]]                            # T 块：剩余 s[2:]，上限 v=s[0]
                if ecase and s[0] <= top:
                    t += 1                                   # E 块
                newV[top] = t
            rec((x,) + s, lg, newV, V0, V1)

    rec((), True, ones, None, None)
    return cnt[0], fails
