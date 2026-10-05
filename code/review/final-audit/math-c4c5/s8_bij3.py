# -*- coding: utf-8 -*-
"""T5.4(4)：U_3 的保值集双射（非增三元组不动；(a<b=c)->(a,a,b)；(b<c<=a)->(b,c,a)）与 Q_3/Λ_3 链数（final-audit math-c4c5）。"""
from itertools import product
from alib import say, check, write_log


def good(a, b, c):
    return b == c or (a >= b and a >= c)


ok = True
for m in range(0, 13):
    V = range(m + 1)
    legal = [t for t in product(V, repeat=3) if good(*t)]
    mono = set(t for t in product(V, repeat=3) if (t[0] <= t[1] <= t[2]) or (t[0] >= t[1] >= t[2]))
    img = []
    for (a, b, c) in legal:
        if a >= b >= c:
            img.append((a, b, c))
        elif a < b == c:
            img.append((a, a, b))
        elif b < c <= a:
            img.append((b, c, a))
        else:
            ok = False
    if len(set(img)) != len(img) or set(img) != mono:
        ok = False
    if any(set(x) != set(y) for x, y in zip(legal, img)):
        ok = False
# Λ_3 与 Q_3 的链数
rows = [r for r in product((0, 1), repeat=3) if r not in ((0, 0, 1), (0, 1, 0))]
le = lambda a, b: all(x <= y for x, y in zip(a, b))
bot, top = (0, 0, 0), (1, 1, 1)


def chains(elems, le, bot, top):
    cnt = {}
    def rec(x, length):
        if x == top:
            cnt[length] = cnt.get(length, 0) + 1
            return
        for y in elems:
            if y != x and le(x, y):
                rec(y, length + 1)
    rec(bot, 0)
    return [cnt.get(q, 0) for q in range(1, 4)]


cl = chains(rows, le, bot, top)
# Q_3：两条 4 元链首尾粘合
Q = ['0', 'a1', 'a2', 'b1', 'b2', '1']
rel = {('0', x) for x in Q} | {(x, '1') for x in Q} | {('a1', 'a2'), ('b1', 'b2')} | {(x, x) for x in Q}
cq = chains(Q, lambda x, y: (x, y) in rel, '0', '1')
check('T5.4.4-bij3', ok and cl == [1, 4, 2] and cq == [1, 4, 2] and len(rows) == 6,
      'U_3 的显式映射是「合法三元组 -> 单调三元组」的保值集双射（m<=12）；Λ_3（6 个允许行）与 Q_3 的 0̂->1̂ 链数都是 %s / %s' % (cl, cq))
write_log('final_audit_math-c4c5_s8.log')
