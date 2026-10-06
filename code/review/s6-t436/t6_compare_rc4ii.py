# -*- coding: utf-8 -*-
"""t6：把 r-c4ii 日志 logs/review_r-c4ii_r6_structure.log 中列出的 π_{j,i}（j=9..14，升幂系数）
与 s6-t436 构造法的结果逐多项式比较。只读取那份日志，不改动它。
（在 s6-t436 的证明与 t1–t4 完成之后才写。）"""
import sys
sys.dont_write_bytecode = True
import ast
from fractions import Fraction
from math import factorial
import s6lib as L

path = 'logs/review_r-c4ii_r6_structure.log'
theirs = {}
with open(path, encoding='utf-8') as fh:
    for line in fh:
        line = line.strip()
        if line.startswith('# j=') and '：' in line:
            head, body = line.split('：', 1)
            j = int(head[len('# j='):])
            d = ast.literal_eval(body)
            theirs[j] = {int(i): L.tp_trim([Fraction(s) for s in coeffs]) for i, coeffs in d.items()}
print('从 r-c4ii 日志读到的 j：', sorted(theirs))
Jmax = max(theirs)
P = L.P_family(Jmax)
ok = True
for j in sorted(theirs):
    K = j // 2 + 1
    p, _, _ = L.decompose(P[j], K)
    mine = {i: L.tp_trim(L.tp_scale(p[i], factorial(i))) for i in range(1, K + 1)}
    mine = {i: v for i, v in mine.items() if v}
    th = {i: v for i, v in theirs[j].items() if v}
    same = (mine == th)
    ok = ok and same
    print('   j=%d：%s' % (j, '逐多项式相同' if same else '不同'))
    if not same:
        print('      mine  =', mine)
        print('      theirs=', th)
print('[%s] r-c4ii 日志中的 π_{j,i}（j=%s）与 s6-t436 构造法相同' % ('OK ' if ok else 'BAD', ','.join(map(str, sorted(theirs)))))
print('ALL_OK' if ok else 'SOME_BAD')
