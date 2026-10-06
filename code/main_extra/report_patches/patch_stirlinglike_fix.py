# -*- coding: utf-8 -*-
"""2026-10-07 修正 T3.9(3) 的陈述：三个位移点必须两两不同（否则系数可以相消，T=0 当然零化 U）。

主 Agent 写论文初稿时复查发现。Kauers 的三项生成元的位移点是 (0,0)、(v_1,v_2)、(w_1,w_2)，|det|=1 保证两两不同，
所以「U 不是 Stirling-like」的结论不变；Lean 定理 `not_mem_relU_of_support_subset` 本来就要求 r≠0，不受影响。
用法：py -3.14 code/main_extra/report_patches/patch_stirlinglike_fix.py [--dry]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
PARTS = os.path.join(ROOT, 'notes', 'report_parts')
DRY = '--dry' in sys.argv
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

name = '04_C3.md'
path = os.path.join(PARTS, name)
t = open(path, encoding='utf-8').read()
fixes = [
    ('(3) 推论：设 T=Σ_{i=0}^{2}c_i(k,m)S^{(s_i,t_i)}（S^{(s,t)}: f(k,m)↦f(k+s,m+t)，(s_i,t_i)∈Z²，c_i 为不全为 0 的有理函数），三个位移点的 |det|≤2，',
     '(3) 推论：设 T=Σ_{i=0}^{2}c_i(k,m)S^{(s_i,t_i)}（S^{(s,t)}: f(k,m)↦f(k+s,m+t)，三个位移点 (s_i,t_i)∈Z² 两两不同，c_i 为不全为 0 的有理函数），|det|≤2，'),
    ('R=D·R′ 在整个象限上零化 U，R≠0，支撑是原位移点经 (s,t)↦(c−s,d−t) 的像，|det| 不变，与 (2) 矛盾。∎ ',
     'R=D·R′ 在整个象限上零化 U；三个点 (c−s_i,d−t_i) 两两不同，所以 R 的正规形系数就是 D·n_i，不全为 0，R≠0，支撑是原位移点经 (s,t)↦(c−s,d−t) 的像，|det| 不变，与 (2) 矛盾。'
     '（「两两不同」不能省：位移点重合时系数可以相消，T=0。Kauers 生成元的位移点 (0,0)、(v_1,v_2)、(w_1,w_2) 因 |det|=1 自动两两不同。）∎ '),
]
for old, new in fixes:
    n = t.count(old)
    assert n == 1, '锚点出现 %d 次：%s' % (n, old[:50])
    t = t.replace(old, new)
if DRY:
    print('would patch', name)
else:
    with open(path, 'w', encoding='utf-8') as f:
        f.write(t)
    print('patched', name)
