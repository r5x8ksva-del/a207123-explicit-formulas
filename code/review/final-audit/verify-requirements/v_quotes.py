# -*- coding: utf-8 -*-
"""verify-requirements：逐条确认审计者引用的原文是对应 report_parts 文件中的精确子串（并统计出现次数）。"""
import os
import sys

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
PARTS = os.path.join(ROOT, 'notes', 'report_parts')

Q = [
    (0, '00_head.md', '只依赖 Python 标准库；装有 numpy 时 c3b 与 rv2 会用它加速模素数运算。'),
    (1, '03_C2.md', '其余奇数形状【已验证（数值，浮点纤维检验 α≥1、α+β≤12，只有 (2,1) 不能由纤维法排除，而它正是定理 S 的形状；不在 verify_all 中，见 notes/review/r-c2a-review.md §4.3）】'),
    (2, '06_C5.md', '(6)【已验证】k≥5 没有类似对应：U_5、U_6、U_7 从 m=0,1,2 起的 8 项窗口全部无结果'),
    (3, '06_C5.md', '(5) 提示词「m=2、3 在 k=40 时相差 <0.4%」只在「相邻比 U_41/U_40 与 ρ_m 比较」的解释下成立'),
    (4, '10_uncertain.md', '数据上 22 个盒子（verify_all）加上复核者新增的盒子全部吻合'),
    (5, '10_uncertain.md', '核对扩到 k≤60、m≤20（多处更远）'),
    (6, '00_head.md', '少数扩展范围只由第二轮复核脚本跑过，已在相应条目注明「不在 verify_all 中」并给出日志路径。'),
    (7, '03_C2.md', '要用 k≤60 才全部被反驳（复核者 r-c2b，logs/review_r-c2b_r4b_full.log，不在 verify_all 中；verify_all 只复现 E m=3、U m=2）'),
    (8, '09_code.md', '**11 个核对模块**（每个都从 `code/core.py` 的原始定义程序取「真值」）'),
    (9, '05_C4.md', '(5)【已证明，一切 j】低次系数 [x^{q+j}]Num_q 在 q≥j+2 时是 q 的 2j 次多项式'),
    (10, '06_C5.md', '(5)【已证明】h_k 在 [0,1] 上无根；每个固定位置的系数 h_{k,i} 最终为正（~c_iρ_i^k）；对固定 t∈(0,1)，Σ_k h_k(t)z^k 的收敛半径为 0。'),
    (11, '04_C3.md', 'c3b.C3B-RES（留数非零）'),
    (12, '06_C5.md', '核对：c5b.col-data、c5b.col-direct、c5b.table、c5b.examples'),
    (13, '06_C5.md', 'Q_3 与 P_3 不同构但链数同为 (1,4,2)'),
    (14, '06_C5.md', '命中的只有 c_2=A077949、c_3=A084386'),
    (15, '02_C1.md', '{C(x+1,q)} 是 Q[x] 的基'),
]

print('== quote check: exact substring in notes/report_parts/<file>')
allok = True
for idx, fn, q in Q:
    with open(os.path.join(PARTS, fn), encoding='utf-8') as f:
        s = f.read()
    n = s.count(q)
    allok &= n >= 1
    print('#%-2d %-16s count=%d %s' % (idx, fn, n, 'OK' if n >= 1 else 'NOT FOUND'))
print('all quotes found:', allok)

# 附带：报告中 c5b.diag / c5b.rows / C3B-INT 是否被引用；P_3、Λ_3 的出现
cat = ''
for fn in sorted(os.listdir(PARTS)):
    with open(os.path.join(PARTS, fn), encoding='utf-8') as f:
        cat += f.read()
for tok in ('c5b.diag', 'c5b.rows', 'C3B-INT', 'P_3', 'Λ_3', 'Λ_k', 'C(x+1', 'C(y+1', 'review_r-c2b_r4b_k60', 'review_r-c2b_r4b_full_small',
            'review_r-c1_r3_C2_final', 'review_r-c1_r4_C3_C6_C7_final', 'review_r-c3b_r2_rank', 'review_x2-dfinite_kernel',
            'review_r-c5b_negzeros_exact', 'notes/c4.md §4.7', 'notes/c4.md §4.9', 'notes/c5a.md §4'):
    print('token %-34s occurrences in report_parts: %d' % (tok, cat.count(tok)))
