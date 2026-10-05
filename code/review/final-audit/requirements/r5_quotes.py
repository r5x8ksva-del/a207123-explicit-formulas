# -*- coding: utf-8 -*-
"""最终审计（requirements）r5：核对本方向每条发现的「原文引用」是否为对应 report_parts 文件中可精确找到的子串（只读）。"""
import os, sys
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
P = os.path.join(ROOT, 'notes', 'report_parts')
Q = [
 ('00_head.md', '只依赖 Python 标准库；装有 numpy 时 c3b 与 rv2 会用它加速模素数运算。'),
 ('03_C2.md', '其余奇数形状【已验证（数值，浮点纤维检验 α≥1、α+β≤12，只有 (2,1) 不能由纤维法排除，而它正是定理 S 的形状；不在 verify_all 中，见 notes/review/r-c2a-review.md §4.3）】'),
 ('06_C5.md', '(6)【已验证】k≥5 没有类似对应：U_5、U_6、U_7 从 m=0,1,2 起的 8 项窗口全部无结果'),
 ('06_C5.md', '(5) 提示词「m=2、3 在 k=40 时相差 <0.4%」只在「相邻比 U_41/U_40 与 ρ_m 比较」的解释下成立'),
 ('10_uncertain.md', '数据上 22 个盒子（verify_all）加上复核者新增的盒子全部吻合'),
 ('00_head.md', '少数扩展范围只由第二轮复核脚本跑过，已在相应条目注明「不在 verify_all 中」并给出日志路径。'),
 ('09_code.md', '**11 个核对模块**（每个都从 `code/core.py` 的原始定义程序取「真值」）'),
 ('05_C4.md', '(5)【已证明，一切 j】低次系数 [x^{q+j}]Num_q 在 q≥j+2 时是 q 的 2j 次多项式'),
 ('05_C4.md', '(7)【已证明】反转分子 R_q(y)=y^{3q−2}Num_q(1/y) 的指数母函数有闭式'),
 ('06_C5.md', '(5)【已证明】h_k 在 [0,1] 上无根；每个固定位置的系数 h_{k,i} 最终为正（~c_iρ_i^k）；对固定 t∈(0,1)，Σ_k h_k(t)z^k 的收敛半径为 0。'),
 ('04_C3.md', 'c3b.C3B-RES（留数非零）'),
 ('06_C5.md', '核对：c5b.col-data、c5b.col-direct、c5b.table、c5b.examples'),
 ('06_C5.md', 'Q_3 与 P_3 不同构但链数同为 (1,4,2)'),
 ('06_C5.md', '命中的只有 c_2=A077949、c_3=A084386'),
 ('06_C5.md', '可写成 c_j 的形式'),
 ('02_C1.md', '{C(x+1,q)} 是 Q[x] 的基'),
 ('03_C2.md', '要用 k≤60 才全部被反驳（复核者 r-c2b，logs/review_r-c2b_r4b_full.log，不在 verify_all 中；verify_all 只复现 E m=3、U m=2）'),
 ('10_uncertain.md', '核对扩到 k≤60、m≤20（多处更远）'),
 ('01_summary.md', '核对扩到 k≤60、m≤20。'),
 ('01_summary.md', 'k≥5 没有对应'),
 ('06_C5.md', '而且 k≥5 在 OEIS 中没有任何对应'),
 ('08_failed.md', 'k≥5 在 OEIS 中没有对应'),
 ('10_uncertain.md', 'k≥5（无对应）'),
 ('06_C5.md', 'c5a.c5a-prompt-k40、c0.c0-c4'),
]
bad = 0
for fn, q in Q:
    t = open(os.path.join(P, fn), encoding='utf-8').read()
    n = t.count(q)
    print('%-16s count=%d  %s' % (fn, n, q[:60]))
    bad += (n == 0)
print('missing quotes:', bad)
