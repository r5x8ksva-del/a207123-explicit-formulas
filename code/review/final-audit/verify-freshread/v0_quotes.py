# -*- coding: utf-8 -*-
"""verify-freshread: 逐条确认待复核发现的原文引用能否在当前 report_parts 中精确找到。只读。"""
ROOT = 'C:/Users/Michael Song/Desktop/私人办公/A207123-任务C-显式公式与母函数'
P = ROOT + '/notes/report_parts/'
Q = [
 (0, '01_summary.md', '（例外：N(k,q) 的组合意义按定义直接计数只核到 k≤9，复核者用独立 DP 到 k≤28）'),
 (1, '08_failed.md', '（对 m=5,6 需要 k≤60）'),
 (2, '09_code.md', 'TOTAL pass=290 fail=0 modules=11 failed_modules=-  (217.7s)'),
 (3, '03_C2.md', '各显式公式约 0.2–2.4 s'),
 (4, '00_head.md', '另做了三轮多 Agent 工作流'),
 (5, '00_head.md', '少数扩展范围只由第二轮复核脚本跑过，都不在 verify_all 中；已在相应条目注明并给出日志路径。'),
 (6, '06_C5.md', '核对：c5a.c5a-roots、c5a.c5a-binet（Lagrange 形式 m≤20、k≤60 精确相等）、c5a.c5a-filter（单独抽出 b_m 的极点分量，1≤m≤20）、c5a.c5a-cm-form、c5a.c5a-cm-repr、'),
 (7, '06_C5.md', '(1)【已证明】基本事实：h_k(0)=1，h_k(1)=2（k≥2）'),
 (8, '04_C3.md', '维数公式的计数：U 的情形看角点 (α′,β*+1) 与 (α*+3,β′)；N 的情形必须取 β′=max{b:q_{α*b}≠0}'),
 (9, '01_summary.md', '全部多项式系数象限递推恰为引理 1 算子生成的左理想。'),
 (10, '03_C2.md', '在 k≤30 上 m=5,6 各有 59/1024 个「零检验」形状对'),
 (11, '03_C2.md', '形状 Σ_s A(m,s)C(k+αm+β−γs, δm+εs+ζ)（γ+ε≥2 的 8232 族）'),
 (12, '06_C5.md', '列方向 (E²−1)^{2k+1} 零化 a_k(n)，所以有限个初值核对即足够；行方向由 (m_1+1)²(m_2+1)² 阶转移矩阵给出先验阶界'),
 (13, '08_failed.md', '另有子 Agent 为查 Lipshitz 1989 读了几次文献元数据（Crossref、Semantic Scholar API、ar5iv、Wikipedia；ScienceDirect 返回 403）'),
]
print('== quote counts in report_parts ==')
for i, f, q in Q:
    s = open(P + f, encoding='utf-8').read()
    print(f'#{i} {f} count={s.count(q)}')
rep = open(ROOT + '/报告.md', encoding='utf-8').read()
print('== quote counts in 报告.md ==')
for i, f, q in Q:
    print(f'#{i} 报告.md count={rep.count(q)}')
# 报告.md 是否等于各节拼接（判断成品与 report_parts 同步）
import os
parts = sorted(x for x in os.listdir(P) if x.endswith('.md'))
cat = ''.join(open(P + x, encoding='utf-8').read() for x in parts)
cat2 = '\n'.join(open(P + x, encoding='utf-8').read() for x in parts)
cat3 = '\n\n'.join(open(P + x, encoding='utf-8').read().rstrip('\n') for x in parts)
print('报告.md len', len(rep), 'concat lens', len(cat), len(cat2), len(cat3))
print('equal(concat)?', rep == cat, rep == cat2, rep.rstrip() == cat3.rstrip())
