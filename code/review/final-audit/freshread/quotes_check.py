# -*- coding: utf-8 -*-
"""freshread：核对每条发现的原文引用是该 report_parts 文件当前内容里的精确子串（且唯一）。"""
import os, re
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = os.path.join(ROOT, 'notes', 'report_parts')

Q = [
    ('08_failed.md', '（对 m=5,6 需要 k≤60）'),
    ('01_summary.md', '（例外：N(k,q) 的组合意义按定义直接计数只核到 k≤9，复核者用独立 DP 到 k≤28）'),
    ('09_code.md', 'TOTAL pass=290 fail=0 modules=11 failed_modules=-  (217.7s)'),
    ('03_C2.md', '各显式公式约 0.2–2.4 s'),
    ('00_head.md', '另做了三轮多 Agent 工作流'),
    ('08_failed.md', '**B. 两轮工作中出过的错（都已更正，记在这里便于复核）**'),
    ('09_code.md', '两轮工作流的原始返回值：`logs/phase1_workflow_output.json`、`logs/phase2_review_output.json`'),
    ('06_C5.md', '核对：c5a.c5a-roots、c5a.c5a-binet（Lagrange 形式 m≤20、k≤60 精确相等）、c5a.c5a-filter（单独抽出 b_m 的极点分量，1≤m≤20）、c5a.c5a-cm-form、c5a.c5a-cm-repr、'),
    ('06_C5.md', '(1)【已证明】基本事实：h_k(0)=1，h_k(1)=2（k≥2）'),
    ('04_C3.md', '维数公式的计数：U 的情形看角点 (α′,β*+1) 与 (α*+3,β′)；N 的情形必须取 β′=max{b:q_{α*b}≠0}'),
    ('03_C2.md', '在 k≤30 上 m=5,6 各有 59/1024 个「零检验」形状对'),
    ('01_summary.md', '全部多项式系数象限递推恰为引理 1 算子生成的左理想。'),
    ('08_failed.md', '另有子 Agent 为查 Lipshitz 1989 读了几次文献元数据（Crossref、Semantic Scholar API、ar5iv、Wikipedia；ScienceDirect 返回 403）'),
    ('00_head.md', '另有子 Agent 对 Lipshitz 1989 做了几次文献元数据只读查询（见 ④C）'),
    ('02_C1.md', '扩展脚本另核对 a_direct 到 k=11'),
    ('05_C4.md', 'c4.c4-pattern-brute（按定义暴力枚举 d≤3；探索中 d=4）'),
    ('00_head.md', '少数扩展范围只由第二轮复核脚本跑过，都不在 verify_all 中；已在相应条目注明并给出日志路径。'),
    ('03_C2.md', '形状 Σ_s A(m,s)C(k+αm+β−γs, δm+εs+ζ)（γ+ε≥2 的 8232 族）'),
    ('06_C5.md', '列方向 (E²−1)^{2k+1} 零化 a_k(n)，所以有限个初值核对即足够；行方向由 (m_1+1)²(m_2+1)² 阶转移矩阵给出先验阶界'),
    ('03_C2.md', '(i)【已证明】命题 S′：形状 C(k+c−αs, βs+d)'),
]
ok_all = True
for fn, q in Q:
    t = open(os.path.join(P, fn), encoding='utf-8').read()
    n = t.count(q)
    ok_all &= (n == 1)
    print('%-14s count=%d  %s' % (fn, n, q[:60]))
print('ALL UNIQUE:', ok_all)

# 证据：重跑后的 verify_all_final.log 的总表与 bench 行
log = open(os.path.join(ROOT, 'logs', 'verify_all_final.log'), encoding='utf-8').read()
m = re.search(r'TOTAL pass=\d+ fail=\d+ modules=\d+ failed_modules=\S+\s+\(([\d.]+)s\)', log)
print('verify_all_final.log TOTAL secs =', m.group(1) if m else None)
b = re.search(r'PASS bench_k200_m30 .*', log)
print('bench line:', b.group(0)[-170:] if b else None)
for area in ('c0', 'c1', 'c2a', 'c2b', 'c3a', 'c3b', 'c4', 'c5a', 'c5b', 'rv', 'rv2'):
    mm = re.search(r'^%s\s+(\d+)\s+(\d+)\s+(\d+)\s+(\S+)\s+([\d.]+)\s+(\S+)$' % area, log, re.M)
    print('  table', area, mm.groups() if mm else None)
