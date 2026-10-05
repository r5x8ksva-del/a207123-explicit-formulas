# -*- coding: utf-8 -*-
import os
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
Q = [
 ('03_C2.md', '要用 k≤60 才全部被反驳（复核者 r-c2b，logs/review_r-c2b_r4b_full.log，不在 verify_all 中；verify_all 只复现 E m=3、U m=2）'),
 ('03_C2.md', '主 Agent 与审计者共 6 次运行的范围：F4 最快，H、F3 最慢；见 logs/c2a_e5_bench_K200_M30.log 与各次 verify_all 日志的 c2a.bench_k200_m30 行；复核者机器负载高时整体慢约 3 倍'),
 ('03_C2.md', 'x⁵−v_0(1−x)³）在实轴上都严格单调'),
 ('03_C2.md', '其余奇数形状【已验证（数值，浮点纤维检验 α≥1、α+β≤12，只有 (2,1) 不能由纤维法排除，而它正是定理 S 的形状；不在 verify_all 中，见 notes/review/r-c2a-review.md §4.3）】'),
 ('02_C1.md', 'ρ_m 为 y³=y²+m 的实根，x_m=1/ρ_m'),
 ('02_C1.md', '收敛半径 1/ρ_{m−1}>x_m'),
]
for f, q in Q:
    t = open(os.path.join(ROOT, 'notes', 'report_parts', f), encoding='utf-8').read()
    print(f, t.count(q), q[:40])
    r = open(os.path.join(ROOT, '报告.md'), encoding='utf-8').read()
    print('   in 报告.md:', r.count(q))
