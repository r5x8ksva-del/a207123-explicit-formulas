# -*- coding: utf-8 -*-
"""Dry-run (in memory only) of the proposed replacements; prints the resulting sentences."""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
PARTS = os.path.join(ROOT, 'notes', 'report_parts')

fixes = [
    (0, '03_C2.md',
     '其余奇数形状【已验证（数值，浮点纤维检验 α≥1、α+β≤12，只有 (2,1) 不能由纤维法排除，而它正是定理 S 的形状；不在 verify_all 中，见 notes/review/r-c2a-review.md §4.3）】',
     '其余奇数形状【猜想（只有浮点数值证据，不是精确核对：纤维检验 α≥1、α+β≤12、容差 1e−7，未做区间算术；只有 (2,1) 不能由纤维法排除，而它正是定理 S 的形状；不在 verify_all 中，见 notes/review/r-c2a-review.md §4.3 与 logs/review_r-c2a_r4_negative.log）】'),
    (1, '03_C2.md',
     '主 Agent 与审计者共 6 次运行的范围：F4 最快，H、F3 最慢；见 logs/c2a_e5_bench_K200_M30.log 与各次 verify_all 日志的 c2a.bench_k200_m30 行；复核者机器负载高时整体慢约 3 倍',
     'c2a 作者 2 次（logs/c2a_e5_bench_K200_M30.log、logs/c2a_check_run.log）、复核者 x2 1 次（logs/review_x2-dfinite_check_c2a_run.log）、主 Agent 2 次（logs/verify_all_run1.log、logs/verify_all_final.log）、审计者 a3 1 次（logs/audit_a3-requirements_verify_rerun.log）共 6 次正常负载运行的范围：F4 最快，H、F3 最慢；除 e5 日志外见各日志的 bench_k200_m30 行；复核者 r-c2a、x1 运行时机器负载高，同项耗时约为同一脚本正常运行的 3–5 倍'),
    (2, '03_C2.md',
     '要用 k≤60 才全部被反驳（复核者 r-c2b，logs/review_r-c2b_r4b_full.log，不在 verify_all 中；verify_all 只复现 E m=3、U m=2）',
     '改用 k≤60 的数据后全部被反驳（复核者 r-c2b：k≤30 全量重跑见 logs/review_r-c2b_r4b_full.log（E m=5,6；U m=4,5,6）与 logs/review_r-c2b_r4b_full_small.log（E m=3,4；U m=2,3），k≤60 的反驳见 logs/review_r-c2b_r4b_k60.log；不在 verify_all 中；verify_all 只复现 E m=3、U m=2）'),
    (3, '03_C2.md',
     'x⁵−v_0(1−x)³）在实轴上都严格单调',
     'x⁵−v_0(1−x)³，此时 v_0=v(ξ)=ξ^{−4}≈4.61）在实轴上都严格单调'),
    (4, '02_C1.md',
     'ρ_m 为 y³=y²+m 的实根，x_m=1/ρ_m',
     'ρ_m 为 y³=y²+m 的最大实根（m≥1 时是唯一实根；ρ_0=1），x_m=1/ρ_m'),
]
for i, fn, old, new in fixes:
    t = open(os.path.join(PARTS, fn), encoding='utf-8').read()
    assert t.count(old) == 1, (i, t.count(old))
    t2 = t.replace(old, new)
    p = t2.index(new)
    a = max(0, p - 80); b = min(len(t2), p + len(new) + 60)
    print('#%d %s -> ...%s...' % (i, fn, t2[a:b].replace('\n', ' ')))
    for path in ['logs/review_r-c2a_r4_negative.log', 'logs/c2a_e5_bench_K200_M30.log', 'logs/c2a_check_run.log',
                 'logs/review_x2-dfinite_check_c2a_run.log', 'logs/verify_all_run1.log', 'logs/verify_all_final.log',
                 'logs/audit_a3-requirements_verify_rerun.log', 'logs/review_r-c2b_r4b_full.log',
                 'logs/review_r-c2b_r4b_full_small.log', 'logs/review_r-c2b_r4b_k60.log']:
        if path in new:
            assert os.path.exists(os.path.join(ROOT, path)), path
print('all referenced log paths exist; no file was written')
