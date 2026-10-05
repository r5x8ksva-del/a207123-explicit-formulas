# -*- coding: utf-8 -*-
"""最终一次 verify_all（2026-10-05，机器另有会话占用 CPU）之后同步：⑤ 结果表、运行时长、T2.9 计时出处、日期。"""
import re
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = ROOT + r'\notes\report_parts' + '\\'


def patch(path, pairs):
    s = open(path, encoding='utf-8').read()
    for a, b in pairs:
        n = s.count(a)
        assert n == 1, (path[-24:], a[:90], n)
        s = s.replace(a, b)
    open(path, 'w', encoding='utf-8').write(s)
    print('patched', path[-28:], len(pairs))


log = open(ROOT + r'\logs\verify_all_final.log', encoding='utf-8').read()
i = log.index('area     pass')
j = log.index('OVERALL', i)
j = log.index('\n', j) if '\n' in log[j:] else len(log)
table = log[i:j].rstrip()
assert 'TOTAL pass=290 fail=0 modules=11' in table and 'OVERALL: PASS' in table

s = open(P + '09_code.md', encoding='utf-8').read()
s2, n = re.subn(r"```\narea     pass.*?OVERALL: \w+\n```", lambda m: "```\n" + table + "\n```", s, flags=re.S)
assert n == 1
open(P + '09_code.md', 'w', encoding='utf-8').write(s2)
print('09_code table replaced')

patch(P + '09_code.md', [
(r"**最终一次运行**（2026-10-04，完整输出 `logs/verify_all_final.log`）：",
 r"**最终一次运行**（2026-10-05，完整输出 `logs/verify_all_final.log`；这次运行时本机另有一个会话在跑基准测试，耗时约为空闲时（此前几次全量运行为 216–232 s）的 3 倍，检查结果不受影响）："),
])

patch(P + '00_head.md', [
(r"- 日期：2026-10-04。",
 r"- 日期：2026-10-04（最终核对完成于 2026-10-05）。"),
(r"运行 `py -3.14 verify_all.py`，约 3–4 分钟，共 11 个模块。",
 r"运行 `py -3.14 verify_all.py`，空闲时约 3.5–4 分钟（机器负载高时更长），共 11 个模块。"),
])

patch(ROOT + r'\README.md', [
(r"（约 3–4 分钟；需要 numpy，rv2 模块没有纯 Python 回退）",
 r"（空闲时约 3.5–4 分钟，机器负载高时更长；需要 numpy，rv2 模块没有纯 Python 回退）"),
])

patch(P + '03_C2.md', [
(r"c2a 作者 2 次（logs/c2a_e5_bench_K200_M30.log、logs/c2a_check_run.log）、复核者 x2 1 次（logs/review_x2-dfinite_check_c2a_run.log）、主 Agent 2 次（logs/verify_all_run1.log、logs/verify_all_final.log）、审计者 a3 1 次（logs/audit_a3-requirements_verify_rerun.log），共 6 次正常负载运行的范围：F4 最快，H、F3 最慢；除 e5 日志外见各日志的 bench_k200_m30 行；",
 r"c2a 作者 2 次（logs/c2a_e5_bench_K200_M30.log、logs/c2a_check_run.log）、复核者 x2 1 次（logs/review_x2-dfinite_check_c2a_run.log）、主 Agent 1 次（logs/verify_all_run1.log）、审计者 a3 1 次（logs/audit_a3-requirements_verify_rerun.log），共 5 次正常负载运行的范围（实测 0.227–2.405 s，与引理 1 之比 114–1202）：F4 最快，H、F3 最慢；除 e5 日志外见各日志的 bench_k200_m30 行。logs/verify_all_final.log 中的同一行随每次重跑覆盖、计时随机器负载变化，不计入这个范围（最终一次运行时另有会话占用 CPU，H 型约 10 s）；"),
])
