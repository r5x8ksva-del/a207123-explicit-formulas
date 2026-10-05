# -*- coding: utf-8 -*-
"""Lean 形式化第四轮（2026-10-05）发现的第二处报告缺条件，按用户同意补上。

T1.9：「deg q=2k−2」「g.f. 最简分母恰为 (1−x)^{2k+1}(1+x)^{2k−1}」「最小递推阶 4k」都要求 k≥1。
k=0 时 a_0(n)≡1，q=0，Σ a_0(n)x^n = 1/(1−x)，最小递推阶为 1 而不是 4k=0
（Lean：`A207123.parity_min_order_zero`；k≥1 的结论见 `A207123.T1_9`、`parity_min_order`）。

结论本身不变，只补适用范围。用法：py -3.14 code/main_extra/report_patches/patch_lean4_fixes2.py，
然后运行 code/main_extra/assemble_report.py 重新拼接报告。每处替换都断言原文恰好出现一次。
"""
import sys

ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = ROOT + r'\notes\report_parts' + '\\'
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')


def patch(path, pairs):
    s = open(path, encoding='utf-8').read()
    for a, b in pairs:
        n = s.count(a)
        assert n == 1, (path[-24:], a[:90], n)
        s = s.replace(a, b)
    open(path, 'w', encoding='utf-8').write(s)
    print('patched', path[-28:], len(pairs))


OLD_A = r"得 deg q=2k−2（首项 c²k/(2·4^k)，c=lc u_k）"
NEW_A = r"得 deg q=2k−2（k≥1；首项 c²k/(2·4^k)，c=lc u_k）"
OLD_B = r"所以 g.f. 最简分母恰为 (1−x)^{2k+1}(1+x)^{2k−1}，最小递推阶 4k。"
NEW_B = (r"所以 g.f. 最简分母恰为 (1−x)^{2k+1}(1+x)^{2k−1}，最小递推阶 4k。"
         r"（这两条与 deg q=2k−2 都要求 k≥1：k=0 时 a_0≡1，q=0，母函数为 1/(1−x)，最小递推阶为 1 而不是 4k=0。"
         r"第一版报告漏写 k≥1，Lean 形式化第四轮发现后补上。）")
patch(P + '02_C1.md', [(OLD_A, NEW_A), (OLD_B, NEW_B)])
print('done')
