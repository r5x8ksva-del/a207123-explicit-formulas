# -*- coding: utf-8 -*-
"""Lean 形式化第四轮收尾（2026-10-07）核对 HStruct.lean 的陈述时发现的报告缺条件，按用户 2026-10-05 的授权补上
（「只缺约定或适用范围、结论本身不变、notes/ 写法与 Lean 一致」时直接补并最后统一列出）。

T5.3(1)：h_k^{(d)}(1) 的公式与 N 行多项式 n_k(z)=(1+z)^{k−1}h_k(z/(1+z)) 都要求 k≥1。它们由
h_k=Σ_qN(k,q)t^{q−1}(1−t)^{k−q} 推出，而 notes/c5a.md §4.1-1 写明这个表示只对 k≥1 成立（h_0=1 单列）。
k=0 时 h_0'(1)=0，导数公式右边却是 −1（Lean：`A207123.iterate_derivative_hpoly_eval_one_k_zero`；k≥1 的公式是
`iterate_derivative_hpoly_eval_one`）；n_0 按定义是 z^{−1}，不是多项式（Lean 的 `nrowPoly`、`nrowPoly_eval` 只对 k≥1 陈述）。

结论本身不变，只补适用范围。用法：py -3.14 code/main_extra/report_patches/patch_lean4_fixes3.py，
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


OLD = (r"h_k^{(d)}(1)=d!Σ_{e≤d}(−1)^eC(k−1−e,d−e)N(k,k−e)，例如 h_k'(1)=−(k²−3k−2)（k≥4）；"
       r"N 行多项式 n_k(z):=Σ_qN(k,q)z^{q−1}=(1+z)^{k−1}h_k(z/(1+z))。")
NEW = (r"h_k^{(d)}(1)=d!Σ_{e≤d}(−1)^eC(k−1−e,d−e)N(k,k−e)（k≥1），例如 h_k'(1)=−(k²−3k−2)（k≥4）；"
       r"N 行多项式 n_k(z):=Σ_qN(k,q)z^{q−1}=(1+z)^{k−1}h_k(z/(1+z))（k≥1）。"
       r"（这两处都要求 k≥1：它们由 h_k=Σ_qN(k,q)t^{q−1}(1−t)^{k−q} 推出，而这个表示只对 k≥1 成立；"
       r"k=0 时 h_0=1，h_0'(1)=0，导数公式右边却是 −1，n_0 则是 z^{−1}，不是多项式。"
       r"第一版报告漏写 k≥1，Lean 形式化第四轮收尾时发现后补上。）")
patch(P + '06_C5.md', [(OLD, NEW)])
print('done')
