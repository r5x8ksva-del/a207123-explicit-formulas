# -*- coding: utf-8 -*-
"""verify-math-c3 / v0：逐字核对 9 条发现的原文引用能否在 04_C3.md 中精确找到（只读）。"""
import os

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
path = os.path.join(ROOT, 'notes', 'report_parts', '04_C3.md')
txt = open(path, encoding='utf-8').read()
rep = open(os.path.join(ROOT, '报告.md'), encoding='utf-8').read()

quotes = {
    0: 'D-finite（等价于 Lipshitz 意义的 P-recursive）要求**每个方向**都有这样的递推',
    1: 'c3b 探索脚本用第二个素数 2147483629 跑的是另一批 k-only 参数（不是同一批参数的复跑）',
    2: '严格尾项界 |尾项|≤3.5·10^{−118}',
    3: '非负幂等于按 s 细化 DP 的完整序列数',
    4: '并且 1<K/Γ(−λ)<2、x→0+ 时趋于 2，整体差值夹在常数项差值的 1 倍与 2 倍之间。',
    5: '𝒮(x,t):=Σ_m t^m G_m(x)（G_m 取有理函数值；用 𝒮 以免与 Stirling 数 S 混淆）',
    6: 'R≠0 时 (R∂_x−R_x)𝓛 是非零算子（整环）且零化 F，与 (1) 矛盾',
    7: '参数 β∈Q(x)（如 β=j+1−λ）时各 (β)_n≠0',
    8: 'T2.2 的第二个独立证明',
}
for i, q in quotes.items():
    print('#%d in 04_C3.md: count=%d ; in 报告.md: count=%d' % (i, txt.count(q), rep.count(q)))
