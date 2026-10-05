# -*- coding: utf-8 -*-
"""核对本方向发现里引用的原文都能在 report_parts 中精确找到（final-audit math-c4c5）。"""
import os
from alib import say, check, ROOT, write_log

QUOTES = [
    ('05_C4.md', '一般的 M(d;σ,β) 没有闭式（见 ④A.5）'),
    ('05_C4.md', 'S(k,k−d)=Σ_j S_2(d+j,j)C(k,d+j) 的对应物'),
    ('05_C4.md', '不存在二阶 Euler 型非负展开'),
    ('05_C4.md', '门槛以下例外值（d+1≤k≤2d+1）全部列在 notes/c4.md 表 2'),
    ('06_C5.md', '旧极点（σ 来自 j<m）的留数满足 α_m(σ)=α_{m−1}(σ)·(−σ³)/(m−j)'),
    ('06_C5.md', '可写成 c_j 的形式'),
    ('06_C5.md', '等价地 U_k(m)=(2/k!)(m+μ_k)^k(1+O(m^{−2}))，μ_k=(k²−2k−1)/2；在 C(m+1,·) 基下 U_k=2C(m+1,k)+(k²−k−4)C(m+1,k−1)+p_2(k)C(m+1,k−2)+…'),
    ('06_C5.md', 'ẽ_j(n)=e_j(−1,0,…,n−2)/n^{\\underline j}'),
    ('06_C5.md', 'Q_3 与 P_3 不同构'),
]
ok = True
for fn, q in QUOTES:
    txt = open(os.path.join(ROOT, 'notes', 'report_parts', fn), encoding='utf-8').read()
    full = open(os.path.join(ROOT, '报告.md'), encoding='utf-8').read()
    c1, c2 = txt.count(q), full.count(q)
    say('  %s count=%d (报告.md count=%d): %s' % (fn, c1, c2, q))
    if c1 != 1:
        ok = False
# 佐证：S_2 只在 05_C4.md 出现一次；e_j(、初等对称在报告中无定义；④A.5 原文为「没找到」
parts = {f: open(os.path.join(ROOT, 'notes', 'report_parts', f), encoding='utf-8').read()
         for f in os.listdir(os.path.join(ROOT, 'notes', 'report_parts')) if f.endswith('.md')}
s2 = sum(t.count('S_2') for t in parts.values())
ej = sum(t.count('初等对称') for t in parts.values())
a5 = '都没找到' in parts['08_failed.md'] and '未完成：一般 M(d;σ,β) 的闭式' in parts['10_uncertain.md']
lam = 'Λ_k' in parts['06_C5.md'] and 'P_m=∏_{i=0}^{m} b_i' in parts['02_C1.md']
check('quotes', ok and s2 == 1 and ej == 0 and a5 and lam,
      '9 条引用在各自文件中恰出现 1 次；S_2 全文只出现 %d 次且无定义；「初等对称」出现 %d 次；④A.5 写「都没找到」、⑥ 写「未完成」；Λ_k 与 P_m 的全局记号存在' % (s2, ej))
write_log('final_audit_math-c4c5_s11.log')
