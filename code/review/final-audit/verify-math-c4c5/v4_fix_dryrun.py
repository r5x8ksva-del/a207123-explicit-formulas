# -*- coding: utf-8 -*-
"""Dry run (no file is written): apply each proposed final_fix in memory and print the resulting sentence."""
import os
BASE = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
RP = os.path.join(BASE, 'notes', 'report_parts')
fixes = [
 (0, '05_C4.md', r'一般的 M(d;σ,β) 没有闭式（见 ④A.5）', r'一般的 M(d;σ,β) 的闭式尚未找到（见 ④A.5）'),
 (1, '05_C4.md', r'S(k,k−d)=Σ_j S_2(d+j,j)C(k,d+j) 的对应物', r'S(k,k−d)=Σ_j S_2(d+j,j)C(k,d+j)（S_2(n,j) 为把 n 元集分成 j 块且每块至少 2 个元素的相伴 Stirling 数）的对应物'),
 (2, '05_C4.md', r'不存在二阶 Euler 型非负展开', r'1≤d≤8 时不存在二阶 Euler 型非负展开'),
 (3, '05_C4.md', r'门槛以下例外值（d+1≤k≤2d+1）全部列在 notes/c4.md 表 2', r'd≤5 的门槛以下例外值（d+1≤k≤2d+1）列在 notes/c4.md 表 2，6≤d≤12 的列在 logs/c4_explore1.log（d≤12 时这些点全是例外由 c4.c4-pd-exceptions 核对）'),
 (4, '06_C5.md', r'等价地 U_k(m)=(2/k!)(m+μ_k)^k(1+O(m^{−2}))，μ_k=(k²−2k−1)/2；在 C(m+1,·) 基下 U_k=2C(m+1,k)+(k²−k−4)C(m+1,k−1)+p_2(k)C(m+1,k−2)+…', r'等价地（k≥4）U_k(m)=(2/k!)(m+μ_k)^k(1+O(m^{−2}))，μ_k=(k²−2k−1)/2；在 C(m+1,·) 基下（k≥6）U_k=2C(m+1,k)+(k²−k−4)C(m+1,k−1)+p_2(k)C(m+1,k−2)+…'),
 (5, '06_C5.md', r'旧极点（σ 来自 j<m）的留数满足 α_m(σ)=α_{m−1}(σ)·(−σ³)/(m−j)', r'旧极点（σ 来自 j<m）处的部分分式系数 α_m(σ)（G_m=Σ_σ α_m(σ)/(1−σx) 中 1/(1−σx) 的系数，不是留数）满足 α_m(σ)=α_{m−1}(σ)·(−σ³)/(m−j)'),
 (6, '06_C5.md', r'可写成 c_j 的形式', r'可写成序列 c_j(n)=[x^n]1/b_j 若干项的有理线性组合（这里的 c_j 是序列，不是 (2) 中的常数 c_m）'),
 (7, '06_C5.md', r'ẽ_j(n)=e_j(−1,0,…,n−2)/n^{\underline j}', r'ẽ_j(n)=e_j(−1,0,…,n−2)/n^{\underline j}（e_j 为 j 次初等对称多项式，与 T4.1 的缺陷 e_d 无关）'),
 (8, '06_C5.md', r'Q_3 与 P_3 不同构', r'Q_3 与 Λ_3（长 3 的允许行偏序集，T1.0(c)）不同构'),
]
for idx, f, old, new in fixes:
    t = open(os.path.join(RP, f), encoding='utf-8').read()
    assert t.count(old) == 1, idx
    t2 = t.replace(old, new, 1)
    j = t2.index(new)
    s = max(0, j - 60); e = min(len(t2), j + len(new) + 60)
    print(f'#{idx} {f}:\n   ...{t2[s:e]}...\n')
print('dry run only; no files written')
