# -*- coding: utf-8 -*-
"""Verifier step 0: check every quoted string exists exactly in the stated report_parts file,
and grep the report_parts for the notations at issue (S_2, alpha_m, c_j / c_m, e_j, P_3, Lambda)."""
import os, re, sys

BASE = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
RP = os.path.join(BASE, 'notes', 'report_parts')
files = sorted(f for f in os.listdir(RP) if f.endswith('.md'))
text = {f: open(os.path.join(RP, f), encoding='utf-8').read() for f in files}
report = open(os.path.join(BASE, '报告.md'), encoding='utf-8').read()

quotes = [
    (0, '05_C4.md', '一般的 M(d;σ,β) 没有闭式（见 ④A.5）'),
    (1, '05_C4.md', 'S(k,k−d)=Σ_j S_2(d+j,j)C(k,d+j) 的对应物'),
    (2, '05_C4.md', '不存在二阶 Euler 型非负展开'),
    (3, '05_C4.md', '门槛以下例外值（d+1≤k≤2d+1）全部列在 notes/c4.md 表 2'),
    (4, '06_C5.md', '等价地 U_k(m)=(2/k!)(m+μ_k)^k(1+O(m^{−2}))，μ_k=(k²−2k−1)/2；在 C(m+1,·) 基下 U_k=2C(m+1,k)+(k²−k−4)C(m+1,k−1)+p_2(k)C(m+1,k−2)+…'),
    (5, '06_C5.md', '旧极点（σ 来自 j<m）的留数满足 α_m(σ)=α_{m−1}(σ)·(−σ³)/(m−j)'),
    (6, '06_C5.md', '可写成 c_j 的形式'),
    (7, '06_C5.md', 'ẽ_j(n)=e_j(−1,0,…,n−2)/n^{\\underline j}'),
    (8, '06_C5.md', 'Q_3 与 P_3 不同构'),
]
print('== quote existence (count in stated file / count in assembled 报告.md) ==')
for idx, f, q in quotes:
    print(f'#{idx} {f}: in-file={text[f].count(q)}  in-report={report.count(q)}  ' + ('OK' if text[f].count(q) == 1 else 'CHECK'))

def grep(pat, label):
    print(f'\n== grep {label!r} (regex {pat!r}) ==')
    rx = re.compile(pat)
    tot = 0
    for f in files:
        for ln, line in enumerate(text[f].splitlines(), 1):
            for mt in rx.finditer(line):
                tot += 1
                s = max(0, mt.start() - 40); e = min(len(line), mt.end() + 40)
                print(f'  {f}:{ln}: ...{line[s:e]}...')
    print(f'  total matches: {tot}')

grep(r'S_2|S₂|S_\{2\}', 'S_2')
grep(r'相伴|每块至少', 'associated Stirling wording')
grep(r'α_', 'alpha_')
grep(r'留数', 'residue word')
grep(r'初等对称', 'elementary symmetric wording')
grep(r'(?<![A-Za-zẽ])e_[0-9a-z{]', 'e_ subscripts')
grep(r'(?<![A-Za-z])P_3', 'P_3')
grep(r'Λ_', 'Lambda_')
grep(r'(?<![A-Za-z])c_j', 'c_j')
grep(r'(?<![A-Za-z])c_[0-9]', 'c_<digit>')
grep(r'(?<![A-Za-z])c_m', 'c_m')
grep(r'c_i', 'c_i')
grep(r'不存在', 'nonexistence wording')
grep(r'没有闭式|闭式', 'closed form wording')
grep(r'表 2', 'Table 2 refs')
