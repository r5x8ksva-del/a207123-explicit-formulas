# -*- coding: utf-8 -*-
"""对抗性验证 consistency 审计的 24 条发现：先确认每条原文引用能在所指 report_parts 文件中精确找到。"""
import os, io

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
PARTS = os.path.join(ROOT, 'notes', 'report_parts')

Q = [
 (0, '00_head.md', '只依赖 Python 标准库；装有 numpy 时 c3b 与 rv2 会用它加速模素数运算'),
 (1, '01_summary.md', 'c4 的两条正性外推（d=47、d=69 起失效）'),
 (2, '03_C2.md', '其余奇数形状【已验证（数值，浮点纤维检验 α≥1、α+β≤12，只有 (2,1) 不能由纤维法排除，而它正是定理 S 的形状；不在 verify_all 中，见 notes/review/r-c2a-review.md §4.3）】'),
 (3, '05_C4.md', '一般的 M(d;σ,β) 没有闭式（见 ④A.5）'),
 (4, '06_C5.md', '等价地 U_k(m)=(2/k!)(m+μ_k)^k(1+O(m^{−2}))，μ_k=(k²−2k−1)/2；在 C(m+1,·) 基下 U_k=2C(m+1,k)+(k²−k−4)C(m+1,k−1)+p_2(k)C(m+1,k−2)+…'),
 (5, '06_C5.md', '(6)【已验证】k≥5 没有类似对应'),
 (6, '07_formula.md', '由 T3.7（F 不是 D-finite）与文献中的 Wilf–Zeilberger 定理（T2.7），U_k(m) 也不能写成 proper 超几何项在自然边界下的有限多重和'),
 (7, '04_C3.md', 'D-finite（等价于 Lipshitz 意义的 P-recursive）要求'),
 (8, '10_uncertain.md', '两位复核者都逐步重推过，其中一位发现维数公式证明里有一句话按字面不成立（已补正，公式不变）。数据上 22 个盒子（verify_all）加上复核者新增的盒子全部吻合，但数据只能检验有限个盒子。'),
 (9, '09_code.md', '**11 个核对模块**（每个都从 `code/core.py` 的原始定义程序取「真值」）'),
 (10, '00_head.md', '少数扩展范围只由第二轮复核脚本跑过，已在相应条目注明「不在 verify_all 中」并给出日志路径'),
 (11, '01_summary.md', '只发现 7 处表述不严谨（见 T1.3–T1.8、T5.1(5)）'),
 (12, '02_C1.md', 'ρ_m 为 y³=y²+m 的实根'),
 (13, '02_C1.md', '{C(x+1,q)} 是 Q[x] 的基'),
 (14, '03_C2.md', '例：R_k=c_1(k+3)+c_1(k−2)−1'),
 (15, '03_C2.md', 'E 的两项 u 型和对一切 m≥3、|3m+3−N_i|≤1500 不存在'),
 (16, '03_C2.md', '（复核者 r-c2b，logs/review_r-c2b_r4b_full.log，不在 verify_all 中；verify_all 只复现 E m=3、U m=2）'),
 (17, '04_C3.md', 'F = Σ_{j≥0} κ_j·(t^j/b_j)·₁F₁(1; j+1−λ; −t/x³)，κ_0=1、κ_j=j x²（j≥1；这里换用 κ，以免与 c_i(n)、c_m 混淆）'),
 (18, '05_C4.md', '所以 2d·c_d=c_{d−1}，c_d=2/(2^d d!)'),
 (19, '05_C4.md', '（h_1 作为平移量的多项式首项为负，Fujiwara 根界外恒负，界内逐个精确计算）'),
 (20, '06_C5.md', '（ẽ_j(n)=e_j(−1,0,…,n−2)/n^{\\underline j}）'),
 (21, '06_C5.md', 'Q_3 与 P_3 不同构但链数同为 (1,4,2)'),
 (22, '06_C5.md', '(5) 提示词「m=2、3 在 k=40 时相差 <0.4%」只在「相邻比 U_41/U_40 与 ρ_m 比较」的解释下成立'),
 (23, '09_code.md', '解析版本的反例与数值、𝒩 与 H'),
]

out = []
for i, fn, q in Q:
    with io.open(os.path.join(PARTS, fn), encoding='utf-8') as f:
        s = f.read()
    c = s.count(q)
    # also check in all parts
    where = []
    for g in sorted(os.listdir(PARTS)):
        with io.open(os.path.join(PARTS, g), encoding='utf-8') as f:
            if q in f.read():
                where.append(g)
    out.append('#%-2d %-15s count=%d  found_in=%s' % (i, fn, c, ','.join(where)))

# report == concat?
parts = sorted(os.listdir(PARTS))
cat = ''
for g in parts:
    with io.open(os.path.join(PARTS, g), encoding='utf-8') as f:
        cat += f.read()
with io.open(os.path.join(ROOT, '报告.md'), encoding='utf-8') as f:
    rep = f.read()
out.append('report chars=%d, concat chars=%d' % (len(rep), len(cat)))
# check each part's content is in report
for g in parts:
    with io.open(os.path.join(PARTS, g), encoding='utf-8') as f:
        t = f.read().strip()
    out.append('  part %s in report: %s' % (g, t in rep))
print('\n'.join(out))
