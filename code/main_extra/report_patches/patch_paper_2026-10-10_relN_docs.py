# -*- coding: utf-8 -*-
"""README.md、ROADMAP.md 与 data/lit/README.md 跟着 patch_paper_2026-10-10_relN.py 与第三次新颖性补查同步
（2026-10-10，用户：「按照你的想法来」）。每处替换断言原文出现一次；按字节读写（LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_relN_docs.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

ROUND4 = (
    ' 2026-10-10 第四轮（用户转来 GPT6.1Sol 的四条意见后答「按照你的想法来」；补丁 '
    '`code/main_extra/report_patches/patch_paper_2026-10-10_relN.py`，日志 `logs/*_2026-10-10_relN.log`）：新增附录 B，'
    '给出 Rel(N)=O·L_N 与 N 的维数公式（总次数与分次数两种，定理 B.1）的完整人工证明，照 Lean 的路线（二项式变换把问题搬到 U、'
    '两条搬运引理、边界引理、左因子 1+Y 的饱和引理）；引理 B.2 的恒等式另由 `code/main_extra/check_appendix_relN.py` '
    '在随机整数组上精确核对（14 PASS）。第 5 节 Rel(N) 一段去掉「We omit the proof」，改为指向附录 B，并改正原来「需要 Y 与 '
    '1+Y 两个饱和引理」的说法（主定理只用 1+Y 的）；第 9 节表 5 新增定理 B.1 一行。摘要与引言按三项主结果重排：固定 m 的结构'
    '（定理 A、B）、全部递推（定理 C，原 D）、h_k 实根（定理 D，原 F）；新增小节「Further results」放渐近、列的最小阶与 OEIS、'
    '求和形状（定理 E，原 C）与近对角线（定理 F，原 E）；引言定理的标签改为按内容命名（intro:order 等），定理陈述逐字不变；'
    '相关工作末尾加「What is new」一段（工具是标准的，新的是这些数组上的结论与形式化，超出直接套用的是块分解、附录 B 的搬运与'
    '四条交错关系的联合归纳）；「Organization」补两个附录。核对：check_tex 无问题（标签 102、引用 94、文献 31/31）、'
    'check_paper_numbers 32 PASS、check_appendix_lean 34 PASS、check_appendix_relN 14 PASS、check_chains_negzeros 6 PASS、'
    'check_bib_dois 26 PASS，Tectonic 37 页、没有溢出。同日另写了给人类专家的英文审读指南 `paper/reviewer_guide.pdf`'
    '（2 页：主结果、已形式化的部分、最需要人工核对的部分及页码、新颖性问题、复现命令），并补查第 5、6、8 节的开放数据库'
    '（`notes/新颖性核查_2026-10-07.md` §10，没有发现先例）。'
)

README = [
    ('引言加了与布尔格、Stirling 数和 Euler 多项式的对照），现 33 页；',
     '引言加了与布尔格、Stirling 数和 Euler 多项式的对照；2026-10-10 第四轮补了附录 B（N 的零化理想与维数公式的完整证明）、'
     '按三项主结果重排了摘要与引言），现 37 页；'),
    ('（2026-10-09 第三轮删去第 6.3 节后 33 页；新结论的核对见 `check_chains_negzeros.py`',
     '（2026-10-09 第三轮删去第 6.3 节后 33 页，2026-10-10 第四轮加附录 B 后 37 页；附录 B 的恒等式见 '
     '`check_appendix_relN.py`；给审稿人的英文审读指南 `paper/reviewer_guide.pdf`；新结论的核对见 `check_chains_negzeros.py`'),
    ('pdflatex 还没实测（本机没有 pdflatex，用 Overleaf 编一次即可）。',
     'pdflatex 还没实测（本机没有 pdflatex，用 Overleaf 编一次即可）。' + ROUND4),
]

ROADMAP = [
    ('## 5. 新颖性与外部评审（开放数据库部分已做，2026-10-07；其余待做）',
     '## 5. 新颖性与外部评审（开放数据库部分已做，2026-10-07，10-10 补查第 5、6、8 节；其余待做）'),
    ('**2026-10-06 做过的初步检索**',
     '**2026-10-10 补查**（笔记 §10，`code/novelty/recheck_2026-10-10.py`，数据 `data/lit/raw_recheck_2026-10-10/`）：针对第 5 节'
     '（N 的零化理想，附录 B）、第 6 节（求和形状）与第 8 节（h_k 实根、链多项式；10-07 时还只是猜想 B1）在 OpenAlex、Crossref、'
     'arXiv 跑了 20 条查询（742 条记录），并取了 7 篇种子的前向引用（375 篇），没有找到先例。最接近的是链多项式实根性的一般结果'
     '（Athanasiadis 等两篇、Brändén–Saud Maia Leite 的 TN 偏序集与几何格），它们的零点都在 [−1,0]，覆盖不了 Λ_k；以及只含上一行'
     '的两项三角递推的实根、对数凹方法（Shankar 2026 两篇、Alexandersson 2026 两篇），不覆盖 N 的 k−3 项递推。开放数据库里这几篇'
     '的前向引用只有 0–3 条，所以手动清单新增 G 组（第 5、8 节），最优先的是它们在 Google Scholar 或 MathSciNet 的被引用。'
     '论文相关工作末尾加了「What is new」一段，区分标准工具与本文特有的步骤。给人类专家的英文审读指南：`paper/reviewer_guide.pdf`。\n\n'
     '**2026-10-06 做过的初步检索**'),
]

LIT_README = [
    ('| `raw_scholar_followup/` |',
     '| `raw_recheck_2026-10-10/` | `code/novelty/recheck_2026-10-10.py` 的原始返回：第三次补查（论文第 5、6、8 节）20 条查询 × OpenAlex、'
     'Crossref、arXiv，以及 7 篇种子的 OpenAlex 前向引用（`cites__<种子>.json`）；`_manifest.jsonl` 记每次请求 |\n'
     '| `recheck_2026-10-10.md` | `recheck_2026-10-10.py report` 生成：每条查询每个来源的前 10 名、同时命中 ≥2 条查询的文献、前向引用候选；'
     '分类见笔记 §10 |\n'
     '| `raw_scholar_followup/` |'),
    ('py -3.14 code/novelty/check_note_refs.py        #',
     'py -3.14 code/novelty/recheck_2026-10-10.py report   # 2026-10-10 第三次补查：只用本地 raw_recheck_2026-10-10/ 重新生成 recheck_2026-10-10.md\n'
     'py -3.14 code/novelty/check_note_refs.py        #'),
]


def patch(path, reps):
    raw = open(path, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in reps:
        c = s.count(old)
        assert c == 1, (path, c, old[:60])
        s = s.replace(old, new)
    open(path, 'wb').write(s.encode('utf-8'))
    print('%s: %d edits' % (os.path.relpath(path, ROOT), len(reps)))


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    patch(os.path.join(ROOT, 'README.md'), README)
    patch(os.path.join(ROOT, 'ROADMAP.md'), ROADMAP)
    patch(os.path.join(ROOT, 'data', 'lit', 'README.md'), LIT_README)


if __name__ == '__main__':
    main()
