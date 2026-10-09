# -*- coding: utf-8 -*-
"""README.md 与 ROADMAP.md 跟着 patch_paper_2026-10-09_trim.py 同步（2026-10-09 晚，用户：「按照你的想法来」）。
每处替换断言原文出现一次；按字节读写（LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-09_trim_docs.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

README = [
    ('同日晚按审读意见修订两轮（新摘要、推论 8.15、注记 8.16、5 条新文献，源文件里不再有 TODO 与内部注释；'
     '论文不再引用只在报告与笔记里有证明的结论），现 36 页；',
     '同日晚按审读意见修订三轮（新摘要、推论 8.15、注记 8.16、5 条新文献，源文件里不再有 TODO 与内部注释；'
     '论文不再引用只在报告与笔记里有证明的结论；删去第 6.3 节，引言加了与布尔格、Stirling 数和 Euler 多项式的对照），现 33 页；'),
    ('更短公式不存在（单族单和、其他形状、proper 超几何多重和）；',
     '更短公式不存在（单族单和、其他形状、两族和；proper 超几何多重和那一节 2026-10-09 删去，结论仍在报告 T2.7′）；'),
    ('（36 页；新结论的核对见 `check_chains_negzeros.py`',
     '（2026-10-09 第三轮删去第 6.3 节后 33 页；新结论的核对见 `check_chains_negzeros.py`'),
    ('审读意见里还没做的：定理 6.13 的 (N1)(N2) 偏人为；符号重载（h、T、D、V、P、α、β）；篇幅（第 6 节占 8 页）；'
     '引言与相关工作按链多项式 / Euler 类比重写；pdflatex 还没实测。',
     '同日晚第三轮（用户：「按照你的想法来」；补丁 `code/main_extra/report_patches/patch_paper_2026-10-09_trim.py`，'
     '日志 `logs/*_2026-10-09_trim.*`）：删去第 6.3 节（proper 超几何多重和，即报告的 T2.7′，连同命题 6.17；条件 (N1)(N2) '
     '偏人为，结论仍在报告与 Lean 的 partialSum_P_not_hypergeometric），引言定理 C、相关工作、第 6 节开头、第 9 节表 5 与'
     '附录 A 开头相应改动；引言「Main results」开头加一段：U_k(m) 是 Λ_k 的多重链数，布尔格对应 (m+1)^k、q!S(k,q) 与 '
     'Euler 多项式，定理 D(3)、E、F 分别对应 Stirling 数的零化子（Kauers 例 5）、对角线多项式（Gessel–Stanley）与 Euler '
     '多项式的实根性，定理 D(4) 与 h_k 大于 1 的零点是类比失效之处。核对：check_tex 无问题（标签 93、引用 83、文献 31/31）、'
     'check_paper_numbers 32 PASS、check_appendix_lean 34 PASS、check_bib_dois 26 PASS，Tectonic 33 页。注记 3.3 的数值段'
     '（check_paper_numbers 的 P24 核对它）、注记 3.5、第 6.2 节的证书细节与附录 A 保留（附录 A 让审稿人不看仓库也能核对'
     '形式化陈述）。审读意见里还没做的：符号重载（h、T、D、V、P、α、β；改名牵动全文与核对脚本，风险大于收益，暂不动）；'
     'pdflatex 还没实测（本机没有 pdflatex，用 Overleaf 编一次即可）。'),
    ('T2.7′ 连同 (N1)(N2) 写进 §6.2。', 'T2.7′ 连同 (N1)(N2) 写进 §6.2（2026-10-09 第三轮已从论文删去）。'),
]

ROADMAP = [
    ('T2.7′ 要连同条件 (N1)(N2) 一起写。', 'T2.7′ 要连同条件 (N1)(N2) 一起写（2026-10-09 第三轮已从论文删去，仍在报告）。'),
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
    print('%s: %d edits' % (os.path.basename(path), len(reps)))


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    patch(os.path.join(ROOT, 'README.md'), README)
    patch(os.path.join(ROOT, 'ROADMAP.md'), ROADMAP)


if __name__ == '__main__':
    main()
