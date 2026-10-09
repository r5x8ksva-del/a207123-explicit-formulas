# -*- coding: utf-8 -*-
"""README.md 与 data/lit/read_papers.md 跟着 patch_paper_2026-10-09_reportrefs.py 同步（2026-10-09 晚，用户：「按照你的想法来」）。
每处替换断言原文出现一次；按字节读写（LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-09_reportrefs_docs.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

README = [
    ('同日晚按审读意见修订（新摘要、推论 8.15、注记 8.16、5 条新文献，源文件里不再有 TODO 与内部注释），现 36 页；',
     '同日晚按审读意见修订两轮（新摘要、推论 8.15、注记 8.16、5 条新文献，源文件里不再有 TODO 与内部注释；'
     '论文不再引用只在报告与笔记里有证明的结论），现 36 页；'),
    ('审读意见里还没做的：注记 6.4 与第 10 节引用中文报告的结论，要么写进附录、要么另发英文短文、要么删去；'
     '推论 5.5 之后 Rel(N)=𝒪·L_N 只有证明梗概；定理 6.13 的 (N1)(N2) 偏人为；符号重载（h、τ、T、D、V、P、α、β、N）；'
     '篇幅（第 6 节占 8 页）；要读 Brändén–Saud Maia Leite（Adv. Math. 2026）确认它的一般理论是否已覆盖 Λ_k；pdflatex 还没实测。',
     '同日晚第二轮（用户：「按照你的想法来」；补丁 `code/main_extra/report_patches/patch_paper_2026-10-09_reportrefs.py`，'
     '日志 `logs/*_2026-10-09_reportrefs.log`）：论文不再依赖中文报告与笔记——只在那里证明的结论不写进论文（注记 6.4 的负形状'
     '改为「本文不处理」；第 10 节删去「报告排除了更多的类」与 (3) 的约化、(4) 的门槛定理），计算证据保留并写明脚本在仓库'
     '（(3) 的 k≤300、(4) 的 i≤579 与 α*≈9.6085）；第 9 节、AI 声明、「Data and code」里提到报告的说法改掉；推论 5.5 之后 '
     'Rel(N) 一段改为只陈述、注明完整证明在 Lean；推论 5.7 证明里 Kauers 的移位算子改用 S。读了 Brändén–Saud Maia Leite'
     '（arXiv:2412.06595v3 第 5、6 节，记录在 `data/lit/read_papers.md`）：他们的 TN-偏序集与 P-positive 偏序集的结果把链多项式'
     '的零点放在 [−1,0]，h-多项式系数非负时也必然如此，而 n_k 在 k≥3 时有 ⌊k/3⌋ 个零点小于 −1，所以定理 8.1 不能由这类结果推出；'
     '这一点写进了注记 8.16 与引言。核对：check_tex 无问题、check_paper_numbers 32 PASS、check_appendix_lean 34 PASS、'
     'check_bib_dois 26 PASS，Tectonic 36 页、没有溢出（仍有第 9 页底部那条 Underfull \\vbox）。审读意见里还没做的：定理 6.13 的 '
     '(N1)(N2) 偏人为；符号重载（h、T、D、V、P、α、β）；篇幅（第 6 节占 8 页）；引言与相关工作按链多项式 / Euler 类比重写；'
     'pdflatex 还没实测。'),
]

READ_PAPERS = [
    ('| fried_2607.24832.pdf | https://arxiv.org/pdf/2607.24832 |',
     '| bl26_2412.06595.pdf | https://arxiv.org/pdf/2412.06595 | Brändén-Saud Maia Leite, Totally nonnegative matrices, chain '
     'enumeration and zeros of polynomials (arXiv:2412.06595v3; Adv. Math. 487 (2026) 110760, doi:10.1016/j.aim.2025.110760) | '
     '摘要、引言、第 5 节（TN-偏序集与定理 5.5）、第 6 节（定义 6.1、定理 6.4-6.6）（2026-10-09 论文审读） | 33 | 670803 | '
     'bbcb98aac54a164f420059ed9601d1397670a792dd98f883dbd673b567fa2c43 |\n'
     '| fried_2607.24832.pdf | https://arxiv.org/pdf/2607.24832 |'),
]
FACT = ('- Brändén-Saud Maia Leite（arXiv:2412.06595v3，2026-10-09 读）：下三角、对角线为 1 的全非负矩阵给出实根多项式族；'
        '拟秩一致且矩阵 R(P) 全非负的「TN-偏序集」的链多项式实根，零点在 [−1,0]（定理 5.5）；对 TN-偏序集 P，P-positive 偏序集'
        '（相对 P 的 h-向量非负）的链多项式零点在 [−1,0]（定理 6.6，推广 Brenti-Welker）。本项目的 n_k 在 k≥3 时有 ⌊k/3⌋ 个零点'
        '小于 −1，所以 Λ_k 不在这些定理的范围内（论文注记 8.16）。\n')


def patch(path, reps, append=''):
    raw = open(path, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in reps:
        c = s.count(old)
        assert c == 1, (path, c, old[:60])
        s = s.replace(old, new)
    if append:
        s = s.rstrip('\n') + '\n' + append
    open(path, 'wb').write(s.encode('utf-8'))
    print('%s: %d edits%s' % (os.path.basename(path), len(reps), ' + 1 appended fact' if append else ''))


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    patch(os.path.join(ROOT, 'README.md'), README)
    patch(os.path.join(ROOT, 'data', 'lit', 'read_papers.md'), READ_PAPERS, FACT)


if __name__ == '__main__':
    main()
