# -*- coding: utf-8 -*-
r"""Lean 续作第二十一项的排版（2026-10-10）：论文第 9 节的「Formalized results」表拆成两张。

原因：第二十一项给表 5 加了推论 8.2 一行后，表高过一页的浮动体上限，被推到全文最后（第 38 页）。在草稿目录试过：
行距 0.88、只写一个名字（表变成整页浮动体，第 29 页 underfull \vbox）、把推论 8.2 并进上一行（首列溢出 32–48pt），
都不干净；第 8 节还有几项要加行，单张表撑不下去。拆成表 5（第 2–7 节，标签 tab:lean，标题
「Formalized results: Sections 2–7.」）与表 6（第 8 节，新标签 tab:lean8，标题「Formalized results: Section 8.」），
两张都只用 [t] 放置。拆开后附录 A 开头那一页仍有三条 underfull \vbox（附录 A 的 alltt 代码块不能分页）；又试了
八种放置（表 6 用 [tb]、[p]、[b]、[tbp]，两张都用 [tp]，表 5 用 [ht]，把表 6 的源码移到附录前），只有在 \appendix
前加 \clearpage 没有警告：39 页，表 5 在第 30 页、表 6 在第 31 页，附录 A 从第 32 页起，附录 B 从第 34 页起，参考文献
从第 38 页起（第十九项为了保持 38 页去掉过这个 \clearpage；现在两张表都在附录之前排完，以后表 6 再加行也不挤附录）。
正文里三处 Table~\ref{tab:lean} 改为两张表。审读指南开头的页数（原写 37 页，第十一项起其实已是 38 页）、第 2 节表与
附录 A 的页码、附录 B 的页码同步。

在 patch_paper_2026-10-10_lean_logconcave.py 之后运行；每处替换断言原文出现一次；按字节读写（都是 LF）。
用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_table_split.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

SPLIT_AFTER = (r'Theorem~\ref{thm:neardiag}, Proposition~\ref{prop:newton} & \lean{T4\_1}, \lean{T4\_1\_threshold}, '
               r'\lean{T4\_2\_3}\\' + '\n')
MID = ('\\bottomrule\n\\end{tabular}\n\\caption{Formalized results: Sections~\\ref{sec:prelim}--\\ref{sec:neardiag}.}'
       '\\label{tab:lean}\n\\end{table}\n\n\\begin{table}[t]\n\\centering\n\\footnotesize\n'
       '\\renewcommand{\\arraystretch}{0.90}\n'
       '\\begin{tabular}{l>{\\raggedright\\arraybackslash}p{0.62\\textwidth}}\n\\toprule\nResult & Lean names\\\\\n'
       '\\midrule\n')
TABLE_HEAD_OLD = '\\begin{table}[ht]\n\\centering\n\\footnotesize\n\\renewcommand{\\arraystretch}{0.90}\n'
TABLE_HEAD_NEW = '\\begin{table}[t]\n\\centering\n\\footnotesize\n\\renewcommand{\\arraystretch}{0.90}\n'

PAPER = [
    (SPLIT_AFTER, SPLIT_AFTER + MID),
    (TABLE_HEAD_OLD, TABLE_HEAD_NEW),
    ('\\caption{Formalized results.}\\label{tab:lean}',
     '\\caption{Formalized results: Section~\\ref{sec:realroots}.}\\label{tab:lean8}'),
    ('The main formal statements are listed in Table~\\ref{tab:lean}.',
     'The main formal statements are listed in Tables~\\ref{tab:lean} and~\\ref{tab:lean8}.'),
    ('Further definitions used by some entries of Table~\\ref{tab:lean},',
     'Further definitions used by some entries of Tables~\\ref{tab:lean} and~\\ref{tab:lean8},'),
    ('Table~\\ref{tab:lean} (for instance the Lean versions of',
     'Tables~\\ref{tab:lean} and~\\ref{tab:lean8} (for instance the Lean versions of'),
    ('% =====================================================================\n\\appendix\n',
     '% =====================================================================\n\\clearpage\n\\appendix\n'),
]

GUIDE = [
    ('This note accompanies the 37-page version of 10 October 2026.',
     'This note accompanies the 39-page version of 10 October 2026.'),
    ('The results in Table 5 (p.~30) are proved in Lean~4', 'The results in Tables 5 and 6 (pp.~30--31) are proved in Lean~4'),
    ('\\textbf{Appendix A (pp.~31--33) transcribes the basic definitions',
     '\\textbf{Appendix A (pp.~32--34) transcribes the basic definitions'),
    ('the definitions added for later entries of Table 5 (', 'the definitions added for later entries of Tables 5 and 6 ('),
    ('Appendix B (pp.~33--36) is formalized', 'Appendix B (pp.~34--37) is formalized'),
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
    patch(os.path.join(ROOT, 'paper', 'main.tex'), PAPER)
    patch(os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), GUIDE)


if __name__ == '__main__':
    main()
