# -*- coding: utf-8 -*-
r"""patch_paper_2026-10-10_lean_threeterm.py 的后续（2026-10-10）：
- paper/main.tex：附录 A 开头一句加上「and some of these statements」（附录 A 也抄录定理的陈述，原句只说定义；
  顺带消掉文件清单加 ThreeTerm.lean 后这一段的 Underfull \hbox）。
- paper/reviewer_guide.tex：论文从 37 页变成 38 页后的页码：表 5 在第 30 页（原第 29 页），附录 A 在第 30–33 页
  （原 30–32），附录 B 在第 33–36 页（原 32–36）。第 4–8 节与「What is new」的页码没变（PyMuPDF 逐页核对）。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_threeterm_fix.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

PAPER = [
    (r'We transcribe the definitions that carry the meaning of the main formal statements of Section~\ref{sec:lean}, '
     r'from the files',
     r'We transcribe the definitions that carry the meaning of the main formal statements of Section~\ref{sec:lean}, '
     r'and some of these statements, from the files'),
]

GUIDE = [
    (r'The results in Table 5 (p.~29) are proved', r'The results in Table 5 (p.~30) are proved'),
    (r'\textbf{Appendix A (pp.~30--32) transcribes', r'\textbf{Appendix A (pp.~30--33) transcribes'),
    (r'Appendix B (pp.~32--36) is formalized', r'Appendix B (pp.~33--36) is formalized'),
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
