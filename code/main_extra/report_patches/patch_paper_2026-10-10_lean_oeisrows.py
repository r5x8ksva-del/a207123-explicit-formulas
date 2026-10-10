# -*- coding: utf-8 -*-
r"""Lean 续作第十四项（2026-10-10）：论文注记 3.5 的行递推核对形式化，新模块 `lean/A207123/OeisRows.lean`：
`Ucol`（按引理 1 逐列算 U，`Ucol_eq`）、`rowList`（a_k(n) 的前 K+1 项，`rowList_eq`）、`checkWindows`、`row_rec_of_check`
（窗口核对为真 ⇒ 前向递推对一切 k ≥ k0 成立，由 `row_rec_of_consecutive`），以及 `oeis_A207069`、`oeis_A207070`、
`oeis_A207124` … `oeis_A207127`：A207123 第 n = 2,…,7 行的经验递推按 OEIS 原样对一切 n ≥ e 成立（e = 10, 22, 28, 49,
55, 85），每条用 decide +kernel 在 Δ_n 个相邻窗口上核对。陈述与系数表由 `code/main_extra/oeis_rows_lean.py` 从 OEIS 快照
逐字生成。没有形式化：Berlekamp–Massey 给出的阶是最小的，以及它们等于特征根之积中不同值的个数。
新定义 `colStep`、`Ucol`、`rowList`、`seg`、`Uext`、`resid`、`checkWindows` 由 AI 核对（`Ucol_eq`、`rowList_eq` 证明前两者
算的就是 U 与 a）。根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_oeisrows.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 推论 3.4 与注记 3.5 一行加六个名字；
  「Not formalized」里注记 3.5 那句只剩行递推阶的最小性。
- paper/reviewer_guide.tex：第 2 节注记 3.5 一句；第 3 节第 5 条同步。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_oeisrows.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_oeisrows.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '47'

ROW = (r'Corollary~\ref{cor:columns}, Remark~\ref{rem:oeis} in part & \lean{T1\_9}, \lean{parity\_min\_order}, '
       r'\lean{oeis\_A207118}--\lean{oeis\_A207122}, \lean{row\_rec}, \lean{row\_rec\_of\_consecutive}, '
       r'\lean{aAlt\_two}, \lean{aAlt\_three}')
PAPER = [
    (ROW + r'\\', ROW + r', \lean{oeis\_A207069}, \lean{oeis\_A207070}, \lean{oeis\_A207124}--\lean{oeis\_A207127}\\'),
    (r'the exact-arithmetic checks of the row recurrences in Remark~\ref{rem:oeis} and the minimality of their orders;',
     r'the minimality of the orders of the row recurrences in Remark~\ref{rem:oeis};'),
]
PAPER_RE = [
    (r'consists of 38 files that start from', 'consists of 39 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('Corollary 3.4 with the OEIS column recurrences and the criterion for the row recurrences in Remark 3.5,',
     'Corollary 3.4 with the OEIS recurrences for the columns and the rows in Remark 3.5,'),
    (r'\item \textbf{Section 3:} the numerical values in Remark 3.3 and the exact-arithmetic checks of the row '
     r'recurrences in Remark 3.5.',
     r'\item \textbf{Section 3:} the numerical values in Remark 3.3 and the minimality of the orders of the row '
     r'recurrences in Remark 3.5.'),
]

README = [
    ('`ThreeTermRat.lean` 与 `SaturatedRat.lean`）', '`ThreeTermRat.lean`、`SaturatedRat.lean` 与 `OeisRows.lean`）'),
    ('共 38 个模块（', '共 39 个模块（'),
    ('（补丁 `patch_paper_2026-10-10_lean_saturatedrat.py`）。',
     '（补丁 `patch_paper_2026-10-10_lean_saturatedrat.py`）。第十四项：注记 3.5 的行递推核对，新模块 `OeisRows.lean`：'
     '`Ucol`（按引理 1 逐列算 U 的前 K+1 项，`Ucol_eq` 证明它就是 U）、`rowList`（a_k(n) 的前 K+1 项，`rowList_eq`）、'
     '`checkWindows`、`row_rec_of_check`（Δ_n 个相邻窗口上核对为真 ⇒ 前向递推对一切 k ≥ k0 成立，由 '
     '`row_rec_of_consecutive`），`oeis_A207069`、`oeis_A207070`、`oeis_A207124` … `oeis_A207127`：A207123 第 n = 2,…,7 行'
     '的经验递推按 OEIS 原样对一切 n ≥ e 成立（e = 10, 22, 28, 49, 55, 85；n = e 时用到 a_0(n) = 1），每条用 '
     '`decide +kernel` 在内核里核对（不用 native_decide，不引入公理；第 7 行的数到 10^120 量级）。陈述与系数表由 '
     '`code/main_extra/oeis_rows_lean.py` 从 `data/oeis/` 的快照逐字生成，脚本同时在 Python 里核对（窗口与更长范围）。'
     'A207069、A207070 用 `aAlt`（标题的列规则 001/101）陈述。没有形式化：Berlekamp–Massey 给出的阶是最小的、等于特征根'
     '之积中不同值的个数。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS'
     '（补丁 `patch_paper_2026-10-10_lean_oeisrows.py`）。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、定理 3\.2\(2\)\(3\)、注记 3\.3 的精确部分、'
     r'注记 3\.5 中不靠计算的部分、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、定理 3.2(2)(3)、注记 3.3 的精确部分、'
     '注记 3.5（行递推阶的最小性除外）、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_saturatedrat.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_saturatedrat.log`）。同日第十四项：新模块 `OeisRows.lean`（论文注记 3.5 的行'
     '递推核对；新定义 `colStep`、`Ucol`、`rowList`、`seg`、`Uext`、`resid`、`checkWindows` 由 AI 核对，其中 `Ucol_eq`、'
     '`rowList_eq` 证明 `Ucol`、`rowList` 算的就是 U 与 a；六条 OEIS 递推的陈述由脚本从快照逐字生成），经 '
     '`lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，'
     '`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_oeisrows.log`）。' % (_ax, DECLS, FRESH)),
]


def patch(path, reps, regex=()):
    raw = open(path, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in reps:
        c = s.count(old)
        assert c == 1, (path, c, old[:60])
        s = s.replace(old, new)
    for pat, new in regex:
        found = re.findall(pat, s)
        assert len(found) == 1, (path, len(found), pat[:60])
        s = re.sub(pat, lambda _m: new, s)
    open(path, 'wb').write(s.encode('utf-8'))
    print('%s: %d edits' % (os.path.relpath(path, ROOT), len(reps) + len(regex)))


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    print('declarations:', DECLS, ' Axioms lines:', _ax)
    patch(os.path.join(ROOT, 'paper', 'main.tex'), PAPER, PAPER_RE)
    patch(os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), GUIDE)
    patch(os.path.join(ROOT, 'README.md'), README, README_RE)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)


if __name__ == '__main__':
    main()
