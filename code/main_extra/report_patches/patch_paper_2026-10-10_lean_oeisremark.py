# -*- coding: utf-8 -*-
r"""Lean 续作第十一项（2026-10-10）：论文注记 3.5（OEIS 条目）中不靠计算的部分形式化，新模块
`lean/A207123/OeisRemark.lean`：`parDen_three` … `parDen_seven`（(1−x)^{2k+1}(1+x)^{2k−1} 的系数恰是 A207118–A207122
经验递推的系数取反、首项补 1，即特征多项式恰为 (x−1)^{2k+1}(x+1)^{2k−1}）、`oeis_A207118` … `oeis_A207122`（这五个
经验递推按 OEIS 原样对一切 n ≥ 4k 成立；陈述由 `code/main_extra/oeis_columns_lean.py` 从 OEIS 快照生成）、`row_rec`
（k ↦ a_k(n) 满足 Δ_n = (3⌈n/2⌉+1)(3⌊n/2⌋+1) 阶首一常系数递推）、`row_rec_of_consecutive`（常系数递推在 Δ_n 个相邻的
k 上成立就对其后一切 k 成立）、`aAlt_two`、`aAlt_three`（A207069、A207070 标题的列规则 001/101 在两行、三行时与
001/011 给出同样的数）。没有形式化：行 n = 2,…,7 的经验递推的精确算术核对与 Berlekamp–Massey 给出的最小阶。
新定义 `ofList`、`rowOrd`、`rowPoly`、`ColRuleAlt`、`aAlt`、`swap01` 由 AI 对照论文与 OEIS 标题核对。
根模块加 import，Axioms 加十四条（共 302 条）；全量扫描的声明数从 logs/lean_axioms_2026-10-10_oeisremark.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 在推论 3.4 一行之后加注记 3.5 一行；
  「Not formalized」里「Remark 3.5」改为行递推的精确核对与其阶的最小性。
- paper/reviewer_guide.tex：第 2 节加上注记 3.5 的列递推与行递推判据；第 3 节第 5 条加上行递推的精确核对。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_oeisremark.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_oeisremark.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
FRESH = '44'

ROW34 = r'Corollary~\ref{cor:columns} & \lean{T1\_9}, \lean{parity\_min\_order}\\' '\n'
PAPER = [
    (ROW34, ROW34 + r'Remark~\ref{rem:oeis}, except the row checks & \lean{parDen\_three}--\lean{parDen\_seven}, '
     r'\lean{oeis\_A207118}--\lean{oeis\_A207122}, \lean{row\_rec}, \lean{row\_rec\_of\_consecutive}, '
     r'\lean{aAlt\_two}, \lean{aAlt\_three}\\' '\n'),
    (r'the numerical values in Remark~\ref{rem:asym}; Remark~\ref{rem:oeis};',
     r'the numerical values in Remark~\ref{rem:asym}; the exact-arithmetic checks of the row recurrences in '
     r'Remark~\ref{rem:oeis} and the minimality of their orders;'),
]
PAPER_RE = [
    (r'consists of 35 files that start from', 'consists of 36 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('with the exact statements of Remark 3.3, Corollary 3.4, the block decomposition',
     'with the exact statements of Remark 3.3, Corollary 3.4 with the OEIS column recurrences and the criterion for '
     'the row recurrences in Remark 3.5, the block decomposition'),
    (r'\item \textbf{Section 3:} the numerical values in Remark 3.3.',
     r'\item \textbf{Section 3:} the numerical values in Remark 3.3 and the exact-arithmetic checks of the row '
     r'recurrences in Remark 3.5.'),
]

README = [
    ('`RootAsymp.lean` 与 `AsympRemark.lean`）', '`RootAsymp.lean`、`AsympRemark.lean` 与 `OeisRemark.lean`）'),
    ('共 35 个模块（', '共 36 个模块（'),
    ('（补丁 `patch_paper_2026-10-10_lean_asympremark.py`）。',
     '（补丁 `patch_paper_2026-10-10_lean_asympremark.py`）。第十一项：注记 3.5（OEIS 条目）中不靠计算的部分，新模块'
     ' `OeisRemark.lean`：`parDen_three` … `parDen_seven`（(1−x)^{2k+1}(1+x)^{2k−1} 的系数恰是 A207118–A207122 经验递推'
     '的系数取反、首项补 1，即特征多项式恰为 (x−1)^{2k+1}(x+1)^{2k−1}）、`oeis_A207118` … `oeis_A207122`（这五个经验递推'
     '按 OEIS 原样对一切 n ≥ 4k 成立；陈述与系数表由 `code/main_extra/oeis_columns_lean.py` 从 `data/lit/oeis/` 的快照'
     '逐字生成，脚本同时在 Python 里核对系数）、`row_rec`（k ↦ a_k(n) 满足 Δ_n = (3⌈n/2⌉+1)(3⌊n/2⌋+1) 阶首一常系数递推，'
     '特征多项式 `rowPoly n` = ∏(X − στ)）、`row_rec_of_consecutive`（常系数递推在 Δ_n 个相邻的 k 上成立就对其后一切 k '
     '成立）、`aAlt_two`、`aAlt_three`（A207069、A207070 标题的列规则 001/101 在两行、三行时与 001/011 给出同样的数；'
     '三行时交换前两行）。没有形式化：行 n = 2,…,7 的经验递推的精确算术核对与 Berlekamp–Massey 给出的最小阶。'
     '一次编译通过、无警告。Axioms 302 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS'
     '（补丁 `patch_paper_2026-10-10_lean_oeisremark.py`）。' % (DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、定理 3\.2\(2\)\(3\)、注记 3\.3 的精确部分、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、定理 3.2(2)(3)、注记 3.3 的精确部分、'
     '注记 3.5 中不靠计算的部分、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_asympremark.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_asympremark.log`）。同日第十一项：新模块 `OeisRemark.lean`（论文注记 3.5 中'
     '不靠计算的部分；新定义 `ofList`（系数表对应的多项式）、`rowOrd`（Δ_n）、`rowPoly`（∏(X − στ)）、`ColRuleAlt`'
     '（列规则 001/101，即 A207069、A207070 标题的规则）、`aAlt`（相应的矩阵个数）、`swap01`（交换前两行）由 AI 对照'
     '论文与 OEIS 标题核对；五个 OEIS 递推的陈述由脚本从快照逐字生成），经 `lean/lean_one.sh` 编译、重编根模块、'
     '重跑 `Axioms.lean`（302 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_oeisremark.log`）。' % (DECLS, FRESH)),
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
    print('declarations:', DECLS)
    patch(os.path.join(ROOT, 'paper', 'main.tex'), PAPER, PAPER_RE)
    patch(os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), GUIDE)
    patch(os.path.join(ROOT, 'README.md'), README, README_RE)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)


if __name__ == '__main__':
    main()
