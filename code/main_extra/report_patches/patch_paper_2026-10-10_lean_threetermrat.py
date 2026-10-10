# -*- coding: utf-8 -*-
r"""Lean 续作第十二项（2026-10-10）：论文推论 5.7 按原样（有理函数系数）形式化，新模块 `lean/A207123/ThreeTermRat.lean`：
`RatCoef = FractionRing Coef`（ℂ(k, m)）、`HasValueAt c x y z`（c 有表示 a/b，b(x, y) ≠ 0，z = a(x, y)/b(x, y)）、
`HasValueAt.unique`（值与表示无关）、`not_annihilate_three_terms_rat`、`not_annihilate_two_terms_rat`、
`not_annihilate_kauers_rat`（取公分母化到 ThreeTerm.lean 的三条）。没有形式化：推论 5.5 与有理系数陈述之间的一步
（要先建有理系数的 Ore 代数）；由 Kauers 定义 3 推出生成元零化延拓的一步。新定义由 AI 对照论文核对。
根模块加 import，Axioms 加四条（共 306 条）；全量扫描的声明数从 logs/lean_axioms_2026-10-10_threetermrat.log 读。

另外改正第 9 节一句：原写「The definitions that carry the meaning of the formal statements are transcribed in
Appendix A」，但续作第 5–12 项新引入的定义（分块、c_m、τ_m、有理函数在一点的值等）没有转录进附录 A，也只经过
AI 对照；改为「The basic definitions …」，并加一句说明这些后加的定义在 Lean 文件里、目前只经过 AI 对照。审读指南同步。

本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 推论 5.7 一行列出有理系数的三条与分母乘掉的
  三条；「Not formalized」里只剩推论 5.5 的那一步；注 5.8 末句；第 9 节关于附录 A 的一段。
- paper/reviewer_guide.tex：第 2 节推论 5.7 去掉「with denominators cleared」、附录 A 一句；第 3 节第 4 条只剩推论 5.5。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_threetermrat.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_threetermrat.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
FRESH = '45'

PAPER = [
    (r'Corollary~\ref{cor:stirlinglike} & \lean{not\_annihilate\_three\_terms}, \lean{not\_annihilate\_two\_terms}, '
     r'\lean{not\_annihilate\_kauers} (with denominators cleared)\\',
     r'Corollary~\ref{cor:stirlinglike} & \lean{not\_annihilate\_three\_terms\_rat}, \lean{not\_annihilate\_two\_terms\_rat}, '
     r'\lean{not\_annihilate\_kauers\_rat}; with denominators cleared: \lean{not\_annihilate\_three\_terms}, '
     r'\lean{not\_annihilate\_two\_terms}, \lean{not\_annihilate\_kauers}\\'),
    (r'the passage between Corollaries~\ref{cor:saturated} and~\ref{cor:stirlinglike}, which are stated for operators '
     r'with rational coefficients, and their formalized versions with denominators cleared;',
     r'the passage between Corollary~\ref{cor:saturated}, which is stated for operators with rational coefficients, and '
     r'its formalized version with denominators cleared;'),
    (r'Not formalized are the choice of a common denominator and the step from \cite[Definition~3]{Kauers07} to the '
     r'annihilation of an extension by its three-term generator.',
     r'The choice of a common denominator is also formalized, but not the step from \cite[Definition~3]{Kauers07} to the '
     r'annihilation of an extension by its three-term generator.'),
    (r'The definitions that carry the meaning of the formal statements are transcribed in',
     r'The basic definitions that carry the meaning of the formal statements are transcribed in'),
    (r'the checklist used for the comparison is in the notes folder of the repository.',
     r'the checklist used for the comparison is in the notes folder of the repository. Further definitions used by some '
     r'entries of Table~\ref{tab:lean}, for instance those of the blocks, of $c_m$ and $\tau_m$ and of the value of a '
     r'rational function at a point, are documented in the Lean files and have so far been compared with the paper only '
     r'by AI.'),
]
PAPER_RE = [
    (r'consists of 36 files that start from', 'consists of 37 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('Corollary 5.7 (with denominators cleared), and the near-diagonal theorem',
     'Corollary 5.7, and the near-diagonal theorem'),
    (r'\textbf{Appendix A (pp.~31--33) transcribes the definitions that carry the meaning}, and comparing them with the '
     r'paper is a short and useful check.',
     r'\textbf{Appendix A (pp.~31--33) transcribes the basic definitions that carry the meaning}, and comparing them with '
     r'the paper is a short and useful check; the definitions added for later entries of Table 5 (blocks, $c_m$, '
     r'$\tau_m$, values of rational functions) are in the Lean files and have been compared only by AI.'),
    ('and the choice of a common denominator in Corollaries 5.5 and 5.7.',
     'and the choice of a common denominator in Corollary 5.5.'),
]

README = [
    ('`AsympRemark.lean` 与 `OeisRemark.lean`）', '`AsympRemark.lean`、`OeisRemark.lean` 与 `ThreeTermRat.lean`）'),
    ('共 36 个模块（', '共 37 个模块（'),
    ('（补丁 `patch_paper_2026-10-10_lean_oeisremark.py`）。',
     '（补丁 `patch_paper_2026-10-10_lean_oeisremark.py`）。第十二项：推论 5.7 按论文原样（有理函数系数）形式化，'
     '新模块 `ThreeTermRat.lean`：`RatCoef = FractionRing Coef`（ℂ(k, m)）、`HasValueAt c x y z`（c 有表示 a/b，'
     'b(x, y) ≠ 0，z = a(x, y)/b(x, y)；`HasValueAt.unique`：值与表示无关）、`not_annihilate_three_terms_rat`、'
     '`not_annihilate_two_terms_rat`、`not_annihilate_kauers_rat`（取公分母 Δ = b₀b₁b₂、n_i = a_i∏_{j≠i}b_j，'
     '化到 `ThreeTerm.lean` 的三条）。没有形式化：推论 5.5 与有理系数陈述之间的一步（要先建有理系数的 Ore 代数）、'
     '由 Kauers 定义 3 推出生成元零化延拓的一步。一次编译通过、无警告。论文第 9 节同时改正一句：附录 A 转录的是'
     '「basic definitions」，续作第 5–12 项新引入的定义（分块、c_m、τ_m、有理函数在一点的值等）在 Lean 文件里，'
     '目前只经过 AI 对照；审读指南同步。Axioms 306 条，全量扫描 %s 个声明，只有三条标准公理；'
     '`check_lean_fresh.py` %s PASS（补丁 `patch_paper_2026-10-10_lean_threetermrat.py`）。' % (DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、定理 3\.2\(2\)\(3\)、注记 3\.3 的精确部分、'
     r'注记 3\.5 中不靠计算的部分、推论 5\.5、推论 5\.7、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、定理 3.2(2)(3)、注记 3.3 的精确部分、'
     '注记 3.5 中不靠计算的部分、推论 5.5、推论 5.7（含有理系数的原样陈述）、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_oeisremark.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_oeisremark.log`）。同日第十二项：新模块 `ThreeTermRat.lean`（论文推论 5.7 '
     '的有理函数系数原样陈述；新定义 `RatCoef`（`FractionRing Coef`，即 ℂ(k, m)）、`HasValueAt`（有理函数在一点有定义'
     '及其值：有表示 a/b 且 b 在该点不为 0，值为 a/b 在该点的值）由 AI 对照论文核对，`HasValueAt.unique` 证明值与表示'
     '无关），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（306 条，%s 个声明，只有三条标准公理）与 '
     '`Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_threetermrat.log`）。'
     '论文第 9 节据此改为「basic definitions」并注明后加的定义只经过 AI 对照。' % (DECLS, FRESH)),
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
