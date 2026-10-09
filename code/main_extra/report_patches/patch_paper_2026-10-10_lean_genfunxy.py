# -*- coding: utf-8 -*-
r"""Lean 续作第五项（2026-10-10）：论文定理 4.4（按上升数细化的二元母函数）与引理 4.5 的按 y 细化形式化，
新模块 `lean/A207123/GenFunXY.lean`：`Gxy_zero`（b_0·G_0 = 1，即 G_{−1} = 1）、`Gxy_rec`（b_{m+1}·G_{m+1} =
G_m + (m+1)·y·x²）、`Gxy_prod`（第二式乘掉分母）、`coef_formula_xy`（∏_{v=j}^{m} b_v⁻¹ 的 xⁿyˢ 系数是
H(m,s,j)·C(n+m−j−2s, n−3s)）。G_m 写成 x 的幂级数、系数是 y 的幂级数（ℚ⟦y⟧⟦x⟧）。论文用块分解（定理 4.2）证明
定理 4.4；Lean 走按上升数细化的引理 1（`Ascent.lean`），与 y = 1 的 `G_rec` 同一路线。
根模块加 import，Axioms 加四条（共 268 条）；全量扫描的声明数从 logs/lean_axioms_2026-10-10_genfun.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数 29 → 30、声明数；表 5 在定理 4.6 一行之前加定理 4.4 与引理 4.5 一行；
  「Not formalized」去掉定理 4.4 的母函数与引理 4.5 的按 y 细化，括号里改为定理 4.4、4.6 的形式证明都走细化递推。
- paper/reviewer_guide.tex：第 2 节加上定理 4.4 与引理 4.5；第 3 节第 3 条去掉定理 4.4 与引理 4.5 的细化。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项；核对清单 6.2 一行补记推论 5.7 已在 Lean 中（第四项）。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_genfunxy.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_genfun.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
FRESH = '38'

ROW46 = r'Theorem~\ref{thm:explicit}, Remark~\ref{rem:forms} & \lean{U\_explicit}, \lean{Us\_explicit}, \lean{U\_F3}, \lean{U\_F4}\\' '\n'
PAPER = [
    (r'consists of 29 files that start from', r'consists of 30 files that start from'),
    (r'all 2728 declarations', r'all %s declarations' % DECLS),
    (ROW46,
     r'Theorem~\ref{thm:gfxy}, Lemma~\ref{lem:coef} & \lean{Gxy\_zero}, \lean{Gxy\_rec}, \lean{Gxy\_prod}, '
     r'\lean{coef\_formula\_xy}\\' '\n' + ROW46),
    (r'the block decomposition (Theorem~\ref{thm:blocks}), the generating function of Theorem~\ref{thm:gfxy} and the '
     r'bijection of Proposition~\ref{prop:bijection} (the formal proof of Theorem~\ref{thm:explicit} goes through the '
     r'recurrence instead, refined by ascents); in Lemma~\ref{lem:coef}, the refinement by $y$ of the coefficient formula '
     r'(the case $y=1$ is formalized) and the identification of $H(m,s,j)$ with $r$-Stirling numbers for $j\ge1$;',
     r'the block decomposition (Theorem~\ref{thm:blocks}) and the bijection of Proposition~\ref{prop:bijection} (the '
     r'formal proofs of Theorems~\ref{thm:gfxy} and~\ref{thm:explicit} go through the recurrence instead, refined by '
     r'ascents); in Lemma~\ref{lem:coef}, the identification of $H(m,s,j)$ with $r$-Stirling numbers for $j\ge1$;'),
]

GUIDE = [
    (r'Corollary 3.4, the explicit formula (Theorem 4.6, through a refined recurrence),',
     r'Corollary 3.4, the generating function in $x$ and $y$ and the coefficient formula (Theorem 4.4, Lemma 4.5) and '
     r'the explicit formula (Theorem 4.6), through a refined recurrence,'),
    (r'Theorems 4.2 and 4.4, the refinement in Lemma 4.5 and the bijection of Proposition 4.7 (the formal proof of '
     r'Theorem 4.6 avoids them).',
     r'Theorem 4.2, the identification with $r$-Stirling numbers in Lemma 4.5 and the bijection of Proposition 4.7 (the '
     r'formal proofs of Theorems 4.4 and 4.6 avoid them).'),
]

README = [
    ('共 29 个模块（2026-10-07 全量构建 26 个，同日又加 `NotStirlingLike.lean`，2026-10-10 加 `Saturated.lean` 与 '
     '`ThreeTerm.lean`）',
     '共 30 个模块（2026-10-07 全量构建 26 个，同日又加 `NotStirlingLike.lean`，2026-10-10 加 `Saturated.lean`、'
     '`ThreeTerm.lean` 与 `GenFunXY.lean`）'),
    ('2728 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、推论 5.5 与推论 5.7 后由 2675 增加；',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、推论 5.5、推论 5.7、定理 4.4 与引理 4.5 的'
     '按 y 细化后由 2675 增加；' % DECLS),
    ('（补丁 `patch_paper_2026-10-10_lean_threeterm.py`）。',
     '（补丁 `patch_paper_2026-10-10_lean_threeterm.py`）。第五项（比原定的定理 6.1 简单，按「先做最简单的」提前）：'
     '定理 4.4（按上升数细化的二元母函数）与引理 4.5 的按 y 细化，新模块 `GenFunXY.lean`：`Gxy_zero`、`Gxy_rec`'
     '（b_{m+1}·G_{m+1} = G_m + (m+1)·y·x²）、`Gxy_prod`（第二式乘掉分母）、`coef_formula_xy`（∏_{v=j}^{m} b_v⁻¹ 的 '
     'xⁿyˢ 系数是 H(m,s,j)·C(n+m−j−2s, n−3s)）；G_m 写成 ℚ⟦y⟧⟦x⟧ 的元素。论文用块分解证明定理 4.4，Lean 走按上升数'
     '细化的引理 1，与 y = 1 的 `G_rec` 同一路线。编译一次通过（改注释里的定理编号后重编一次）；根模块、Axioms（268 条，'
     '全量扫描 %s 个声明，只有三条标准公理）与 Checks 通过，`check_lean_fresh.py` %s PASS'
     '（补丁 `patch_paper_2026-10-10_lean_genfunxy.py`）。' % (DECLS, FRESH)),
]

CHECKLIST = [
    ('| 6.2 | Kauers 定义到 Lean 定理的书面论证 | ✓ | 不在 Lean 中。',
     '| 6.2 | Kauers 定义到 Lean 定理的书面论证 | ✓ | 2026-10-10 起推论 5.7（分母乘掉、对 U 的任意延拓）已在 Lean 中'
     '（`ThreeTerm.lean`），剩下取公分母与从 Kauers 定义到「生成元零化延拓」两步仍不在 Lean 中。以下是 10-08 的核对：'),
    ('`check_lean_fresh.py` 37 项全部 PASS（`logs/check_lean_fresh_2026-10-10_three.log`）。',
     '`check_lean_fresh.py` 37 项全部 PASS（`logs/check_lean_fresh_2026-10-10_three.log`）。同日第五项：新模块 '
     '`GenFunXY.lean`（论文定理 4.4 与引理 4.5 的按 y 细化；新定义 `Gxy`（G_m(x,y) 的系数是 `Us k m s`）与 `bxy`'
     '（b_v = 1 − x − v·y·x³）由 AI 对照论文核对，`Us`、`asc`、`hc`、`vars` 沿用 `Ascent.lean`、`Formula.lean`，'
     '不在上面 18 项里），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（268 条，%s 个声明，只有三条'
     '标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_genfun.log`）。'
     % (DECLS, FRESH)),
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
    print('declarations:', DECLS)
    patch(os.path.join(ROOT, 'paper', 'main.tex'), PAPER)
    patch(os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), GUIDE)
    patch(os.path.join(ROOT, 'README.md'), README)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)


if __name__ == '__main__':
    main()
