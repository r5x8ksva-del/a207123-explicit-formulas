# -*- coding: utf-8 -*-
r"""Lean 续作第四项（2026-10-10）：论文推论 5.7 与注 5.8 形式化（分母乘掉的形式），新模块 `lean/A207123/ThreeTerm.lean`：
  `not_annihilate_three_terms`（v_i 两两不同、|det|≤2、分子 n_i 不全为 0、公分母 Δ≠0，则不存在整数象限，使得在其中
  Δ≠0 的每个点上 Σ n_i(k,m)·f(k+s_i, m+t_i) = 0；f 是 U 在 ℤ² 上的任意延拓，所以也覆盖注 5.8 的论证）、
  `not_annihilate_two_terms`（至多两项）、`not_annihilate_kauers`（Kauers 定义 3 的生成元形状，|v₁w₂−v₂w₁|=1）。
  根模块加 import，Axioms 加三条（共 264 条），全量扫描 2728 个声明（含编译器自动生成的辅助声明）。
本补丁同步：
- paper/main.tex：第 9 节文件数 28 → 29、声明数 2682 → 2728；表 5 在命题 5.6 一行之后加推论 5.7 一行；
  「Not formalized」里推论 5.5 一项改为推论 5.5、5.7 两者与分母乘掉的形式之间的换算，推论 5.7 与注 5.8 一项改为
  注 5.8 里从 Kauers 定义到「三项算子零化延拓」这一步；注 5.8 末两句改写；附录 A 开头的文件清单加 ThreeTerm.lean，
  「Supports」小节末尾抄录 `not_annihilate_three_terms` 的陈述。
- code/main_extra/check_appendix_lean.py：TeX → Lean 的对照表加 `\(\Z\times\Z\)` 与 `\(\Delta\)`。
- paper/reviewer_guide.tex：第 2 节加上推论 5.7（分母乘掉的形式）；第 3 节第 4 条改为注 5.8 与取公分母两步。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_threeterm.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

ROW56 = (r'Proposition~\ref{prop:triangle} & \lean{relU\_support\_det}, \lean{relU\_card\_support}, '
         r'\lean{not\_mem\_relU\_of\_support\_subset}\\' '\n')
NORMOP = r'Here \lean{normOp r} is the operator $\sum_{(a,b)}r(a,b)X^aE^{-b}$ with finitely supported coefficients.' '\n'
TRANSCRIPT = (
    r'Corollary~\ref{cor:stirlinglike} is formalized in \lean{ThreeTerm.lean} as follows: \lean{f} is an arbitrary '
    r'extension of $U$ to $\Z^2$, $v_i=(s_i,t_i)$, the coefficients are $n_i/\Delta$, and \lean{p.evalEval x y} is the '
    r'value at $(x,y)$ of a polynomial \lean{p} in $(k,m)$.' '\n'
    r'\begin{alltt}\small' '\n'
    r'theorem not_annihilate_three_terms (f : \(\Z\) \(\to\) \(\Z\) \(\to\) \(\C\))' '\n'
    r'    (hf : \(\forall\) k m : \(\NN\), f k m = U k m)' '\n'
    r'    \{v0 v1 v2 : \(\Z\times\Z\)\} (h01 : v0 \(\ne\) v1) (h02 : v0 \(\ne\) v2) (h12 : v1 \(\ne\) v2)' '\n'
    r'    (hdet : |(v1.1 - v0.1) * (v2.2 - v0.2) - (v1.2 - v0.2) * (v2.1 - v0.1)| \(\le\) 2)' '\n'
    r'    \{n0 n1 n2 \(\Delta\) : Coef\} (hn : n0 \(\ne\) 0 \(\lor\) n1 \(\ne\) 0 \(\lor\) n2 \(\ne\) 0)' '\n'
    r'    (h\(\Delta\) : \(\Delta\) \(\ne\) 0) (k0 m0 : \(\Z\)) :' '\n'
    r'    \(\lnot\) \(\forall\) k m : \(\Z\), k0 \(\le\) k \(\to\) m0 \(\le\) m \(\to\) '
    r'\(\Delta\).evalEval (k : \(\C\)) (m : \(\C\)) \(\ne\) 0 \(\to\)' '\n'
    r'      n0.evalEval (k : \(\C\)) (m : \(\C\)) * f (k + v0.1) (m + v0.2)' '\n'
    r'        + n1.evalEval (k : \(\C\)) (m : \(\C\)) * f (k + v1.1) (m + v1.2)' '\n'
    r'        + n2.evalEval (k : \(\C\)) (m : \(\C\)) * f (k + v2.1) (m + v2.2) = 0' '\n'
    r'\end{alltt}' '\n'
)

PAPER = [
    (r'consists of 28 files that start from', r'consists of 29 files that start from'),
    (r'all 2682 declarations', r'all 2728 declarations'),
    (ROW56,
     ROW56 + r'Corollary~\ref{cor:stirlinglike} & \lean{not\_annihilate\_three\_terms}, \lean{not\_annihilate\_two\_terms}, '
     r'\lean{not\_annihilate\_kauers} (with denominators cleared)\\' '\n'),
    (r"the passage between Corollary~\ref{cor:saturated}, which is stated for operators with rational coefficients, and "
     r"the formalized version with denominators cleared; Corollary~\ref{cor:stirlinglike} and Remark~\ref{rem:kauers}, "
     r"which lead from Kauers' definition to Proposition~\ref{prop:triangle};",
     r"the passage between Corollaries~\ref{cor:saturated} and~\ref{cor:stirlinglike}, which are stated for operators "
     r"with rational coefficients, and their formalized versions with denominators cleared; the step in "
     r"Remark~\ref{rem:kauers} from Kauers' definition to the annihilation of an extension of $U$ by a three-term "
     r"operator;"),
    (r'In this subsection only Proposition~\ref{prop:triangle} is formalized. The passage from '
     r'\cite[Definition~3]{Kauers07} to it, that is, the reduction in the proof of Corollary~\ref{cor:stirlinglike} '
     r'together with the argument above, is not.',
     r'Proposition~\ref{prop:triangle} and Corollary~\ref{cor:stirlinglike} are formalized. In the formal version of '
     r'the corollary (Appendix~\ref{app:lean}) the coefficients are written as $n_i/\Delta$ with polynomials $n_i$ and '
     r'$\Delta\ne0$, the relation is assumed only at the points of a quadrant in $\Z^2$ where $\Delta\ne0$, and $U$ may '
     r'be replaced by any extension to $\Z^2$; so it also covers the argument above. Not formalized are the choice of a '
     r'common denominator and the step from \cite[Definition~3]{Kauers07} to the annihilation of an extension by its '
     r'three-term generator.'),
    (r'\lean{OreRel.lean} and \lean{NotStirlingLike.lean}.',
     r'\lean{OreRel.lean}, \lean{NotStirlingLike.lean} and \lean{ThreeTerm.lean}.'),
    (NORMOP, NORMOP + TRANSCRIPT),
]

CHECKER = [
    (r"(r'\(\NN\times\NN\)', 'ℕ × ℕ'), ",
     r"(r'\(\NN\times\NN\)', 'ℕ × ℕ'), (r'\(\Z\times\Z\)', 'ℤ × ℤ'), "),
    (r"(r'\(\sigma\)', 'σ'), ",
     r"(r'\(\sigma\)', 'σ'), (r'\(\Delta\)', 'Δ'), "),
]

GUIDE = [
    (r'Corollary 5.5 (with denominators cleared), Proposition 5.6, and the near-diagonal theorem',
     r'Corollary 5.5 (with denominators cleared), Proposition 5.6, Corollary 5.7 (with denominators cleared), and the '
     r'near-diagonal theorem'),
    (r"\item \textbf{Section 5:} Corollary 5.7 with Remark 5.8, which lead from Kauers' definition of Stirling-like "
     r"sequences to the formalized Proposition 5.6.",
     r"\item \textbf{Section 5:} Remark 5.8, the step from Kauers' definition of Stirling-like sequences to the "
     r"formalized Corollary 5.7, and the choice of a common denominator in Corollaries 5.5 and 5.7."),
]

README = [
    ('共 28 个模块（2026-10-07 全量构建 26 个，同日又加 `NotStirlingLike.lean`，2026-10-10 加 `Saturated.lean`）',
     '共 29 个模块（2026-10-07 全量构建 26 个，同日又加 `NotStirlingLike.lean`，2026-10-10 加 `Saturated.lean` 与 '
     '`ThreeTerm.lean`）'),
    ('2682 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句与推论 5.5 后由 2675 增加）',
     '2728 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、推论 5.5 与推论 5.7 后由 2675 增加；'
     '扫描把编译器自动生成的辅助声明也算在内）'),
    ('`check_lean_fresh.py` 36 PASS（补丁 `patch_paper_2026-10-10_lean_saturated.py`）。',
     '`check_lean_fresh.py` 36 PASS（补丁 `patch_paper_2026-10-10_lean_saturated.py`）。第四项：推论 5.7 形式化'
     '（分母乘掉的形式），新模块 `ThreeTerm.lean`：`not_annihilate_three_terms`（v_i 两两不同、|det|≤2、分子 n_i '
     '不全为 0、公分母 Δ≠0，则不存在整数象限，使得在其中 Δ≠0 的每个点上 Σ n_i(k,m)·f(k+s_i,m+t_i)=0；f 是 U 在 ℤ² '
     '上的任意延拓，所以也覆盖注 5.8 的论证）、`not_annihilate_two_terms`（至多两项）、`not_annihilate_kauers`'
     '（Kauers 定义 3 的生成元形状，|v₁w₂−v₂w₁|=1）；证明照论文：平移到 ℕ²、乘公分母，再用命题 5.6。仍是书面的：取公分母，'
     '以及从 Kauers 定义到「生成元零化延拓」这一步。编译一次通过；根模块、Axioms（264 条，全量扫描 2728 个声明，只有三条'
     '标准公理；比上次多 46 个，写的是 7 个，其余是编译器自动生成的辅助声明）与 Checks 都通过，`check_lean_fresh.py` '
     '37 PASS；论文附录 A 抄录了 `not_annihilate_three_terms` 的陈述，由 `check_appendix_lean.py` 对照源码'
     '（补丁 `patch_paper_2026-10-10_lean_threeterm.py`）。'),
]

CHECKLIST = [
    ('`check_lean_fresh.py` 36 项全部 PASS（`logs/check_lean_fresh_2026-10-10_sat.log`）。',
     '`check_lean_fresh.py` 36 项全部 PASS（`logs/check_lean_fresh_2026-10-10_sat.log`）。同日第四项：新模块 '
     '`ThreeTerm.lean`（论文推论 5.7 与注 5.8，分母乘掉的形式；陈述只用到 `U`、`Coef` 与多项式取值 `evalEval`，'
     '`f` 是 `U` 在 ℤ² 上的任意延拓；陈述由 AI 对照论文核对，并抄进论文附录 A，由 `check_appendix_lean.py` 对照源码），'
     '经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（264 条，2728 个声明，只有三条标准公理）与 '
     '`Checks.lean`，`check_lean_fresh.py` 37 项全部 PASS（`logs/check_lean_fresh_2026-10-10_three.log`）。'),
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
    patch(os.path.join(ROOT, 'code', 'main_extra', 'check_appendix_lean.py'), CHECKER)
    patch(os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), GUIDE)
    patch(os.path.join(ROOT, 'README.md'), README)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)


if __name__ == '__main__':
    main()
