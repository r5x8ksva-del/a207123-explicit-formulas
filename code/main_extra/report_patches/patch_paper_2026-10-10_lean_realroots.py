# -*- coding: utf-8 -*-
r"""Lean 续作第十九项（2026-10-10）：论文第 8 节命题 8.10（四个交错关系）与「每个 n_k 只有实根」的形式化，
新模块 `lean/A207123/Interlace.lean`（交错的工具）与 `lean/A207123/RealRoots.lean`（应用）：
- 交错 `g ≪ f` 按论文给出的等价刻画定义（对每个 x，f 在 (x,∞) 中的根比 g 多 0 或 1 个，计重数）；
  引理 8.4（`interlaces_mul_iff`）、引理 8.6（`Interlaces.add_left`、`Interlaces.add_right`）、引理 8.7(1)(2)
  （`interlaces_X_sub_C_mul`、`interlaces_derivative`、`Interlaces.X_mul`）。引理 8.5（上半平面的虚部刻画）与
  引理 8.7(3)（导数保持交错）没有形式化：形式证明改用锥的表示 g = c·f + Σ_a w_a·f/(z−a)（c, w_a ≥ 0，a 取 f 的
  不同根；`cone_of_interlaces`、`interlaces_coneSum` 及上锥的两条），只用介值定理与插值。
- 引理 8.8（`lemma_il_T_one`、`Interlaces.opTz`、`Interlaces.opPsiz`、`interlaces_one_add_X_mul_opTz`、
  `opTz_one_add_X_mul`；(2) 由 𝒟f = (z−a)·𝒟(f/(z−a)) + (1+z)·f/(z−a) 与引理 8.6 得到）、引理 8.9（`nR_rec`）、
  命题 8.10（`prop_four_relations`、`alpha_two`、`beta_two`），以及定理 8.1 第一句中「n_k 的根都是实数」
  （`realRooted_nR`、`nrowPoly_root_im_eq_zero`）。单根、h_k 的那半句、推论 8.2 及其后各条（推论 8.15 与引理 8.12
  中已形式化的部分除外）仍未形式化。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_realroots.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 在定理 7.1 一行之后加三行；
  「Not formalized」里第 8 节一句改为列出仍未形式化的部分，并说明引理 8.8(2) 的形式证明绕开了引理 8.5 与 8.7(3)；
  「只由 AI 核对的定义」一句加上 g ≪ f；为保持 38 页、无警告，表 5 行距 0.96 改 0.90，并去掉 \appendix 前的
  \clearpage（附录 A 改为接在第 10 节之后，从第 31 页开始；附录 B 与参考文献的起始页不变）。
- paper/reviewer_guide.tex：第 2 节加第 8 节已形式化的部分；第 3 节 Section 8 一条改写。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_realroots.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_realroots.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '53'

ROW_MINUS = r'Lemma~\ref{lem:minusone}, except the sign of $\lambda_k$ & '
ROWS_NEW = (
    r'Lemmas~\ref{lem:il-factor}, \ref{lem:il-sum}, \ref{lem:il-ops}(1)(2) & \lean{interlaces\_mul\_iff}, '
    r'\lean{Interlaces.add\_left}, \lean{Interlaces.add\_right}, \lean{interlaces\_X\_sub\_C\_mul}, '
    r'\lean{interlaces\_derivative}, \lean{Interlaces.X\_mul}\\' + '\n'
    r'Lemmas~\ref{lem:il-T}, \ref{lem:rowrec} & \lean{lemma\_il\_T\_one}, \lean{Interlaces.opTz}, '
    r'\lean{Interlaces.opPsiz}, \lean{interlaces\_one\_add\_X\_mul\_opTz}, \lean{opTz\_one\_add\_X\_mul}, '
    r'\lean{nR\_rec}\\' + '\n'
    r'Proposition~\ref{prop:four}, Theorem~\ref{thm:realroots} & \lean{prop\_four\_relations}, \lean{alpha\_two}, '
    r'\lean{beta\_two}; zeros of $n_k$ real: \lean{realRooted\_nR}, \lean{nrowPoly\_root\_im\_eq\_zero}\\' + '\n')
PAPER = [
    ('\n' + ROW_MINUS, '\n' + ROWS_NEW + ROW_MINUS),
    (r'Section~\ref{sec:short}; and Section~\ref{sec:realroots}, apart from Corollary~\ref{cor:negzeros} and the '
     r'statements about $a_k$, $\deg h_k$ and the sign of the leading coefficient of $h_k$ in '
     r'Lemma~\ref{lem:minusone}.',
     r'Section~\ref{sec:short}; and in Section~\ref{sec:realroots} Lemmas~\ref{lem:il-pick} and~\ref{lem:il-ops}(3) '
     r'(the formal proof of Lemma~\ref{lem:il-T}(2) writes $g\ll f$ as $g=cf+\sum_aw_a\,f/(z-a)$ with $c,w_a\ge0$ '
     r'instead), Proposition~\ref{prop:simple}, hence the simplicity of the zeros and the statement about $h_k$ in '
     r'Theorem~\ref{thm:realroots}, Corollary~\ref{cor:logconcave}, the sign of $\lambda_k$ in '
     r'Lemma~\ref{lem:minusone}, Corollaries~\ref{cor:hk-signs} and~\ref{cor:clt}, and Remark~\ref{rem:chains}.'),
    # 形式定义 `Interlaces` 取论文定义之后给出的计数刻画：记进「只由 AI 核对的定义」一句
    (r'of $c_m$ and $\tau_m$ and of the value of a rational function at a point, are documented',
     r'of $c_m$ and $\tau_m$, of the value of a rational function at a point and of $g\ll f$ (by the '
     r'characterization after its definition), are documented'),
    # 表 5 多了三行（约 6 行字），第 10 节在第 30 页表下放不下（第 31 页只剩第 10 节、附录 A 移到第 32 页，共 39 页，
    # 第 29、30 页各一条 underfull \vbox）。表 5 行距 0.96 改 0.90，并去掉第十一项在 \appendix 前加的 \clearpage
    # （当时为避免附录 A 的标题被挤到下一页）：第 30 页排表 5 与第 10 节 (2)(3)，第 31 页排 (4) 后接附录 A，
    # 仍 38 页、无警告，附录 B（33）与参考文献（37）的起始页不变
    ('\\renewcommand{\\arraystretch}{0.96}', '\\renewcommand{\\arraystretch}{0.90}'),
    ('% =====================================================================\n\\clearpage\n\\appendix\n',
     '% =====================================================================\n\\appendix\n'),
]
PAPER_RE = [
    (r'consists of 43 files that start from', 'consists of 45 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('the near-diagonal theorem (Theorem 7.1, Proposition 7.2), Corollary 8.15 and part of Lemma 8.12.',
     'the near-diagonal theorem (Theorem 7.1, Proposition 7.2), Lemmas 8.4, 8.6, 8.8, 8.9 and Proposition 8.10 '
     '(so all zeros of every $n_k$ are real), Corollary 8.15 and part of Lemma 8.12.'),
    ('(blocks, $c_m$, $\\tau_m$, values of rational functions)',
     '(blocks, $c_m$, $\\tau_m$, values of rational functions, interlacing)'),
    ('Lemmas 8.4--8.7 collect standard interlacing facts, and Lemma 8.8 applies them to the operators $\\mathcal D$, '
     '$\\mathcal T$ and $\\Psi$ of the recurrence. The core is Lemma 8.9 (the recurrence for the row polynomials), '
     'Proposition 8.10 (four interlacing relations propagate along the recurrence), Proposition 8.11 (simplicity of '
     'the zeros) and Lemma 8.12',
     'Proposition 8.10 and the real-rootedness of the $n_k$ are formalized, by a route that replaces Lemmas 8.5 and '
     '8.7(3) (upper half-plane, Gauss--Lucas) with $g=cf+\\sum_aw_af/(z-a)$. Not formalized: Lemmas 8.5 and 8.7(3) '
     'themselves, Proposition 8.11 (simplicity of the zeros, hence the rest of Theorem 8.1), Corollary 8.2 and '
     'Lemma 8.12'),
]

README = [
    ('`OeisRowOrders.lean`、`RStirling.lean` 与 `Bijection.lean`）',
     '`OeisRowOrders.lean`、`RStirling.lean`、`Bijection.lean`、`Interlace.lean` 与 `RealRoots.lean`）'),
    ('共 43 个模块（', '共 45 个模块（'),
    ('命题 4.7（双射的存在）与注记 5.2 后由 2675 增加',
     '命题 4.7（双射的存在）、注记 5.2 与命题 8.10（行多项式只有实根，含引理 8.4、8.6、8.8、8.9）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_bijection.py`。',
     '补丁 `patch_paper_2026-10-10_lean_bijection.py`。第十九项：论文第 8 节命题 8.10 与「每个 n_k 只有实根」，'
     '新模块 `Interlace.lean`（交错 `g ≪ f` 按论文给出的等价刻画定义：对每个 x，f 在 (x,∞) 中的根比 g 多 0 或 1 '
     '个；引理 8.4、8.6、8.7(1)(2)；论文用上半平面虚部证的引理 8.5 与 8.7(3) 改用锥的表示 '
     '`g = c·f + Σ_a w_a·f/(z−a)`（`cone_of_interlaces`、`interlaces_coneSum` 及上锥的两条），只用介值定理与插值）'
     '与 `RealRoots.lean`（引理 8.8：`lemma_il_T_one`、`Interlaces.opTz`、`Interlaces.opPsiz`、'
     '`interlaces_one_add_X_mul_opTz`、`opTz_one_add_X_mul`；引理 8.9：`nR_rec`；命题 8.10：`prop_four_relations`、'
     '`alpha_two`、`beta_two`，初值按显式的根逐点数根；`realRooted_nR`、`nrowPoly_root_im_eq_zero`）。单根（命题 8.11）、'
     'h_k 的那半句与推论 8.2 等仍未形式化。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；'
     '`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_realroots.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_bijection.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_bijection.log`）。同日第十九项：新模块 `Interlace.lean` 与 '
     '`RealRoots.lean`（论文第 8 节命题 8.10 与「每个 n_k 只有实根」；新定义 `nAbove`、`RealRooted`、`Interlaces`、'
     '`coneSum`、`uconeSum`、`InCone`、`nR`、`opDz`、`opTz`、`opPsiz` 由 AI 核对：`Interlaces` 取论文定义后给出的计数刻画，'
     '`nR k` 与 `HStruct.lean` 的 `nrowPoly k` 相差系数域的映射（`nR_eq_map`）；主陈述 `realRooted_nR`、'
     '`nrowPoly_root_im_eq_zero` 只用到 `N`、`nrowPoly` 与 Mathlib 的 `roots`、`aeval`），经 `lean/lean_one.sh` 编译、'
     '重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` '
     '%s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_realroots.log`）。' % (_ax, DECLS, FRESH)),
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
