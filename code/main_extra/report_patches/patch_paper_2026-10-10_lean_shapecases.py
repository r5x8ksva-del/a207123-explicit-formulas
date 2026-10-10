# -*- coding: utf-8 -*-
r"""Lean 续作第三十项（2026-10-10）：论文定理 6.3 的情形分析与主定理（单族二项式形状的分类），新模块
`lean/A207123/ShapeNT.lean` 与 `lean/A207123/ShapeCases.lean`：
- ShapeNT：X³ + X − 1 在 ℚ 上不可约（`irreducible_fQ`），次数 ≤ 2 的有理系数多项式在它的根处为 0 只能是零多项式
  （`eq_zero_of_aeval_root_b1`、`quad_rel_root_b1`），有理系数多项式在一个根处为 0 则在每个根处为 0
  （`aeval_root_b1_eq_zero`），实根 ξ ∈ (2/3, 1) 与复根 ξ₂（|ξ₂|² = ξ² + 1），N ≥ 1 时 ξ^N ∉ ℚ（`real_root_pow_not_rat`，
  不用范数）。
- ShapeCases：`thm_shapes`（m ≥ 1、α, β ≥ 0 不全为 0 时 `ShapeRep (U · m) α β ↔ α + β = 1`）；`shape_01`、`shape_10`
  （α + β = 1 的两种形状）、`not_shape_21`（由 `thm_S`）、`not_shape_a`、`not_shape_b`、`not_shape_c`、`not_shape_d`
  （其余形状，用上一项 `ShapeFibre.lean` 的纤维引理）。β = 0 与 α = 0、β 奇两种情形的形式证明换了论证：不用
  「ℚ(ξ) 不正规」与「三次域没有二次子域」，改用共轭根的韦达关系与模的比较。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_shapecases.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；表 5 定理 6.1、6.2 一行改为定理 6.1–6.3；「Not formalized」改为第 6 节除
  定理 6.1–6.3 外；只经 AI 对照的定义里「定理 6.1 的二项式约定」改为「定理 6.1–6.3 的和」（包含二项式约定与
  `ShapeRep`）。第 29 页已排满，草稿目录用 code/main_extra/try_layout.py 试了三种写法，取不加长的这一种。
- paper/reviewer_guide.tex：第 2 节定理 6.1、6.2 一句改为定理 6.1–6.3，只经 AI 对照的定义加上定理 6.3 的和；
  第 3 节 Section 6 一条改写（定理 6.1–6.3 都已形式化，人工核对的重点是定理 6.5）。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A12、A20 的完成度与 Lean 一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_shapecases.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_shapecases.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '65'

PAPER = [
    (r'Theorems~\ref{thm:S}, \ref{thm:Spart}, other proof & \lean{thm\_S}, \lean{thm\_Spart}, '
     r'\lean{substU\_coords\_unique}, \lean{single\_sum\_cross}, \lean{no\_common\_value}, '
     r'\lean{no\_common\_value\_b2}\\',
     r'Theorems~\ref{thm:S}--\ref{thm:shapes}, other proof & \lean{thm\_S}, \lean{thm\_Spart}, \lean{thm\_shapes}, '
     r'\lean{substU\_coords\_unique}, \lean{single\_sum\_cross}, \lean{shape\_fibre\_x}, \lean{shape\_fibre\_y}, '
     r'\lean{no\_common\_value}, \lean{no\_common\_value\_b2}\\'),
    (r'; and Section~\ref{sec:short} except Theorems~\ref{thm:S}, \ref{thm:Spart}. ',
     r'; and Section~\ref{sec:short} except Theorems~\ref{thm:S}--\ref{thm:shapes}. '),
    # 第 29 页已排满：「the binomial convention and the sums in Theorems 6.1–6.3」会把第 10 节标题挤到下一页
    # （try_layout 的 v3），「the sums in Theorems 6.1–6.3」不加长（v1）
    (r'and of the binomial convention in Theorem~\ref{thm:S}, are documented',
     r'and of the sums in Theorems~\ref{thm:S}--\ref{thm:shapes}, are documented'),
]
PAPER_RE = [
    (r'consists of 55 files that start from', 'consists of 57 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    (r'Theorems 6.1 and 6.2 (no single sum $\sum_sA(s)\binom{k+c-2s}{m+s+d}$ for $U_k(m)$, nor for the sequences '
     r"ending with an ascent; the formal proofs use coordinates with respect to $1,x,x^2$ and Vieta's formulas instead "
     r'of residues and norms), and the near-diagonal theorem',
     r'Theorems 6.1--6.3 (no single sum $\sum_sA(s)\binom{k+c-2s}{m+s+d}$ for $U_k(m)$, nor for the sequences '
     r'ending with an ascent; of the shapes $\binom{k+c-\alpha s}{\beta s+d}$ with $\alpha,\beta\ge0$ only '
     r'$\alpha+\beta=1$ occurs; the formal proofs use coordinates with respect to $1,y,\dots,y^{\alpha+\beta-1}$ and '
     r"Vieta's formulas instead of residues, poles and norms), and the near-diagonal theorem"),
    (r'the binomial convention of Theorem 6.1, the sequences ending with an ascent in Theorem 6.2) are in the Lean '
     r'files',
     r'the binomial convention of Theorem 6.1, the sequences ending with an ascent in Theorem 6.2, the sums in '
     r'Theorem 6.3) are in the Lean files'),
    (r'\item \textbf{Section 6, obstructions (pp.~16--22).} Theorem 6.3 uses residues on fibres and norms in number '
     r'fields; so do the written proofs of Theorems 6.1 and 6.2, which are formalized by another route. Theorem 6.5 '
     r"(two single sums) is computer-assisted: a sieve modulo $5040$ and Skolem's $p$-adic method (Propositions "
     r'6.8--6.10, Lemma 6.11); the scripts are in the repository.',
     r'\item \textbf{Section 6, obstructions (pp.~16--22).} Theorem 6.5 (two single sums) is computer-assisted: a '
     r"sieve modulo $5040$ and Skolem's $p$-adic method (Propositions 6.8--6.10, Lemma 6.11); the scripts are in the "
     r'repository. The written proofs of Theorems 6.1--6.3 use residues or poles on fibres and norms in number '
     r'fields; the theorems are formalized by another route.'),
]

README = [
    ('`SingleSum.lean`、`SingleSumAsc.lean` 与 `ShapeFibre.lean`）',
     '`SingleSum.lean`、`SingleSumAsc.lean`、`ShapeFibre.lean`、`ShapeNT.lean` 与 `ShapeCases.lean`）'),
    ('共 55 个模块（', '共 57 个模块（'),
    ('、定理 6.1、6.2（没有 (2,1) 形状的单族和）与定理 6.3 证明的第 1–3 步后由 2675 增加',
     '与定理 6.1–6.3（没有 (2,1) 形状的单族和；非负参数的单族二项式形状只有 α+β = 1 的）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_shapefibre.py`。',
     '补丁 `patch_paper_2026-10-10_lean_shapefibre.py`。第三十项：论文定理 6.3 的情形分析与主定理，新模块 '
     '`ShapeNT.lean`（X³ + X − 1 的数论：`irreducible_fQ` 在 ℚ 上不可约（没有有理根）；`quad_rel_root_b1`：ξ 不满足'
     '非零的有理二次关系；`aeval_root_b1_eq_zero`：有理系数多项式在一个根处为 0 则在每个根处为 0；'
     '`real_root_pow_not_rat`：N ≥ 1 时 ξ^N ∉ ℚ，论文用范数，这里把 X^N − q 对 X³ + X − 1 取余后搬到复根 ξ₂ 上，'
     '|ξ₂| > 1 > ξ）与 `ShapeCases.lean`（`thm_shapes`：m ≥ 1、α, β ≥ 0 不全为 0 时 '
     '`ShapeRep (fun k => U k m) α β ↔ α + β = 1`；(0,1) 是 Newton 前向差分公式（Mathlib 的 '
     '`shift_eq_sum_fwdDiff_iter`），(1,0) 是差分逐项求和，(2,1) 由 `thm_S`；其余形状用上一项的纤维引理：'
     '`not_shape_a`（α, β ≥ 1、α ≠ 2β：纤维多项式的根之积，同论文）、`not_shape_b`（β = 0：论文用「分圆域是 Abel '
     '扩张而 ℚ(ξ) 不正规」，这里 z = ξζ 不是实数时 z、z̄ 都是 b_w 的根，韦达关系化成 ξ 的有理二次关系，只能 w = 0）、'
     '`not_shape_c`（α = 2β ≥ 4，同论文）、`not_shape_d`（α = 0：β 偶同论文；β 奇时论文用「三次域没有二次子域」'
     '得 χ(ξ) ∈ ℚ，这里由 χ(ξ)² ∈ ℚ 直接得 χ(ξ₂)² = χ(ξ)²，再比较模））。Axioms %d 条，全量扫描 %s 个声明，只有'
     '三条标准公理；`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_shapecases.py`。'
     % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_shapefibre.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_shapefibre.log`）。同日第三十项：新模块 `ShapeNT.lean` 与 `ShapeCases.lean`'
     '（论文定理 6.3 的情形分析与主定理 `thm_shapes`；没有新的承重定义：陈述只用 `U` 与上一项的 `ShapeRep`（AI 核对）；'
     '`fQ` 只在证明里用），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条'
     '标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_shapecases.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('| ■■■■□（定理 S 与 (ii) ■■■■■） |', '| ■■■■■ |'),
    ('三个根上的韦达关系，(ii) 再加 17 进赋值），S′ 与其他形状未形式化 |',
     '三个根上的韦达关系，(ii) 再加 17 进赋值）；S′ 与其他形状（论文定理 6.3）同日也已形式化（`ShapeCases.lean` 的 '
     '`thm_shapes`，见 A20） |'),
    ('是唯一要靠留数与范数的形状 | ■■■■□ |', '是唯一要靠留数与范数的形状 | ■■■■■ |'),
    ('Lean：证明的第 1–3 步（母函数、坐标、纤维上每一点都是 P_m 的根）2026-10-10 已形式化（`ShapeFibre.lean` 的 '
     '`shape_fibre_x`、`shape_fibre_y`），情形分析尚未形式化；α<0 的形状不在范围内。',
     'Lean：2026-10-10 已完整形式化（`ShapeCases.lean` 的 `thm_shapes`）。第 1–3 步在 `ShapeFibre.lean`（纤维上每一点'
     '都是 P_m 的根；论文用极点，这里用坐标的交叉关系）；情形分析在 `ShapeCases.lean`：β=0 时不用「Q(ξ) 不正规」，'
     '改用 z、z̄ 两个根的韦达关系化成 ξ 的有理二次关系；α=0、β 奇时不用「三次域没有二次子域」，改用 '
     'χ(ξ₂)² = χ(ξ)² 与模的比较；ξ^N ∉ Q 用对 X³+X−1 取余与复根的模，不用范数（`ShapeNT.lean`）。α<0 的形状不在'
     '范围内。'),
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
    patch(os.path.join(ROOT, '猜想总表.md'), TABLE)


if __name__ == '__main__':
    main()
