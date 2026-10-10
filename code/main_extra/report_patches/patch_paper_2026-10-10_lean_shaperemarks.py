# -*- coding: utf-8 -*-
r"""Lean 续作第三十一项（2026-10-10）：论文第 6.1 节其余的断言，新模块 `lean/A207123/ShapeRemarks.lean`，并把
`ShapeCases.lean` 的 `shape_10`、`shape_01` 推广到任何数列（论文第 6 节开头：α + β = 1 的形状对每个数列都有表示）：
- `NA_single_sum`、`NA_excluded_form`：不以上升结尾的部分是定理 6.1 排除的形状，A(s) = S(m+s, m)；
  `U_zero_single_sum`：m = 0 时定理 6.1 的结论不成立。
- `NUp_explicit`（U^↑_k(m) 是定理 4.6 的第二个和）、`NUp_one_single_sum`、`NUp_one_excluded_form`：
  U^↑_k(1) = Σ_{s≥0} C(k−2−2s, s)，m = 1 时定理 6.2 的结论不成立。
- `ShapeRepZ`（α、β 取整数的表示）、`shapeRepZ_natCast`（α, β ≥ 0 时就是 `ShapeRep`）、`shape_neg`（注记 6.4 的
  第一句：α < 0、α + β = 1 时每个数列都有表示，系数由三角方程组 `triA` 逐个解出）、`shape_sum_one`（β ≥ 0、
  α + β = 1 的整数形状对每个数列都有表示）。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_shaperemarks.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；表 5 定理 6.1–6.3 一行改为第 6.1 节（加三个名字）；「Not formalized」改为
  第 6.2 节与注记 6.4 的最后两句；只经 AI 对照的定义改为「第 6.1 节的和」。草稿目录用 try_layout 试了三种写法，
  都是 39 页、无警告，取最准确的一种。
- paper/reviewer_guide.tex：第 2 节定理 6.1–6.3 一句改为第 6.1 节（除注记 6.4 的最后两句），只经 AI 对照的定义改为
  第 6.1 节的和。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A24 的 Lean 一句（β ≥ 0、α + β = 1 的方向已形式化）。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_shaperemarks.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_shaperemarks.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '66'

PAPER = [
    (r'Theorems~\ref{thm:S}--\ref{thm:shapes}, other proof & \lean{thm\_S}, \lean{thm\_Spart}, \lean{thm\_shapes}, '
     r'\lean{substU\_coords\_unique}, \lean{single\_sum\_cross}, \lean{shape\_fibre\_x}, \lean{shape\_fibre\_y}, '
     r'\lean{no\_common\_value}, \lean{no\_common\_value\_b2}\\',
     r'Section~\ref{sec:single}, other proof & \lean{thm\_S}, \lean{thm\_Spart}, \lean{thm\_shapes}, '
     r'\lean{substU\_coords\_unique}, \lean{single\_sum\_cross}, \lean{shape\_fibre\_x}, \lean{shape\_fibre\_y}, '
     r'\lean{no\_common\_value}, \lean{no\_common\_value\_b2}, \lean{NA\_single\_sum}, \lean{NUp\_one\_single\_sum}, '
     r'\lean{shape\_sum\_one}\\'),
    # 草稿目录 try_layout 的三种写法（只写第 6.2 节；第 6.2 节与注记 6.4 中 α+β≥2 的情形；第 6.2 节与注记 6.4 的
    # 最后两句）都是 39 页、无警告、第 10 节标题仍在第 29 页；取最后一种：注记 6.4 的最后两句说明 α<0、α+β≥2 时
    # 第 2 步为什么不成立，是没有形式化的断言
    (r'; and Section~\ref{sec:short} except Theorems~\ref{thm:S}--\ref{thm:shapes}. ',
     r'; Section~\ref{sec:twofam}; and the last two sentences of Remark~\ref{rem:othershapes}. '),
    (r'and of the sums in Theorems~\ref{thm:S}--\ref{thm:shapes}, are documented',
     r'and of the sums in Section~\ref{sec:single}, are documented'),
]
PAPER_RE = [
    (r'consists of 57 files that start from', 'consists of 58 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    (r'Theorems 6.1--6.3 (no single sum $\sum_sA(s)\binom{k+c-2s}{m+s+d}$ for $U_k(m)$, nor for the sequences '
     r'ending with an ascent; of the shapes $\binom{k+c-\alpha s}{\beta s+d}$ with $\alpha,\beta\ge0$ only '
     r'$\alpha+\beta=1$ occurs; the formal proofs',
     r'Section 6.1 except the last two sentences of Remark 6.4 (no single sum $\sum_sA(s)\binom{k+c-2s}{m+s+d}$ for '
     r'$U_k(m)$, nor for the sequences ending with an ascent; of the shapes $\binom{k+c-\alpha s}{\beta s+d}$ with '
     r'$\alpha,\beta\ge0$ only $\alpha+\beta=1$ occurs; the formal proofs'),
    (r'the sums in Theorem 6.3) are in the Lean files', r'the sums in Section 6.1) are in the Lean files'),
]

README = [
    ('`ShapeFibre.lean`、`ShapeNT.lean` 与 `ShapeCases.lean`）',
     '`ShapeFibre.lean`、`ShapeNT.lean`、`ShapeCases.lean` 与 `ShapeRemarks.lean`）'),
    ('共 57 个模块（', '共 58 个模块（'),
    ('与定理 6.1–6.3（没有 (2,1) 形状的单族和；非负参数的单族二项式形状只有 α+β = 1 的）后由 2675 增加',
     '与第 6.1 节（定理 6.1–6.3：没有 (2,1) 形状的单族和，非负参数的单族二项式形状只有 α+β = 1 的；以及其后的注记，'
     '注记 6.4 的最后两句除外）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_shapecases.py`。',
     '补丁 `patch_paper_2026-10-10_lean_shapecases.py`。第三十一项：论文第 6.1 节其余的断言，新模块 '
     '`ShapeRemarks.lean`（`NA_single_sum`：不以上升结尾的部分 NA k m = Σ_{s≥0} S(m+s, m)·C(k+m−2s, m+s)，正是定理 6.1 '
     '排除的形状（注记 5.2 的 P_m·Σ NA xᵏ = 1 与 `coeff_inv_Ppoly`）；`U_zero_single_sum`：m = 0 时定理 6.1 的结论不成立；'
     '`NUp_explicit`：U^↑_k(m) 是定理 4.6 的第二个和；`NUp_one_single_sum`：U^↑_k(1) = Σ_{s≥0} C(k−2−2s, s)，m = 1 时'
     '定理 6.2 的结论不成立；`ShapeRepZ`：α、β 取整数的表示，`shapeRepZ_natCast`：α, β ≥ 0 时就是 `ShapeRep`；'
     '`shape_neg`：注记 6.4 的第一句，α < 0、α + β = 1 时每个数列都有表示（s = k 一项是 C(βk, βk) = 1，系数由三角方程组'
     '逐个解出）；`shape_sum_one`：β ≥ 0、α + β = 1 的整数形状对每个数列都有表示），同时把 `ShapeCases.lean` 的 '
     '`shape_10`、`shape_01` 推广到任何数列（论文第 6 节开头）。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；'
     '`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_shaperemarks.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_shapecases.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_shapecases.log`）。同日第三十一项：新模块 `ShapeRemarks.lean`（论文第 6.1 节'
     '其余的断言；新定义 `ShapeRepZ f α β`（与 `ShapeRep` 相同，只是 α、β 取整数，用于注记 6.4 的 α < 0）由 AI 核对，'
     '`shapeRepZ_natCast` 证明 α, β ≥ 0 时它与 `ShapeRep` 定义上相同（`Iff.rfl`）；`triA` 只在证明里用；其余陈述只用 '
     '`U`、`NA`、`NUp`、`binomZ` 与 Mathlib 的 `Nat.stirlingSecond`），`ShapeCases.lean` 的 `shape_10`、`shape_01` 改为对'
     '任何数列成立；经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）'
     '与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_shaperemarks.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('单值群数值核对 15 组 (e,b)）。未形式化 |',
     '单值群数值核对 15 组 (e,b)）。Lean：「β≥0 且 α+β=1 时任何数列都有表示」这一方向 2026-10-10 已形式化'
     '（`ShapeRemarks.lean` 的 `shape_sum_one`，α<0 的部分是 `shape_neg`）；α<0、α+β≥2 的形状与退化情形未形式化'
     '（要用 Lüroth 与 Riemann–Hurwitz） |'),
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
