# -*- coding: utf-8 -*-
r"""Lean 续作第二十九项（2026-10-10）：论文定理 6.3 证明的第 1–3 步（一般形状的母函数、坐标与纤维），
新模块 `lean/A207123/ShapeFibre.lean`：
- 定义 `ShapeRep f α β`（定理 6.3 的表示：k ≥ k₀ 时 f(k) = Σ_{s≥s₀} A(s)·C(k+c−αs, βs+d)）；`vS`、`substV`
  （v = x^{α+β}/(1−x)^β 的代入）、`qV`、`coordV`、`homogY` 只在证明里用。
- `shape_gf`（第 1 步）、`subst_coords_unique_gen`、`aeval_eq_coordsV`、`cross_of_eq`（第 2 步）、`shape_fibre_x`、
  `shape_fibre_y`（第 3 步：纤维 v = v(ξ) 上每个点都是 P_m 的根；论文用极点，这里用坐标的交叉关系）。
  情形分析（定理 6.3 的四种情形与 α+β = 1 的方向）在下一项。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_shapefibre.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（定理 6.3 还没有全部形式化，表 5 不变）。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A20 的 Lean 一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_shapefibre.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_shapefibre.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '63'

PAPER = []
PAPER_RE = [
    (r'consists of 54 files that start from', 'consists of 55 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`SingleSum.lean` 与 `SingleSumAsc.lean`）', '`SingleSum.lean`、`SingleSumAsc.lean` 与 `ShapeFibre.lean`）'),
    ('共 54 个模块（', '共 55 个模块（'),
    ('与定理 6.1、6.2（没有 (2,1) 形状的单族和）后由 2675 增加',
     '、定理 6.1、6.2（没有 (2,1) 形状的单族和）与定理 6.3 证明的第 1–3 步后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_singlesumasc.py`。',
     '补丁 `patch_paper_2026-10-10_lean_singlesumasc.py`。第二十九项：论文定理 6.3 证明的第 1–3 步，新模块 '
     '`ShapeFibre.lean`（`ShapeRep`：定理 6.3 的表示 f(k) = Σ_{s≥s₀} A(s)·C(k+c−αs, βs+d)；`shape_gf`：第 1 步，'
     'Σ_k C(k+c−αs, βs+d)x^k = x^{d−c}(1−x)^{−d−1}v^s，v = x^{α+β}/(1−x)^β，所以 f 要么最终为 0，要么 '
     'x^{K₁}F − x^{K₂}(1−x)^{−h−1}ã(v) 是多项式（重新编号时用 Nat.find 找到使 βs+d ≥ 0 的最小 s）；'
     '`subst_coords_unique_gen`：z = x 或 z = x/(1−x) 时 1, z, …, z^{n−1} 在 ℂ⟦v⟧ 上线性无关（x 进阶模 n 不同）；'
     '`aeval_eq_coordsV`、`cross_of_eq`：在 ℂ[v][T] 中对 T^n − v(1−T)^b 取余得到坐标，F₁(z) = F₂(z)·ã(v) 时'
     ' T^n − v₀(1−T)^b 的任意两个根 η、η′ 满足 F₁(η)F₂(η′) = F₁(η′)F₂(η)；`shape_fibre_x`（α ≥ 1）、'
     '`shape_fibre_y`（α = 0，用 y = x/(1−x)，多项式先乘 (1+y)^D）：b_1 的根 ξ 所在的纤维 v = v(ξ) 上每个点都是 '
     'P_m 的根。论文用 G_m 在纤维上的极点，这里取 F₂ = x^{K₂}P_m、F₁ = (1−x)^{h+1}(x^{K₁}W_m − P_mE)，F₂(ξ) = 0 而 '
     'F₁(ξ) ≠ 0。定理 6.3 的情形分析在下一项）。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；'
     '`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_shapefibre.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_singlesumasc.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_singlesumasc.log`）。同日第二十九项：新模块 `ShapeFibre.lean`（论文定理 6.3 '
     '证明的第 1–3 步；新定义 `ShapeRep f α β`（k ≥ k₀ 时 `f k = ∑ᶠ s, if s₀ ≤ s then A s * binomZ (k+c−α·s) (β·s+d) '
     'else 0`，即论文定理 6.3 中的 Σ_{s≥s₀}）由 AI 核对，是下一项定理 6.3 陈述的一部分；`vS`、`substV`、`qV`、`coordV`、'
     '`homogY` 只在证明里用），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条'
     '标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_shapefibre.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('5 条，含 1800 个方程组与反向检查）。未形式化；α<0 的形状不在范围内。',
     '5 条，含 1800 个方程组与反向检查）。Lean：证明的第 1–3 步（母函数、坐标、纤维上每一点都是 P_m 的根）'
     '2026-10-10 已形式化（`ShapeFibre.lean` 的 `shape_fibre_x`、`shape_fibre_y`），情形分析尚未形式化；α<0 的形状不在'
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
    patch(os.path.join(ROOT, 'README.md'), README, README_RE)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)
    patch(os.path.join(ROOT, '猜想总表.md'), TABLE)


if __name__ == '__main__':
    main()
