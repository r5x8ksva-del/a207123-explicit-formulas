# -*- coding: utf-8 -*-
r"""Lean 续作第二十八项（2026-10-10）：论文定理 6.2（以上升结尾的部分 U^↑_k(m) 也没有 (2,1) 形状的单族和，m ≥ 2），
新模块 `lean/A207123/SingleSumAsc.lean`：
- 定义 `NUp k m`（`L k m` 中 `endsAsc l = true` 的序列个数，即以上升结尾 h_{k−1} < h_k 的序列）；主定理 `thm_Spart`
  （陈述与 `thm_S` 相同，把 U_k(m) 换成 U^↑_k(m)）。
- `single_sum_cross`：定理 6.1 证明的前两步对任意满足 P_m·G = V（V 是多项式）的幂级数都成立；`P_mul_GUp`
  （P_m·G^↑ = W_m − 1）；纤维 u = 1/2 上 `no_common_value_b2`（韦达关系与 `not_rat_cube_17` 的 17 进赋值）。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_singlesumasc.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；表 5 定理 6.1 一行改为定理 6.1、6.2；「Not formalized」改为第 6 节除定理
  6.1、6.2 外。
- paper/reviewer_guide.tex：第 2 节定理 6.1 一句改为定理 6.1、6.2，只经 AI 对照的定义加上以上升结尾的序列；第 3 节
  Section 6 一条改写。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A12 的完成度与 Lean 一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_singlesumasc.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_singlesumasc.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '62'

PAPER = [
    (r'Theorem~\ref{thm:S}, other proof & \lean{thm\_S}, \lean{substU\_coords\_unique}, \lean{coe\_eq\_coords}, '
     r'\lean{no\_common\_value}\\',
     r'Theorems~\ref{thm:S}, \ref{thm:Spart}, other proof & \lean{thm\_S}, \lean{thm\_Spart}, '
     r'\lean{substU\_coords\_unique}, \lean{single\_sum\_cross}, \lean{no\_common\_value}, '
     r'\lean{no\_common\_value\_b2}\\'),
    # 第 29 页已排满：「except Theorems 6.1 and 6.2」或在只经 AI 对照的定义里加上 U^↑ 都会把第 10 节标题挤到下一页
    # （草稿目录 code/main_extra/try_layout.py 试了七种写法），取用逗号的这一种；U^↑ 的定义写进审读指南
    (r'; and Section~\ref{sec:short} except Theorem~\ref{thm:S}. ',
     r'; and Section~\ref{sec:short} except Theorems~\ref{thm:S}, \ref{thm:Spart}. '),
]
PAPER_RE = [
    (r'consists of 53 files that start from', 'consists of 54 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('Theorem 6.1 (no single sum $\\sum_sA(s)\\binom{k+c-2s}{m+s+d}$; the formal proof uses coordinates with respect '
     'to $1,x,x^2$ and Vieta\'s formulas instead of residues and norms), and the near-diagonal theorem',
     'Theorems 6.1 and 6.2 (no single sum $\\sum_sA(s)\\binom{k+c-2s}{m+s+d}$ for $U_k(m)$, nor for the sequences '
     'ending with an ascent; the formal proofs use coordinates with respect to $1,x,x^2$ and Vieta\'s formulas instead '
     'of residues and norms), and the near-diagonal theorem'),
    ('chains in $\\bar\\Lambda_k$, the binomial convention of Theorem 6.1) are in the Lean files',
     'chains in $\\bar\\Lambda_k$, the binomial convention of Theorem 6.1, the sequences ending with an ascent in '
     'Theorem 6.2) are in the Lean files'),
    ('Theorems 6.2 and 6.3 use residues on fibres and norms in number fields; so does the written proof of Theorem '
     '6.1, which is formalized by another route. ',
     'Theorem 6.3 uses residues on fibres and norms in number fields; so do the written proofs of Theorems 6.1 and '
     '6.2, which are formalized by another route. '),
]

README = [
    ('`Chains.lean` 与 `SingleSum.lean`）', '`Chains.lean`、`SingleSum.lean` 与 `SingleSumAsc.lean`）'),
    ('共 53 个模块（', '共 54 个模块（'),
    ('与定理 6.1（没有 (2,1) 形状的单族和）后由 2675 增加', '与定理 6.1、6.2（没有 (2,1) 形状的单族和）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_singlesum.py`。',
     '补丁 `patch_paper_2026-10-10_lean_singlesum.py`。第二十八项：论文定理 6.2，新模块 `SingleSumAsc.lean`'
     '（`thm_Spart`：m ≥ 2 时 U^↑_k(m)（`NUp`：H_k(m) 中以上升结尾 h_{k−1} < h_k 的序列个数）也不能写成定理 6.1 那种'
     '单族和。`single_sum_cross` 把定理 6.1 证明的前两步写成对任意满足 P_m·G = V（V 是多项式）的幂级数都成立的引理：'
     'D(u₀) = 0 时 T³ + u₀T − u₀ 的任意两个根 ξ、η 满足 F₁(ξ)F₂(η) = F₁(η)F₂(ξ)；`P_mul_GUp`：P_m·G^↑ = W_m − 1'
     '（用注记 5.2 的 `P_mul_NAser`）；取 u₀ = 1/2（b_2 = 1 − x − 2x³ 的根 η），W_m(η) − 1 = η⁵(4 − 2η)、1 − η = 2η³；'
     '`no_common_value_b2`：2X³ + X − 1 的三个根上 η^p(2 − η) = λη^r 不可能，韦达关系给出 λ³ = 17·2^{r−p−1} 而 3λ 是'
     '有理数，`not_rat_cube_17` 用 17 进赋值（Mathlib 的 `padicValRat`）排除；论文用 ℚ(η) 中的范数，这里不用）。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_singlesumasc.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_singlesum.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_singlesum.log`）。同日第二十八项：新模块 `SingleSumAsc.lean`（论文定理 6.2；'
     '新定义 `NUp k m`（`L k m` 中 `endsAsc l = true` 的序列个数，即以上升结尾 h_{k−1} < h_k 的序列；`endsAsc` 是注记 '
     '5.2 已有的定义）由 AI 核对；主陈述 `thm_Spart` 与 `thm_S` 一样用 `binomZ` 与 `∑ᶠ`；`GUp` 只在证明里用），经 '
     '`lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，'
     '`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_singlesumasc.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('| ■■■■□（定理 S ■■■■■） |', '| ■■■■□（定理 S 与 (ii) ■■■■■） |'),
    ('Lean：定理 S（论文定理 6.1）2026-10-10 已形式化（`SingleSum.lean` 的 `thm_S`；形式证明不用 Laurent 级数、留数与'
     '范数，改用 1、x、x² 的坐标与 X³ + X − 1 三个根上的韦达关系），S′ 与其他形状未形式化 |',
     'Lean：定理 S（论文定理 6.1）与 (ii)（截断块部分，论文定理 6.2）2026-10-10 已形式化（`SingleSum.lean` 的 '
     '`thm_S`、`SingleSumAsc.lean` 的 `thm_Spart`；形式证明不用 Laurent 级数、留数与范数，改用 1、x、x² 的坐标与'
     '三个根上的韦达关系，(ii) 再加 17 进赋值），S′ 与其他形状未形式化 |'),
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
