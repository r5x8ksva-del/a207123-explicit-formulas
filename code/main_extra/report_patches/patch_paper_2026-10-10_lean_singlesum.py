# -*- coding: utf-8 -*-
r"""Lean 续作第二十七项（2026-10-10）：论文定理 6.1（U_k(m) 没有 (2,1) 形状的单族和），新模块 `lean/A207123/SingleSum.lean`：
- 定义 `binomZ a b`（论文第 2 节的二项式约定：0 ≤ b ≤ a 之外为 0）；主定理 `thm_S`（m ≥ 1 时不存在整数 c、d、k₀ 与
  复数 A(s)，使 k ≥ k₀ 时 U_k(m) = ∑ᶠ s, A(s)·binomZ(k+c−2s, m+s+d)）。
- 形式证明与论文的路线不同，不用 Laurent 级数域、留数与范数：`substU_coords_unique`（1、x、x² 在 ℂ⟦u⟧ 上线性无关，
  u = x³/(1−x)）、`coe_eq_coords`（在 ℂ[u][T] 中对 T³ + uT − u 取余得到坐标）、`no_common_value`（X³ + X − 1 的三个根上
  ξ^p(1+ξ) = λξ^r 不可能：韦达关系给出 λ³ = 3 且 3λ 是有理数）。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_singlesum.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；表 5 在定理 7.1 之前加定理 6.1 一行（行标签注明 other proof）；「Not formalized」
  改为第 6 节除定理 6.1 外；只经 AI 对照的定义加上定理 6.1 的二项式约定。
- paper/reviewer_guide.tex：第 2 节加定理 6.1 与它的定义；第 3 节 Section 6 一条改写。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A12 的完成度与 Lean 一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_singlesum.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_singlesum.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '61'

PAPER = [
    # 第 6 节在第 7 节之前；行标签照「Remark 8.16, except citations」的写法注明形式证明走另一条路。第一稿把
    # 「形式证明用 1, x, x² 的坐标与韦达关系代替留数与范数」写进第 9 节正文，第 10 节标题被挤到下一页、出 underfull
    # \vbox；在草稿目录（code/main_extra/try_layout.py）试了八种写法，正文里哪怕只加「and that of Theorem 6.1 avoids
    # residues and norms」或一个括号也会挤页，取写进行标签的这一种，路线的说明放进审读指南
    (r'\lean{not\_annihilate\_kauers}\\' + '\n' + r'Theorem~\ref{thm:neardiag}, Proposition~\ref{prop:newton} &',
     r'\lean{not\_annihilate\_kauers}\\' + '\n' +
     r'Theorem~\ref{thm:S}, other proof & \lean{thm\_S}, \lean{substU\_coords\_unique}, \lean{coe\_eq\_coords}, '
     r'\lean{no\_common\_value}\\' + '\n' +
     r'Theorem~\ref{thm:neardiag}, Proposition~\ref{prop:newton} &'),
    (r'; and Section~\ref{sec:short}. ',
     r'; and Section~\ref{sec:short} except Theorem~\ref{thm:S}. '),
    (r' and of chains in $\bar\Lambda_k$, are documented in the Lean files',
     r', of chains in $\bar\Lambda_k$ and of the binomial convention in Theorem~\ref{thm:S}, are documented in the '
     r'Lean files'),
]
PAPER_RE = [
    (r'consists of 52 files that start from', 'consists of 53 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('Proposition 5.6, Corollary 5.7, and the near-diagonal theorem',
     'Proposition 5.6, Corollary 5.7, Theorem 6.1 (no single sum $\\sum_sA(s)\\binom{k+c-2s}{m+s+d}$; the formal proof '
     'uses coordinates with respect to $1,x,x^2$ and Vieta\'s formulas instead of residues and norms), and the '
     'near-diagonal theorem'),
    ('interlacing, the law of $X_k$, chains in $\\bar\\Lambda_k$) are in the Lean files',
     'interlacing, the law of $X_k$, chains in $\\bar\\Lambda_k$, the binomial convention of Theorem 6.1) are in the '
     'Lean files'),
    ('\\item \\textbf{Section 6, obstructions (pp.~16--22).} Theorems 6.1--6.3 use residues on fibres and norms in '
     'number fields. ',
     '\\item \\textbf{Section 6, obstructions (pp.~16--22).} Theorems 6.2 and 6.3 use residues on fibres and norms in '
     'number fields; so does the written proof of Theorem 6.1, which is formalized by another route. '),
]

README = [
    ('`CLT.lean` 与 `Chains.lean`）', '`CLT.lean`、`Chains.lean` 与 `SingleSum.lean`）'),
    ('共 52 个模块（', '共 53 个模块（'),
    ('与注记 8.16（链与序复形）后由 2675 增加', '、注记 8.16（链与序复形）与定理 6.1（没有 (2,1) 形状的单族和）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_chains.py`。',
     '补丁 `patch_paper_2026-10-10_lean_chains.py`。第二十七项：论文定理 6.1，新模块 `SingleSum.lean`（`thm_S`：m ≥ 1 时'
     ' U_k(m) 不能对所有 k ≥ k₀ 写成 Σ_s A(s)·C(k+c−2s, m+s+d)；二项式按论文第 2 节的约定写成 `binomZ`（0 ≤ b ≤ a 之外'
     '为 0），对 s 的和用 `∑ᶠ`（对每个 k 只有有限项非零）。形式证明与论文的路线不同，不用 Laurent 级数域、留数与范数：'
     '用 Mathlib 的 `PowerSeries.subst` 代入 u = x³/(1−x)，由 Σ_n C(n−2t, t)x^n = u^t/(1−x) 得 x^{K₁}G_m − x^{K₂}ã(u)/(1−x)'
     ' 是多项式；`substU_coords_unique`：1、x、x² 在 ℂ⟦u⟧ 上线性无关（代入后的 x 进阶模 3 不同）；`coe_eq_coords`：'
     '在 ℂ[u][T] 中对 T³ + uT − u 取余得到坐标，乘以 P_m = (1−x)^{m+1}∏_{v≤m}(1 − vu) 后消去未知的 ã，在 u = 1 处'
     '坐标向量成比例；`no_common_value`：于是 X³ + X − 1 的三个根上 ξ^p(1+ξ) = λξ^r，韦达关系给出 λ³ = 3 而 3λ 是'
     '有理数，矛盾）。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_singlesum.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_chains.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_chains.log`）。同日第二十七项：新模块 `SingleSum.lean`（论文定理 6.1；新定义 '
     '`binomZ a b`（整数参数的二项式系数：`0 ≤ b ≤ a` 时为 `a.toNat.choose b.toNat`，否则为 0，即论文第 2 节的约定）'
     '由 AI 核对；主陈述 `thm_S` 对 s ∈ ℤ 的和用 Mathlib 的 `∑ᶠ`，对每个 k 只有有限个 s 的项非零，所以就是论文的有限和；'
     '`uS`、`substU`、`qU`、`coordU`、`Dpoly` 只在证明里用，不承载陈述的含义），经 `lean/lean_one.sh` 编译、重编根模块、'
     '重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_singlesum.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('| ■■■■□ | 书面证明（Eisenstein + 留数 / 范数）；',
     '| ■■■■□（定理 S ■■■■■） | 书面证明（Eisenstein + 留数 / 范数）；'),
    ('（当天第一次重排时曾是第 1 处）；无 Lean |',
     '（当天第一次重排时曾是第 1 处）；Lean：定理 S（论文定理 6.1）2026-10-10 已形式化（`SingleSum.lean` 的 `thm_S`；'
     '形式证明不用 Laurent 级数、留数与范数，改用 1、x、x² 的坐标与 X³ + X − 1 三个根上的韦达关系），S′ 与其他形状'
     '未形式化 |'),
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
