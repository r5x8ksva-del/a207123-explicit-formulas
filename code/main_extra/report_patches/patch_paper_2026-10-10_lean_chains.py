# -*- coding: utf-8 -*-
r"""Lean 续作第二十六项（2026-10-10）：论文注记 8.16（链多项式与序复形），新模块 `lean/A207123/Chains.lean`：
- 定义 `lamBot`、`lamTop`（Λ_k 的最小元、最大元）与 `numChainsBar k n`（Λ̄_k = Λ_k \ {0,1} 中 n 元链的个数，链从大到小
  排列）；`N_eq_numChainsBar`（N(k,q) 是 q − 1 元链的个数）、`nR_eq_chainPoly`（n_k 是链多项式）、
  `hpoly_eq_hPoly_orderComplex`（h_k 是序复形的 h-多项式；`numChainsBar_eq_zero`、`numChainsBar_pos` 给出维数 k − 2）、
  `no_root_lt_neg_one`（h 系数非负时链多项式在 (−∞,−1) 无零点）、`hpoly_exists_coeff_neg`（k ≥ 3 时 h_k 有负系数）。
  与 Boolean 格的类比、「不是 Cohen–Macaulay」与 [BL26] 的结果是引文献，未形式化。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_chains.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；表 6 加注记 8.16 一行（行标签注明 except citations）；「Not formalized」删去
  注记 8.16；只经 AI 对照的定义加上 Λ̄_k 中的链。
- paper/reviewer_guide.tex：第 2 节加注记 8.16；第 3 节 Section 8 一条改写。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A19 的形式化一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_chains.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_chains.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '60'

PAPER = [
    (r'\lean{leadingCoeff\_hpoly\_eq}\\' + '\n' + r'\bottomrule',
     r'\lean{leadingCoeff\_hpoly\_eq}\\' + '\n' +
     r'Remark~\ref{rem:chains}, except citations & \lean{N\_eq\_numChainsBar}, \lean{nR\_eq\_chainPoly}, '
     r'\lean{hpoly\_eq\_hPoly\_orderComplex}, \lean{no\_root\_lt\_neg\_one}, \lean{hpoly\_exists\_coeff\_neg}\\' + '\n' +
     r'\bottomrule'),
    # 第一稿在这里写「and in Remark 8.16 the statements quoted from the literature (...)」，第 9 节长出约一行，第 10 节
    # 标题被挤到下一页、第 29 页出 underfull \vbox；在草稿目录（code/main_extra/try_layout.py）试了七种写法，取把例外
    # 写进表 6 行标签的这一种（与原来「Lemma 8.12, except the sign of λ_k」的写法一致）
    (r'; Section~\ref{sec:short}; and in Section~\ref{sec:realroots} Remark~\ref{rem:chains}. ',
     r'; and Section~\ref{sec:short}. '),
    (r' and of the law of $X_k$ in Corollary~\ref{cor:clt}, are documented in the Lean files',
     r', of the law of $X_k$ in Corollary~\ref{cor:clt} and of chains in $\bar\Lambda_k$, are documented in the '
     r'Lean files'),
]
PAPER_RE = [
    (r'consists of 51 files that start from', 'consists of 52 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('instead of citing the Lindeberg--Feller theorem) and Corollary 8.15. The axiom check',
     'instead of citing the Lindeberg--Feller theorem), Corollary 8.15 and Remark 8.16 ($N(k,q)$ counts chains in '
     '$\\bar\\Lambda_k$, $h_k$ is the $h$-polynomial of the order complex and has a negative coefficient for '
     '$k\\ge3$). The axiom check'),
    ('values of rational functions, interlacing, the law of $X_k$) are in the Lean files',
     'values of rational functions, interlacing, the law of $X_k$, chains in $\\bar\\Lambda_k$) are in the Lean files'),
    ('\\item \\textbf{Section 8, real-rootedness (pp.~24--29):} only Remark 8.16 is not formalized; it explains why '
     'the general theorems on chain polynomials do not apply (the zeros are not confined to $[-1,0]$). The formal '
     'proofs replace the upper half-plane by $g=cf+\\sum_aw_af/(z-a)$ (Lemma 8.5 itself is formalized separately) '
     'and the Lindeberg--Feller theorem by a direct estimate of characteristic functions.\n',
     '\\item \\textbf{Section 8, real-rootedness (pp.~24--29):} formalized except the statements of Remark 8.16 '
     'quoted from the literature (the Boolean lattice, Cohen--Macaulayness). Some written proofs differ from the '
     'formal ones, which replace the upper half-plane by $g=cf+\\sum_aw_af/(z-a)$ (Lemma 8.5 itself is formalized '
     'separately) and the Lindeberg--Feller theorem by a direct estimate of characteristic functions.\n'),
]

README = [
    ('`Pick.lean` 与 `CLT.lean`）', '`Pick.lean`、`CLT.lean` 与 `Chains.lean`）'),
    ('共 51 个模块（', '共 52 个模块（'),
    ('与推论 8.14（中心极限定理）后由 2675 增加', '、推论 8.14（中心极限定理）与注记 8.16（链与序复形）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_clt.py`。',
     '补丁 `patch_paper_2026-10-10_lean_clt.py`。第二十六项：论文注记 8.16，新模块 `Chains.lean`（`N_eq_numChainsBar`：'
     'k, q ≥ 1 时 N(k,q) 是 Λ̄_k = Λ_k \\ {0,1} 中 q − 1 元链 y_1 > ⋯ > y_{q−1} 的个数，复用 `Multichain.lean` 的高度表述，'
     '严格递减且不含 0、1 当且仅当高度取遍 0,…,q−1；`nR_eq_chainPoly`：n_k 是 Λ̄_k 的链多项式；'
     '`hpoly_eq_hPoly_orderComplex`：h_k 是序复形 Δ(Λ̄_k)（维数 k − 2）的 h-多项式；`no_root_lt_neg_one`：h 系数非负时'
     '链多项式 (1+z)^d h(z/(1+z)) 在 (−∞,−1) 无零点；`hpoly_exists_coeff_neg`：k ≥ 3 时 h_k 有负系数（n_k 在 (−∞,−1) 有 '
     '⌊k/3⌋ 个零点）。与 Boolean 格的类比、「不是 Cohen–Macaulay」与 [BL26] 的结果是引文献，未形式化）。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_chains.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_clt.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_clt.log`）。同日第二十六项：新模块 `Chains.lean`（论文注记 8.16；新定义 '
     '`lamBot k`、`lamTop k`（全 0 行、全 1 行，Λ_k 的最小元与最大元）、`numChainsBar k n`（`Fin n → Lam k` 中严格递减、'
     '不取 `lamBot`、`lamTop` 的序列个数，即 Λ̄_k 中 n 元链的个数）由 AI 核对；主陈述 `N_eq_numChainsBar`、'
     '`hpoly_eq_hPoly_orderComplex`（h-多项式按定义 Σ f_{i−1} t^i (1−t)^{d−i} 写出）、`hpoly_exists_coeff_neg`），经 '
     '`lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，'
     '`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_chains.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('再用 Mathlib 的 Lévy 连续性定理）。',
     '再用 Mathlib 的 Lévy 连续性定理）。第二十六项形式化了论文注记 8.16 的主体（`Chains.lean`：N(k,q) 是 Λ̄_k 中 '
     'q − 1 元链的个数，n_k 是链多项式，h_k 是序复形的 h-多项式，k ≥ 3 时 h_k 有负系数；与 Boolean 格的类比、'
     '「不是 Cohen–Macaulay」两句引文献，未形式化）。'),
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
