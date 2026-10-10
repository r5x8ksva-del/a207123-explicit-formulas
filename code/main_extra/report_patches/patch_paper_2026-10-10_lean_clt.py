# -*- coding: utf-8 -*-
r"""Lean 续作第二十五项（2026-10-10）：论文推论 8.14（不同取值个数的中心极限定理），新模块 `lean/A207123/CLT.lean`：
- 定义 `cltWords k`（长 k、值域恰为某个 {1,…,q} 的合法词）、`numValues`（不同取值个数 X_k）、`cltMean`、`cltVar`
  （均匀分布下的期望与方差）、`cltLaw k`（(X_k − E X_k)/√Var X_k 的分布）；`cor_clt`：`cltLaw k` 弱收敛到
  `gaussianReal 0 1`。证明不用 Lindeberg–Feller 定理：特征函数的乘积形式 `charFun_cltLaw_eq_prod`、
  逐因子的三阶泰勒估计 `bernoulli_factor_bound`、方差下界 `cltVar_ge`、Mathlib 的 Lévy 连续性定理。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_clt.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；表 6 加推论 8.14 一行；「Not formalized」删去推论 8.14，并说明形式化证明直接估计
  特征函数；只经 AI 对照的定义加上 X_k 的分布。
- paper/reviewer_guide.tex：第 2 节加推论 8.14；第 3 节按优先级重排（第 8 节只剩注记 8.16，移到最后）。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A19 的完成度与形式化一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_clt.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_clt.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '59'

PAPER = [
    (r'Corollary~\ref{cor:negzeros} & \lean{upoly\_eval\_neg\_eq\_zero}',
     r'Corollary~\ref{cor:clt} & \lean{cor\_clt}, \lean{charFun\_cltLaw\_eq\_prod}, \lean{bernoulli\_factor\_bound}, '
     r'\lean{cltVar\_ge}\\' + '\n' +
     r'Corollary~\ref{cor:negzeros} & \lean{upoly\_eval\_neg\_eq\_zero}'),
    (r'and in Section~\ref{sec:realroots} Corollary~\ref{cor:clt} and Remark~\ref{rem:chains}. '
     r'Lemma~\ref{lem:il-pick} is formalized, but the other formal proofs in Section~\ref{sec:realroots} write '
     r'$g\ll f$ as $g=cf+\sum_aw_a\,f/(z-a)$ with $c,w_a\ge0$ instead of using it.',
     r'and in Section~\ref{sec:realroots} Remark~\ref{rem:chains}. '
     r'Lemma~\ref{lem:il-pick} is formalized, but the other formal proofs in Section~\ref{sec:realroots} write '
     r'$g\ll f$ as $g=cf+\sum_aw_a\,f/(z-a)$ with $c,w_a\ge0$ instead of using it, and the formal proof of '
     r'Corollary~\ref{cor:clt} estimates the characteristic functions directly instead of citing the '
     r'Lindeberg--Feller theorem.'),
    (r'at a point and of $g\ll f$ (by the characterization after its definition), are documented in the Lean files',
     r'at a point, of $g\ll f$ (by the characterization after its definition) and of the law of $X_k$ in '
     r'Corollary~\ref{cor:clt}, are documented in the Lean files'),
]
PAPER_RE = [
    (r'consists of 50 files that start from', 'consists of 51 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('with Descartes\' rule from Mathlib), and Corollary 8.15. The axiom check',
     'with Descartes\' rule from Mathlib), Corollary 8.14 (the central limit theorem; the formal proof estimates '
     'characteristic functions directly instead of citing the Lindeberg--Feller theorem) and Corollary 8.15. '
     'The axiom check'),
    ('values of rational functions, interlacing) are in the Lean files',
     'values of rational functions, interlacing, the law of $X_k$) are in the Lean files'),
    ('\\item \\textbf{Section 8, real-rootedness (pp.~24--29).} Propositions 8.10 and 8.11 and Theorem 8.1 are '
     'formalized, by a route that replaces Lemma 8.5 (upper half-plane) with $g=cf+\\sum_aw_af/(z-a)$; Lemma 8.5 '
     'itself and Lemma 8.7(3) (without Gauss--Lucas) are formalized too. Not formalized: Corollary 8.14 (the central '
     'limit theorem, a consequence via the Lindeberg--Feller theorem); Lemma 8.12 and Corollaries 8.13 and 8.15 are '
     'formalized. Remark 8.16 explains why the general theorems on chain polynomials do not apply: the zeros are not '
     'confined to $[-1,0]$.\n', ''),
    ('the formal Corollary 5.5 uses instead of constructing $\\cO(k,m)$.\n',
     'the formal Corollary 5.5 uses instead of constructing $\\cO(k,m)$.\n'
     '\\item \\textbf{Section 8, real-rootedness (pp.~24--29):} only Remark 8.16 is not formalized; it explains why '
     'the general theorems on chain polynomials do not apply (the zeros are not confined to $[-1,0]$). The formal '
     'proofs replace the upper half-plane by $g=cf+\\sum_aw_af/(z-a)$ (Lemma 8.5 itself is formalized separately) '
     'and the Lindeberg--Feller theorem by a direct estimate of characteristic functions.\n'),
]

README = [
    ('`InterlaceDeriv.lean` 与 `Pick.lean`）', '`InterlaceDeriv.lean`、`Pick.lean` 与 `CLT.lean`）'),
    ('共 50 个模块（', '共 51 个模块（'),
    ('与引理 8.5（Pick 判据）后由 2675 增加', '、引理 8.5（Pick 判据）与推论 8.14（中心极限定理）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_pick.py`。',
     '补丁 `patch_paper_2026-10-10_lean_pick.py`。第二十五项：论文推论 8.14（中心极限定理），新模块 `CLT.lean`'
     '（`cor_clt`：在 n_k(1) 个「长 k、值域恰为某个 {1,…,q}」的合法词中均匀随机地取一个，不同取值个数 X_k 标准化后的'
     '分布 `cltLaw k` 弱收敛（即依分布收敛）到标准正态分布 `gaussianReal 0 1`；X_k 的期望、方差按定义写成有限和。'
     '不用 Lindeberg–Feller 定理：由 n_k = N(k,k)·∏(z + r) 把特征函数写成 ∏_r e^{−iτ p_r}(p_r e^{iτ} + q_r)'
     '（`charFun_cltLaw_eq_prod`，p_r = 1/(1+r)），期望 1 + Σp_r、方差 Σp_r q_r 由 ∏(z + r) 在 1 处的一阶、二阶导数'
     '得到，逐因子三阶泰勒估计（`bernoulli_factor_bound`，Mathlib 的 `Complex.exp_bound`）给出 |φ_k(t) − e^{−t²/2}| ≤ '
     '|t|³/σ_k + t⁴/σ_k²，方差下界 σ_k² ≥ (⌈k/3⌉ − 1)/4（`cltVar_ge`，−1 的重根各贡献 1/4），最后用 Mathlib 的 Lévy '
     '连续性定理）。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_clt.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_pick.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_pick.log`）。同日第二十五项：新模块 `CLT.lean`（论文推论 8.14；新定义 '
     '`cltWords k`（`range (k+1)` 上 `NW k q` 的并，即长 k、值域恰为某个 {1,…,q} 的合法词）、`numValues w`'
     '（`w.toFinset.card`，不同取值个数）、`cltMean k`、`cltVar k`（均匀分布下的期望与方差，有限和）、`cltLaw k`'
     '（每个词质量 `1/|cltWords k|` 的狄拉克测度之和在 `(X − E)/√Var` 下的像）由 AI 核对；主陈述 `cor_clt` 是 Mathlib '
     '`ProbabilityMeasure ℝ` 中的收敛（弱收敛，Mathlib 的依分布收敛即此），极限 `gaussianReal 0 1`；辅助定义 '
     '`linProd`、`negRoots`、`momS`、`momQ` 不出现在主陈述里），经 `lean/lean_one.sh` 编译、重编根模块、重跑 '
     '`Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_clt.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('■■■■■（实根、单根、对数凹与单峰、根的分布与变号，2026-10-10）；■■■■□（中心极限定理）',
     '■■■■■（实根、单根、对数凹与单峰、根的分布与变号、中心极限定理，2026-10-10）'),
    ('；中心极限定理未形式化。',
     '；第二十五项形式化了中心极限定理（论文推论 8.14，`CLT.lean` 的 `cor_clt`：均匀随机取词时不同取值个数标准化后'
     '的分布弱收敛到标准正态分布；不用 Lindeberg–Feller 定理，由 n_k 的根分解把特征函数写成 ∏(p e^{iτ} + q)，'
     '逐因子三阶泰勒估计，再用 Mathlib 的 Lévy 连续性定理）。'),
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
