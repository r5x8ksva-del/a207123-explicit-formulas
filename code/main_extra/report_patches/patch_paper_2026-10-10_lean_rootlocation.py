# -*- coding: utf-8 -*-
r"""Lean 续作第二十二项（2026-10-10）：论文引理 8.12 中 λ_k 的符号与推论 8.13（h_k 的根的位置与系数的变号次数），
新模块 `lean/A207123/RootLocation.lean`：
- 引理 8.12：`lemma_minusone_sign`（λ_k 的符号，按论文的分情形写法）、`lemma_minusone`（引理 8.12 合在一起）；
  证明经 λ_k = (−1)^{deg h_k}·lc(h_k) 与已形式化的 lc(h_k) 的符号（论文的归纳证明没有照搬）。
- 推论 8.13：`nBelow_nR`（n_k 在 (−∞,−1) 中恰有 ⌊k/3⌋ 个根）、`card_roots_hR_gt_one`、`card_roots_hR_neg`、
  `signVariations_hpoly`（Mathlib 的 Descartes 法则给 ≥，组合引理 `signVariations_add_comp_neg_X_le`
  （常数项非零时 V(P) + V(P(−x)) ≤ deg P）给 ≤）、`cor_hk_signs`（合在一起）。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_rootlocation.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；表 6 引理 8.12 一行去掉「except the sign of λ_k」并加 `lemma_minusone`，
  加推论 8.13 一行；「Not formalized」删去 λ_k 的符号与推论 8.13；第 8 节引理 8.12 之后说明 Lean 的那句改写。
- paper/reviewer_guide.tex：第 2 节与第 3 节 Section 8 一条。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A19 的完成度与形式化一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_rootlocation.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_rootlocation.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '56'

PAPER = [
    (r'Lemma~\ref{lem:minusone}, except the sign of $\lambda_k$ & \lean{rootMultiplicity\_nrowPoly\_ceil}, '
     r'\lean{natDegree\_hpoly}, \lean{leadingCoeff\_hpoly\_sign}\\' + '\n',
     r'Lemma~\ref{lem:minusone} & \lean{lemma\_minusone}, \lean{lemma\_minusone\_sign}, '
     r'\lean{rootMultiplicity\_nrowPoly\_ceil}, \lean{natDegree\_hpoly}, \lean{leadingCoeff\_hpoly\_sign}\\' + '\n'
     r'Corollary~\ref{cor:hk-signs} & \lean{cor\_hk\_signs}, \lean{nBelow\_nR}, '
     r'\lean{signVariations\_add\_comp\_neg\_X\_le}\\' + '\n'),
    (r'with $c,w_a\ge0$ instead), the sign of $\lambda_k$ in Lemma~\ref{lem:minusone}, '
     r'Corollaries~\ref{cor:hk-signs} and~\ref{cor:clt}, and Remark~\ref{rem:chains}.',
     r'with $c,w_a\ge0$ instead), Corollary~\ref{cor:clt}, and Remark~\ref{rem:chains}.'),
    (r'The statements about $a_k$, $\deg h_k$ and the sign of the leading coefficient of $h_k$ are also formalized '
     r'in Lean, with a different proof (\lean{rootMultiplicity\_nrowPoly}, \lean{natDegree\_hpoly}, '
     r'\lean{leadingCoeff\_hpoly\_sign}).',
     # 第一稿写得更长（先列三条再说 λ_k），这一段出 underfull \hbox、第 29 页出 underfull \vbox；在草稿目录试了
     # 四种措辞（code/main_extra/try_layout.py），都无警告，取保留原来三个名字的这一种
     r'The lemma is also formalized in Lean, with a different proof: \lean{lemma\_minusone} combines '
     r'\lean{rootMultiplicity\_nrowPoly}, \lean{natDegree\_hpoly} and \lean{leadingCoeff\_hpoly\_sign} with the '
     r'identity $\lambda_k=(-1)^{\deg h_k}\lc(h_k)$ proved at the end of the proof below.'),
]
PAPER_RE = [
    (r'consists of 47 files that start from', 'consists of 48 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('strictly log-concave and unimodal; proved without Newton\'s inequalities),',
     'strictly log-concave and unimodal; proved without Newton\'s inequalities), Lemma 8.12 and Corollary 8.13 '
     '(where the zeros of $h_k$ lie and how often its coefficients change sign, with Descartes\' rule from Mathlib),'),
    ('Not formalized: Lemmas 8.5 and 8.7(3) themselves and Lemma 8.12 (the order of the zero $-1$ and the sign of the '
     'cofactor there; of this lemma only $a_k$, $\\deg h_k$ and the sign of the leading coefficient of $h_k$ are '
     'formalized); Corollaries 8.13 and 8.14 are consequences; Corollary 8.15 is formalized.',
     'Not formalized: Lemmas 8.5 and 8.7(3) themselves and Corollary 8.14 (the central limit theorem, a consequence '
     'via the Lindeberg--Feller theorem); Lemma 8.12 and Corollaries 8.13 and 8.15 are formalized.'),
]

README = [
    ('`SimpleRoots.lean` 与 `LogConcave.lean`）', '`SimpleRoots.lean`、`LogConcave.lean` 与 `RootLocation.lean`）'),
    ('共 47 个模块（', '共 48 个模块（'),
    ('推论 8.2（N 的每一行为正、严格对数凹、单峰）后由 2675 增加',
     '推论 8.2（N 的每一行为正、严格对数凹、单峰）、引理 8.12（λ_k 的符号）与推论 8.13（h_k 的根的位置、系数的变号次数）'
     '后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_table_split.py`。',
     '补丁 `patch_paper_2026-10-10_lean_table_split.py`。第二十二项：论文引理 8.12 中 λ_k 的符号与推论 8.13，新模块 '
     '`RootLocation.lean`（`lemma_minusone_sign`、`lemma_minusone`：经 λ_k = (−1)^{deg h_k}·lc(h_k) 与已形式化的 '
     'lc(h_k) 的符号；`nBelow_nR`：n_k 在 (−∞,−1) 中恰有 ⌊k/3⌋ 个根，由 (α_k) 每步增 0 或 1 与 λ_k 的符号给出的奇偶性；'
     '`card_roots_hR_gt_one`、`card_roots_hR_neg`：h_k 在 (1,∞) 中恰有 ⌊k/3⌋ 个根，其余 ⌊(k+1)/3⌋ 个是负数；'
     '`signVariations_hpoly`：h_k 的系数恰变号 ⌊k/3⌋ 次，Mathlib 的 Descartes 法则给 ≥，组合引理 '
     '`signVariations_add_comp_neg_X_le`（常数项非零时 V(P) + V(P(−x)) ≤ deg P）给 ≤；`cor_hk_signs`）。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_rootlocation.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_logconcave.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_logconcave.log`）。同日第二十二项：新模块 `RootLocation.lean`（论文引理 8.12 '
     '中 λ_k 的符号与推论 8.13；新定义 `mPoly k`（n_k 去掉 (1+z)^{a_k} 后的因子 m_k，显式和）、`mR k`、`nBelow p a`'
     '（(−∞,a) 中的根数）由 AI 核对；主陈述 `lemma_minusone`、`cor_hk_signs` 用到 `nrowPoly`、`hpoly`、`hR` 与 Mathlib 的 '
     '`rootMultiplicity`、`roots`、`signVariations`），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`'
     '（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_rootlocation.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('N 的每一行单峰、对数凹 | ■■■■■（实根、单根、对数凹与单峰，2026-10-10）；■■■■□（其余推论） |',
     'N 的每一行单峰、对数凹 | ■■■■■（实根、单根、对数凹与单峰、根的分布与变号，2026-10-10）；■■■■□（中心极限定理） |'),
    ('；根的分布、变号、中心极限定理未形式化',
     '；第二十二项形式化了根的分布与变号次数（论文推论 8.13 与引理 8.12 中 λ_k 的符号，`RootLocation.lean` 的 '
     '`cor_hk_signs`、`lemma_minusone`；变号次数用 Mathlib 的 Descartes 法则加组合引理 V(P) + V(P(−x)) ≤ deg P）；'
     '中心极限定理未形式化'),
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
