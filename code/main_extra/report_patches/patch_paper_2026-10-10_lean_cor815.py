# -*- coding: utf-8 -*-
r"""Lean 续作第二项（2026-10-10）：推论 8.15 与引理 8.12 的已形式化部分补进论文表 5。
核对发现推论 8.15 早已在 Lean 里证完（报告 T5.3(2)(3)，`lean/A207123/HStruct.lean`）：
  u_k(−j)=0（1≤j≤⌈k/3⌉）= `upoly_eval_neg_eq_zero`（条件写成 j≤⌊(k+2)/3⌋）；
  u_k(−⌈k/3⌉−1)=(−1)^k·lc(h_k) ⇔ `leadingCoeff_hpoly_eq`（lc(h_k)=(−1)^k·u_k(−⌊(k+2)/3⌋−1)，两边同乘 (−1)^k）；
  这个值 ≠ 0 = `upoly_eval_neg_ne_zero`。
引理 8.12 里 a_k=⌈k/3⌉−1、deg h_k=⌊2k/3⌋、lc(h_k) 的符号也早已形式化（`rootMultiplicity_nrowPoly_ceil`、
`natDegree_hpoly`、`leadingCoeff_hpoly_sign`；`nrowPoly` 就是论文的 n_k），正文「Not formalized」一段本来就把它们除外，
但表 5 没有列。10-09 说推论 8.15「没有形式化」是我漏看了 HStruct.lean。
没有新证明；只给 `leadingCoeff_hpoly_eq` 补一行 #print axioms（表 5 的定理名都在 Axioms.lean 里打印公理），重跑 Axioms
（259 条，全量扫描仍是 2678 个声明，只有三条标准公理；日志 logs/lean_axioms_2026-10-10_cor815.log）。本补丁同步：
- paper/main.tex：表 5 在第 7 节一行之后加引理 8.12（除 λ_k 的符号）与推论 8.15 两行；「Not formalized」里第 8 节的除外项
  加上推论 8.15。
- paper/reviewer_guide.tex：第 2 节加上推论 8.15 与引理 8.12 的一部分；第 3 节第 1 条改为推论 8.13、8.14 是推论，8.15 已形式化。
- README.md、notes/Lean定义核对清单.md：记一笔。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_cor815.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

ROW7 = (r'Theorem~\ref{thm:neardiag}, Proposition~\ref{prop:newton} & \lean{T4\_1}, \lean{T4\_1\_threshold}, '
        r'\lean{T4\_2\_3}\\' '\n')
PAPER = [
    (ROW7,
     ROW7 + r'Lemma~\ref{lem:minusone}, except the sign of $\lambda_k$ & \lean{rootMultiplicity\_nrowPoly\_ceil}, '
     r'\lean{natDegree\_hpoly}, \lean{leadingCoeff\_hpoly\_sign}\\' '\n'
     r'Corollary~\ref{cor:negzeros} & \lean{upoly\_eval\_neg\_eq\_zero}, \lean{upoly\_eval\_neg\_ne\_zero}, '
     r'\lean{leadingCoeff\_hpoly\_eq}\\' '\n'),
    (r'Section~\ref{sec:realroots}, apart from the statements about $a_k$, $\deg h_k$ and the sign of the leading '
     r'coefficient of $h_k$ in Lemma~\ref{lem:minusone}.',
     r'Section~\ref{sec:realroots}, apart from Corollary~\ref{cor:negzeros} and the statements about $a_k$, $\deg h_k$ '
     r'and the sign of the leading coefficient of $h_k$ in Lemma~\ref{lem:minusone}.'),
]

GUIDE = [
    (r'the near-diagonal theorem (Theorem 7.1, Proposition 7.2).',
     r'the near-diagonal theorem (Theorem 7.1, Proposition 7.2), Corollary 8.15 and part of Lemma 8.12.'),
    (r'Corollaries 8.13--8.15 are consequences.',
     r'Corollaries 8.13 and 8.14 are consequences; Corollary 8.15 is formalized.'),
]

README = [
    ('论文表 5、「Not formalized」与审读指南相应改动（补丁 `patch_paper_2026-10-10_lean_sigma.py`）。',
     '论文表 5、「Not formalized」与审读指南相应改动（补丁 `patch_paper_2026-10-10_lean_sigma.py`）。第二项：核对发现推论 8.15 '
     '早已形式化（`HStruct.lean` 的 `upoly_eval_neg_eq_zero`、`upoly_eval_neg_ne_zero`、`leadingCoeff_hpoly_eq`，报告 T5.3(2)(3)），'
     '引理 8.12 的 a_k、deg h_k 与首项系数符号也是（`rootMultiplicity_nrowPoly_ceil`、`natDegree_hpoly`、`leadingCoeff_hpoly_sign`），'
     '只是论文表 5 没列；没有新证明，给 `leadingCoeff_hpoly_eq` 补一行 #print axioms 后重跑 Axioms（259 条，仍是 2678 个声明，'
     '只有三条标准公理），表 5 加两行（补丁 `patch_paper_2026-10-10_lean_cor815.py`）。'),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10.log`）。\n\n## 总清单',
     '（`logs/check_lean_fresh_2026-10-10.log`）。同日第二项：推论 8.15 与引理 8.12 的一部分本来就已形式化（见论文表 5 新加的两行），'
     '给 `leadingCoeff_hpoly_eq` 补一行 `#print axioms` 后重跑 `Axioms.lean`（259 条，2678 个声明，只有三条标准公理；'
     '`logs/lean_axioms_2026-10-10_cor815.log`），`check_lean_fresh.py` 35 项全部 PASS（`logs/check_lean_fresh_2026-10-10_cor815.log`）。'
     '\n\n## 总清单'),
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
    patch(os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), GUIDE)
    patch(os.path.join(ROOT, 'README.md'), README)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)


if __name__ == '__main__':
    main()
