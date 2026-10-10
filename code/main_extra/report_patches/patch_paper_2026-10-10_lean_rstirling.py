# -*- coding: utf-8 -*-
r"""Lean 续作第十七项（2026-10-10）：论文引理 4.5 最后一句的形式化，新模块 `lean/A207123/RStirling.lean`：
`H(m,s,j) = h_s(j, …, m)` 是 `{1, …, m+s}` 分成 `m` 块、`1, …, j` 两两不同块的集合划分个数（r-Stirling 数），
`H(m,s,0) = H(m,s,1)` 是分成 `m` 块的划分个数，且等于 Mathlib 按递推定义的 `Nat.stirlingSecond`
（`hc_vars_eq_partCount`、`stirlingSecond_eq_partCount`、`partCount_one`、`lemma_coef_partitions`）。集合划分按
定义写成「各块非空、两两不交、并为 {1, …, N}」的有限集族（`IsSetPartition`）；证明去掉最大元，得到与
`h_{s+1}(j..m+1) = h_{s+1}(j..m) + (m+1)·h_s(j..m+1)` 相同的递推（`card_setParts_single`、`card_setParts_join`）。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_rstirling.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 定理 4.4、引理 4.5 一行加
  `lemma_coef_partitions`、`stirlingSecond_eq_partCount`；「Not formalized」去掉引理 4.5 的 r-Stirling 识别。
- paper/reviewer_guide.tex：第 2 节引理 4.5 一句；第 3 节 Section 4 一条只剩命题 4.7 的双射。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_rstirling.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_rstirling.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '50'

PAPER = [
    (r'Theorem~\ref{thm:gfxy}, Lemma~\ref{lem:coef} & \lean{Gxy\_zero}, \lean{Gxy\_rec}, \lean{Gxy\_prod}, '
     r'\lean{coef\_formula\_xy}\\',
     r'Theorem~\ref{thm:gfxy}, Lemma~\ref{lem:coef} & \lean{Gxy\_zero}, \lean{Gxy\_rec}, \lean{Gxy\_prod}, '
     r'\lean{coef\_formula\_xy}, \lean{lemma\_coef\_partitions}, \lean{stirlingSecond\_eq\_partCount}\\'),
    (r'in Lemma~\ref{lem:coef}, the identification of $H(m,s,j)$ with $r$-Stirling numbers for $j\ge1$; ', ''),
]
PAPER_RE = [
    (r'consists of 41 files that start from', 'consists of 42 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('the generating function in $x$ and $y$ and the coefficient formula (Theorem 4.4, Lemma 4.5)',
     'the generating function in $x$ and $y$ and the coefficient formula (Theorem 4.4, Lemma 4.5, including the '
     'set-partition meaning of $H(m,s,j)$)'),
    ('the identification with $r$-Stirling numbers in Lemma 4.5 and the bijection of Proposition 4.7 (the formal proofs '
     'of Theorems 4.4 and 4.6 avoid them).',
     'the bijection of Proposition 4.7 (the formal proofs of Theorems 4.4 and 4.6 avoid it).'),
]

README = [
    ('`AsympNumerics.lean` 与 `OeisRowOrders.lean`）', '`AsympNumerics.lean`、`OeisRowOrders.lean` 与 `RStirling.lean`）'),
    ('共 41 个模块（', '共 42 个模块（'),
    ('定理 4.4、引理 4.5 的按 y 细化与注记 5.2 后由 2675 增加', '定理 4.4、引理 4.5（按 y 细化与集合划分的意义）与注记 5.2 后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_oeisroworders.py`。',
     '补丁 `patch_paper_2026-10-10_lean_oeisroworders.py`。第十七项：引理 4.5 最后一句（H(m,s,j) 是 {1,…,m+s} 分成 m 块、'
     '1,…,j 两两不同块的集合划分个数，即 r-Stirling 数；H(m,s,0) = H(m,s,1) 是分成 m 块的划分个数），新模块 '
     '`RStirling.lean`：集合划分按定义写成「各块非空、两两不交、并为 {1,…,N}」的有限集族（`IsSetPartition`、'
     '`Separates`、`setParts`、`partCount`）；去掉最大元 N+1：单独成块的一一对应 N 个元素分成 m 块的划分'
     '（`card_setParts_single`），否则对应「N 个元素分成 m+1 块的划分与其中可加入 N+1 的一块」（`card_setParts_join`），'
     'N ≥ j 时可加入任何一块、N < j 时一块也不行，于是 `partCount_succ_succ` 与 h_s 的递推一致，归纳得 '
     '`hc_vars_eq_partCount`；`stirlingSecond_eq_partCount` 说明 Mathlib 按递推定义的 `Nat.stirlingSecond` 就是划分个数'
     '（Mathlib 的 Bell 数文件把「确实是划分个数」列为待办），`partCount_one`：只分开一个元素没有约束；合并陈述 '
     '`lemma_coef_partitions`。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；'
     '补丁 `patch_paper_2026-10-10_lean_rstirling.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_oeisroworders.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_oeisroworders.log`）。同日第十七项：新模块 `RStirling.lean`（论文引理 4.5 最后'
     '一句；陈述用到的新定义 `IsSetPartition`（各块非空、两两不交、并为 S）、`Separates`（1,…,j 两两不同块）、'
     '`setParts`、`partCount` 承载「集合划分个数」的意思，由 AI 对照论文核对；`Allowed` 只在证明里用），经 '
     '`lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，'
     '`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_rstirling.log`）。' % (_ax, DECLS, FRESH)),
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
