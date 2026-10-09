# -*- coding: utf-8 -*-
r"""Lean 续作第三项（2026-10-10）：论文推论 5.5 形式化（分母乘掉的形式），新模块 `lean/A207123/Saturated.lean`：
  `mul_mem_ideal_of_vanish`（(1)：R ∈ O 在象限中 Δ ≠ 0 的点上零化 U ⇒ Δ·R ∈ O·L1）、
  `mem_ideal_of_mul_mem_ideal`（(2)：Δ ≠ 0、Δ·R ∈ O·L1 ⇒ R ∈ O·L1，即 O(k,m)·L1 ∩ O = O·L1）、
  辅助引理 `mulOp_mul_pureOp`。有理系数的 Ore 代数 O(k,m) 本身没有在 Lean 里定义；论文的陈述与分母乘掉的形式之间的
  换算（取公分母、系数写在左边）是书面的。根模块加 import，Axioms 加两条（共 261 条），全量扫描 2682 个声明。
本补丁同步：
- paper/main.tex：第 9 节文件数 27 → 28、声明数 2678 → 2682；表 5 在定理 5.4 一行之后加推论 5.5（分母乘掉的形式）一行；
  「Not formalized」里的「Corollary 5.5」改为「推论 5.5 与分母乘掉的形式之间的换算」。
- paper/reviewer_guide.tex：第 2 节加上推论 5.5；第 3 节第 4 条去掉推论 5.5，注明它已形式化（分母乘掉的形式）。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_saturated.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

ROW54 = (r'Theorem~\ref{thm:ideal} & \lean{RelU\_eq}, \lean{RelU\_iff\_mem\_span}, \lean{finrank\_relU\_tot}, '
         r'\lean{finrank\_relU\_gr}\\' '\n')
PAPER = [
    (r'consists of 27 files that start from', r'consists of 28 files that start from'),
    (r'all 2678 declarations', r'all 2682 declarations'),
    (ROW54,
     ROW54 + r'Corollary~\ref{cor:saturated}, with denominators cleared & \lean{mul\_mem\_ideal\_of\_vanish}, '
     r'\lean{mem\_ideal\_of\_mul\_mem\_ideal}\\' '\n'),
    (r'Corollary~\ref{cor:saturated}; Corollary~\ref{cor:stirlinglike} and Remark~\ref{rem:kauers},',
     r'the passage between Corollary~\ref{cor:saturated}, which is stated for operators with rational coefficients, and '
     r'the formalized version with denominators cleared; Corollary~\ref{cor:stirlinglike} and Remark~\ref{rem:kauers},'),
]

GUIDE = [
    (r'(Theorems 5.4 and B.1), Proposition 5.6,',
     r'(Theorems 5.4 and B.1), Corollary 5.5 (with denominators cleared), Proposition 5.6,'),
    (r"Corollary 5.5 (rational coefficients), and Corollary 5.7 with Remark 5.8, which lead from Kauers' definition of "
     r"Stirling-like sequences to the formalized Proposition 5.6.",
     r"Corollary 5.7 with Remark 5.8, which lead from Kauers' definition of Stirling-like sequences to the formalized "
     r"Proposition 5.6."),
]

README = [
    ('共 27 个模块（2026-10-07 全量构建 26 个，同日又加 `NotStirlingLike.lean`）',
     '共 28 个模块（2026-10-07 全量构建 26 个，同日又加 `NotStirlingLike.lean`，2026-10-10 加 `Saturated.lean`）'),
    ('2678 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句后由 2675 增加）',
     '2682 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句与推论 5.5 后由 2675 增加）'),
    ('只有三条标准公理），表 5 加两行（补丁 `patch_paper_2026-10-10_lean_cor815.py`）。',
     '只有三条标准公理），表 5 加两行（补丁 `patch_paper_2026-10-10_lean_cor815.py`）。第三项：推论 5.5 形式化（分母乘掉的形式），'
     '新模块 `Saturated.lean`：`mul_mem_ideal_of_vanish`（Δ·R 在象限中 Δ≠0 的点上零化 U ⇒ Δ·R ∈ O·L1）、'
     '`mem_ideal_of_mul_mem_ideal`（Δ≠0、Δ·R ∈ O·L1 ⇒ R ∈ O·L1），证明用命题 A（论文引理 5.3），不用正规形；有理系数的 '
     'Ore 代数本身没有在 Lean 里定义，两种写法之间的换算是书面的。中途内存两次不够（提交余量 12.2–12.8 GB），没有启动，'
     '等回升到 13 GB 以上才继续；编译、根模块、Axioms（261 条，2682 个声明，只有三条标准公理）与 Checks 都通过，'
     '`check_lean_fresh.py` 36 PASS（补丁 `patch_paper_2026-10-10_lean_saturated.py`）。'),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_cor815.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_cor815.log`）。同日第三项：新模块 `Saturated.lean`（论文推论 5.5，分母乘掉的形式；'
     '只用到上面第 5 节的 `RelU`、`OU`、`L1`、`mulOp` 与 `pureOp`，陈述由 AI 对照论文核对），经 `lean/lean_one.sh` 编译、'
     '重编根模块、重跑 `Axioms.lean`（261 条，2682 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` 36 项全部 '
     'PASS（`logs/check_lean_fresh_2026-10-10_sat.log`）。'),
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
