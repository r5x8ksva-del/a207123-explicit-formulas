# -*- coding: utf-8 -*-
r"""Lean 续作第五十一项（2026-10-10）：notes/12 定理 2(a) 的 U 部分（猜想总表 A25 (a)）——m ≥ 1 时不存在复数 γ(i)、
整数 δ(i)（0 ≤ i ≤ m）使 U_k(m) = Σ_{i=0}^{m} γ(i)·c_i(k+δ(i)) 对充分大的 k 成立。新模块 `lean/A207123/OneAtom.lean`：
- `U_no_one_atom`：取 ℚ-线性泛函 ψ : ℂ → ℚ、ψ(1) = 1，化成有理系数 `U_no_one_atom_rat`。
- `phi_atoms`、`ciZ_eq_atoms`：单个原子换成三个相邻原子（x^{3m−δ} 在 K_i 中的约化代表）；由第四十六项的唯一性
  `three_atoms_unique`（σ = 0）得 i = 1 处 γ(1)·x^{3m−δ(1)} ≡ (−1)^{m−1}/(m−1)!·W̃_1 (mod b_1)。
- 范数 N(f) = det f(M_1)，`M1` 是 K_1 中乘以 x 的矩阵（`aeval_M1_bpoly`：b_1(M_1) = 0）；N(x^σ) = 1、N(W̃_1) = 3
  （`det_aeval_M1_xpowRep`、`det_aeval_M1_atomRep`）；`rat_cube_ne_three`：3 不是有理数的立方。
根模块加 import，Axioms 加 8 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_oneatom.log 读。
论文没有陈述 A25：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A25 的 Lean 一句。
每处替换断言原文出现一次；先在内存里改完全部文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_oneatom.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_oneatom.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '85'

PAPER_RE = [
    (r'consists of 76 files that start from', 'consists of 77 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`HNegOneProd.lean` 与 `TwoAtoms.lean`）', '`HNegOneProd.lean`、`TwoAtoms.lean` 与 `OneAtom.lean`）'),
    ('共 76 个模块（', '共 77 个模块（'),
    ('，猜想总表 A25 (d)、A26 (iii) 中「每个 i 两个原子」在 m ≤ 2、q ≤ 3 时的存在例子（这些论文都没有陈述）后由 2675 增加',
     '，猜想总表 A25 (d)、A26 (iii) 中「每个 i 两个原子」在 m ≤ 2、q ≤ 3 时的存在例子，notes/12 定理 2(a) 的 U 部分'
     '（每个 i 一个原子的单和不存在）（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_twoatoms.py`。',
     '补丁 `patch_paper_2026-10-10_lean_twoatoms.py`。第五十一项：notes/12 定理 2(a)（猜想总表 A25 (a)）的 U 部分，新模块 '
     '`OneAtom.lean`（`U_no_one_atom`：m ≥ 1 时不存在复数 γ(i)、整数 δ(i)（0 ≤ i ≤ m）使 U_k(m) = Σ_{i=0}^{m} '
     'γ(i)·c_i(k+δ(i)) 对充分大的 k 成立。证明：取 ℚ-线性泛函 ψ : ℂ → ℚ、ψ(1) = 1 作用在等式两边，化成有理系数'
     '（`U_no_one_atom_rat`）；把单个原子换成三个相邻原子（`ciZ_eq_atoms`，由一般的 `phi_atoms`：'
     'Φ_θ(n) = Σ_r [x^r](x^σθ mod b_i)·c_i(n+σ−r)），由第四十六项的唯一性 `three_atoms_unique`（σ = 0）得 i = 1 处 '
     'γ(1)·x^{3m−δ(1)} ≡ (−1)^{m−1}/(m−1)!·W̃_1 (mod b_1)；范数取 N(f) = det f(M_1)，M_1 是 K_1 中乘以 x 的 3×3 矩阵'
     '（`M1`，b_1(M_1) = 0：`aeval_M1_bpoly`），N 只依赖 f mod b_1、可乘，N(x^σ) = 1、N(W̃_1) = det(1 + M_1⁵) = 3'
     '（`det_aeval_M1_xpowRep`、`det_aeval_M1_atomRep`），于是 γ(1)³ = 3·((−1)^{m−1}/(m−1)!)³，与「3 不是有理数的立方」'
     '（`rat_cube_ne_three`，3 进赋值）矛盾；notes/12 用三个共轭相等推出 θ ∈ ℚ，这里由唯一性直接得到系数是有理数）。'
     'E（以上升结尾，m ≥ 2）的情形未形式化。编译改了一轮（`hall` 里的 k 被推断成整数，要写 `k : ℕ`；r ≥ 3 时少一步 '
     '`mul_zero`；去掉几个用不到的 simp 参数），最终无错误、无警告（36 s、峰值 8.0 GB）。论文没有陈述 A25，只改第 9 节'
     '计数。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_oneatom.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_twoatoms.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_twoatoms.log`）。同日第五十一项：新模块 `OneAtom.lean`（notes/12 定理 2(a) 的 '
     'U 部分）。主定理 `U_no_one_atom` 的陈述只用到已核对的 `U` 与 `ciZ`，与 notes/12「不存在复数 γ(i)、整数 δ(i)'
     '（0 ≤ i ≤ m）与 k_0，使 U_k(m) = Σ_{i=0}^{m} γ(i)·c_i(k+δ(i)) 对一切 k ≥ k_0 成立」逐项对照（`∀ᶠ k in atTop` 即'
     '「存在 k_0」；i = 0 的原子 c_0 ≡ 1；c_i 在负下标取 0 不影响「充分大的 k」）。新定义 `M1`（K_1 中乘以 x 的矩阵）'
     '只在证明里用。经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）'
     '与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_oneatom.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；(a)、(c) 与 (d) 的「m ≥ 3 不存在」（计算机辅助证书）未形式化 |',
     '；(a) 的 U 部分（m ≥ 1，复数系数）2026-10-10 也已形式化（`OneAtom.lean` 的 `U_no_one_atom`：先用 ℚ-线性泛函 ψ'
     '（ψ(1) = 1）化成有理系数，再把每个原子换成三个相邻原子、由 (b) 的唯一性得到 i = 1 处 '
     'γ(1)·x^{3m−δ(1)} ≡ (−1)^{m−1}/(m−1)!·W̃_1 (mod b_1)，取范数 N(f) = det f(M_1)（M_1 是 K_1 中乘以 x 的矩阵，'
     'N(x) = 1、N(W̃_1) = 3）得 3 是有理数的立方，与 3 进赋值矛盾；notes/12 用三个共轭相等推出 θ ∈ ℚ，这里由唯一性'
     '直接得到）；(a) 的 E 部分（m ≥ 2）、(c) 与 (d) 的「m ≥ 3 不存在」（计算机辅助证书）未形式化 |'),
]


def patched(path, reps, regex=()):
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
    return s, len(reps) + len(regex)


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    print('declarations:', DECLS, ' Axioms lines:', _ax)
    jobs = [(os.path.join(ROOT, 'paper', 'main.tex'), [], PAPER_RE),
            (os.path.join(ROOT, 'README.md'), README, README_RE),
            (os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST, ()),
            (os.path.join(ROOT, '猜想总表.md'), TABLE, ())]
    out = [(path,) + patched(path, reps, regex) for path, reps, regex in jobs]
    for path, s, n in out:
        open(path, 'wb').write(s.encode('utf-8'))
        print('%s: %d edits' % (os.path.relpath(path, ROOT), n))


if __name__ == '__main__':
    main()
