# -*- coding: utf-8 -*-
r"""Lean 续作第五十二项（2026-10-10）：notes/12 定理 2(a) 的 E 部分（猜想总表 A25 (a)）——m ≥ 2 时以上升结尾的序列数
E_k(m) 没有「每个 i 一个原子」的单和 Σ_{i=0}^{m} γ(i)·c_i(k+δ(i))（复数系数）。新模块 `lean/A207123/OneAtomE.lean`：
- `EA`：H_k(m) 中以上升结尾的序列个数；`EA_add_NA`：E + NA = U（NA 是不以上升结尾的个数，已有 P_m·Σ NA xᵏ = 1）。
- `NA_F4`：m!·NA_k(m) = Σ_i (−1)^{m−i}C(m,i)·c_i(k+3m)（1/P_m 的部分分式）；`EA_F4_phi`：
  m!·E_k(m) = Σ_i (−1)^{m−i}C(m,i)·Φ_{W̃_i−1}(k+3m)；`EA_atoms_exists`：三原子表示。
- `EA_no_one_atom_rat`：唯一性取 i = 2，范数 N(f) = det f(M_2)（`M2`，N(x) = 1/2、N(1+2x²) = 2、N(W̃_2 − 1) = 17/8），
  17 进赋值得矛盾（`cube_mul_ne_seventeen_mul_cube`）；`one_atom_rat_of_complex`、`EA_no_one_atom`：复数系数。
根模块加 import，Axioms 加 11 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_oneatome.log 读。
论文没有陈述 A25：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A25 的 Lean 一句。
每处替换断言原文出现一次；先在内存里改完全部文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_oneatome.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_oneatome.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '86'

PAPER_RE = [
    (r'consists of 77 files that start from', 'consists of 78 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`TwoAtoms.lean` 与 `OneAtom.lean`）', '`TwoAtoms.lean`、`OneAtom.lean` 与 `OneAtomE.lean`）'),
    ('共 77 个模块（', '共 78 个模块（'),
    ('，notes/12 定理 2(a) 的 U 部分（每个 i 一个原子的单和不存在）（这些论文都没有陈述）后由 2675 增加',
     '，notes/12 定理 2(a)（每个 i 一个原子的单和不存在：U 与以上升结尾的 E）（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_oneatom.py`。',
     '补丁 `patch_paper_2026-10-10_lean_oneatom.py`。第五十二项：notes/12 定理 2(a) 的 E 部分（猜想总表 A25 (a)），新模块 '
     '`OneAtomE.lean`（`EA_no_one_atom`：m ≥ 2 时不存在复数 γ(i)、整数 δ(i) 使以上升结尾的序列数 E_k(m) = '
     'Σ_{i=0}^{m} γ(i)·c_i(k+δ(i)) 对充分大的 k 成立。新定义 `EA`：H_k(m) 中以上升结尾（`endsAsc`）的序列个数，'
     '`EA_add_NA`：E + NA = U。三原子表示：`NA_F4`（1/P_m 的部分分式，m!·NA_k(m) = Σ_i (−1)^{m−i}C(m,i)·c_i(k+3m)，'
     '由已有的 `alt_sum_bser_inv` 与 P_m·Σ NA xᵏ = 1）、`EA_F4_phi`（m!·E_k(m) = Σ_i (−1)^{m−i}C(m,i)·Φ_{W̃_i−1}(k+3m)）、'
     '`EA_atoms_exists`；唯一性 `atoms_lin_indep` 取 i = 2，范数 N(f) = det f(M_2)，M_2 是 K_2 中乘以 x 的矩阵（`M2`，'
     'b_2(M_2) = 0），N(x) = 1/2、N(1 + 2x²) = 2、N(W̃_2 − 1) = det(2M_2⁵ + 4M_2⁸) = 17/8（与 notes/12 一致），'
     '于是 γ(2)³·2^{±a}·8 = 17·κ³，17 进赋值得 3v = 1，矛盾（`cube_mul_ne_seventeen_mul_cube`）；复数系数用 ℚ-线性'
     '泛函化成有理系数（`one_atom_rat_of_complex`）。编译改了一轮（Finset 引理换了名字 '
     '`card_filter_add_card_filter_not`；一处 `congr 2` 已关掉目标；主定理里要显式给 `Fact (Nat.Prime 17)`），最终'
     '无错误、无警告（24 s、峰值 8.1 GB）。论文没有陈述 A25，只改第 9 节计数。Axioms %d 条，全量扫描 %s 个声明，只有'
     '三条标准公理；`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_oneatome.py`。'
     % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_oneatom.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_oneatom.log`）。同日第五十二项：新模块 `OneAtomE.lean`（notes/12 定理 2(a) 的 '
     'E 部分）。新的承重定义 `EA k m`：`L k m`（已核对）中 `endsAsc` 为真的序列个数，`endsAsc` 是「最后两项 x < y」'
     '（注记 5.2 一项已核对），与 notes/12「E（以上升结尾的序列数）」一致；`EA_add_NA` 说明它与不以上升结尾的 `NA` '
     '互补。主定理 `EA_no_one_atom` 的陈述与 notes/12 定理 2(a) 第二句逐项对照（m ≥ 2、复数 γ(i)、整数 δ(i)、'
     '0 ≤ i ≤ m、充分大的 k）。`M2` 只在证明里用。经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`'
     '（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_oneatome.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；(a) 的 E 部分（m ≥ 2）、(c) 与 (d) 的「m ≥ 3 不存在」（计算机辅助证书）未形式化 |',
     '；(a) 的 E 部分（m ≥ 2）2026-10-10 也已形式化（`OneAtomE.lean` 的 `EA_no_one_atom`：E_k(m)（`EA`，以上升结尾的'
     '序列数）= U − NA，三原子表示由 `U_F4_phi` 减去 1/P_m 的部分分式得到，唯一性取 i = 2，范数 N(f) = det f(M_2)'
     '（N(x) = 1/2、N(W̃_2 − 1) = 17/8），17 进赋值得矛盾）；(c) 与 (d) 的「m ≥ 3 不存在」（计算机辅助证书）未形式化 |'),
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
