# -*- coding: utf-8 -*-
r"""Lean 续作第四十六项（2026-10-10）：notes/12 定理 2(b)（猜想总表 A25 (b)）——以 c_i(n) = [xⁿ]1/b_i 为原子、每个 i
三个相邻原子 c_i(k+3m+σ−r)（r = 0, 1, 2）的单和对每个 m ≥ 0、每个整数 σ 存在且唯一，系数
γ_r(m,i) = (−1)^{m−i}/(i!(m−i)!)·a_r^{(σ)}(i)，a_r^{(σ)}(i) 是 x^σ·W̃_i 在 K_i = ℚ[x]/(b_i) 中约化代表的系数（与 m 无关）。
新模块 `lean/A207123/ThreeAtoms.lean`：
- 存在：`three_atoms_exists`。由 T2.5(3) 的部分分式式 `U_F4` 出发（`U_F4_phi`），Φ_θ(n) := [xⁿ]θ/b_i 只依赖 θ mod b_i
  （`phi_eq_of_dvd`），乘 x^s 是平移（`phi_X_pow_mul`），x⁻¹ ≡ 1 + i x²（`bpoly_dvd_inv_shift`），次数 ≤ 2 的代表给出三个
  相邻原子（`phi_of_natDegree_le_two`、`phi_Wtil_atoms`）。
- 唯一：`three_atoms_unique`、`atoms_lin_indep`。数列看成 ℚ 上的向量，E 为平移算子（`shiftE`）；n ↦ c_i(n+b) 最终被
  q_i(E) = E³ − E² − i 零化（`evZero_qpoly`），q_i 两两互素、也与 E − 1 互素（`isCoprime_qpoly`、
  `isCoprime_qpoly_X_sub_one`），Bezout 分离各分量（`evZero_of_coprime`），再由 c_i 的递推往回推出系数为零
  （`atomComb_evZero_imp`）。
- 合并为 `three_atoms`；`atomCoeff_normalized`：(−1)^{m−i}·i!(m−i)!·γ_r(m,i) 就是约化代表的系数。
根模块加 import，Axioms 加 16 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_threeatoms.log 读。
论文没有陈述 A25：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A25 的 Lean 一句。
每处替换断言原文出现一次；先在内存里改完全部文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_threeatoms.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_threeatoms.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '80'

PAPER_RE = [
    (r'consists of 71 files that start from', 'consists of 72 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`NumGcd.lean` 与 `A038718.lean`）', '`NumGcd.lean`、`A038718.lean` 与 `ThreeAtoms.lean`）'),
    ('共 71 个模块（', '共 72 个模块（'),
    ('，T5.4(3) 中允许行与 Hamilton 路的递归双射（这些论文都没有陈述）后由 2675 增加',
     '，T5.4(3) 中允许行与 Hamilton 路的递归双射，notes/12 定理 2(b)（猜想总表 A25 (b)：每个 i 三个相邻原子的单和'
     '存在且唯一）（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_a038718.py`。',
     '补丁 `patch_paper_2026-10-10_lean_a038718.py`。第四十六项：notes/12 定理 2(b)（猜想总表 A25 (b)），新模块 '
     '`ThreeAtoms.lean`（原子 c_i(n) = [xⁿ]1/b_i，n < 0 时取 0（`ciZ`）；`three_atoms`：对每个 m ≥ 0、每个整数 σ，k 充分大'
     '时 U_k(m) = (−1)^m/m! + Σ_{i=1}^{m} Σ_{r=0}^{2} γ_r(m,i)·c_i(k+3m+σ−r)，而且这样的表示唯一；系数 '
     '`atomCoeff`：γ_r(m,i) = (−1)^{m−i}/(i!(m−i)!)·a_r^{(σ)}(i)，a_r^{(σ)}(i) 是 x^σ·W̃_i 在 K_i = ℚ[x]/(b_i) 中约化代表的'
     '系数（`atomRep`，σ < 0 时用 x⁻¹ ≡ 1 + i x²；`atomCoeff_normalized`：与 m 无关）。存在：由 T2.5(3) 的部分分式式 '
     '`U_F4` 出发，Φ_θ(n) := [xⁿ]θ/b_i 只依赖 θ mod b_i、乘 x^s 是平移、次数 ≤ 2 的代表给出三个相邻原子（`phi_eq_of_dvd`、'
     '`phi_X_pow_mul`、`phi_of_natDegree_le_two`、`phi_Wtil_atoms`、`three_atoms_exists`）；唯一：把数列看成 ℚ 上的向量，'
     '平移算子 E（`shiftE`）的多项式 q_i(E) = E³ − E² − i 最终零化 n ↦ c_i(n+b)，q_i 两两互素、也与 E − 1 互素，用 Bezout '
     '分离各个 i 的分量，再由 c_i 的递推往回推出三个系数为零（`evZero_qpoly`、`evZero_of_coprime`、'
     '`atomComb_evZero_imp`、`atoms_lin_indep`、`three_atoms_unique`）；notes/12 的唯一性证明用的是线性递推数列的唯一分解'
     '（等价于母函数的部分分式唯一），这里换成了这条算子论证）。编译改了一轮（`if_pos`/`if_neg` 在这一版已弃用、'
     '`Int.neg_le_natAbs` 不在 `Int` 命名空间），最终无错误、无警告（27 s、峰值 8.1 GB）。论文没有陈述 A25，只改第 9 节'
     '计数。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_threeatoms.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_a038718.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_a038718.log`）。同日第四十六项：新模块 `ThreeAtoms.lean`（猜想总表 A25 (b)，'
     'notes/12 定理 2(b)）。主定理 `three_atoms` 的陈述用到已核对的 `U` 与 `ciZ`（c_i(n) = [xⁿ]1/b_i，n < 0 时取 0，'
     '与 notes/12 一致：充分大的 k 只用到非负下标），以及新定义 `atomCoeff`、`atomRep`、`xpowRep`：已与 notes/12 定理 '
     '2(b) 对照——`atomRep i σ` 是 (xpowRep i σ)·W̃_i 除以 b_i 的余式（次数 ≤ 2），`xpowRep i σ` 在 σ ≥ 0 时是 x^σ，在 σ < 0 '
     '时是 (1 + i x²)^{−σ}（K_i 中 x⁻¹ = 1 + i x²），所以余式就是 x^σ·W̃_i 在 K_i 中的约化代表，系数即 a_r^{(σ)}(i)；'
     '`atomCoeff m i σ r` = (−1)^{m−i}/(i!(m−i)!)·a_r^{(σ)}(i) 即 γ_r(m,i)，常数项 γ^{(0)} = (−1)^m/m!（引理 2.1 的 R_0）。'
     '`phi`、`shiftE`、`EvZero`、`qpoly`、`atomComb`、`atomSeq` 只在证明里用。经 `lean/lean_one.sh` 编译、重编根模块、'
     '重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项'
     '全部 PASS（`logs/check_lean_fresh_2026-10-10_threeatoms.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('平移随 m 变化而系数为闭式的写法。未形式化 |',
     '平移随 m 变化而系数为闭式的写法。(b)（存在且唯一，a_r^{(σ)}(i) 与 m 无关、是 x^σ·W̃_i 在 K_i 中约化代表的系数）'
     '2026-10-10 已形式化（`ThreeAtoms.lean` 的 `three_atoms`、`atomCoeff_normalized`：存在由 T2.5(3) 的部分分式式 '
     '`U_F4` 在 K_i 中约化得到；唯一由平移算子 E 的多项式 q_i(E) = E³ − E² − i 两两互素、Bezout 分离各分量，再由 c_i '
     '的递推得到）；(a)、(c)、(d) 未形式化 |'),
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
