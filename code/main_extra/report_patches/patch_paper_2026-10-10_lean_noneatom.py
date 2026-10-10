# -*- coding: utf-8 -*-
r"""Lean 续作第五十三项（2026-10-10）：notes/13 定理 5(a)（猜想总表 A26 (ii) 的「每个 i 一个原子不存在」）——q ≥ 2 时
N(k,q) 没有 Σ_{i=0}^{q−1} γ(i)·c_i(k+δ(i)) 形式的单和（复数系数）。新模块 `lean/A207123/NOneAtom.lean`：
- `N_no_one_atom_rat`：由第四十八项的唯一性 `N_three_atoms_unique` 落到纤维 1，范数 N(f) = det f(M_1) 给出
  γ(1)³ = 3·det S，S = Σ_M c_M·Y^{q−1−M}（`nOneCoeff`，Y = M_1³）；乘以 ((q−2)!·(−1)^q)³ 后是整数矩阵
  T_q = Σ_M C(q,M+1)·(q−2)^{\underline{q−1−M}}·Y^{q−1−M}（`TZ`、`nOneCoeff_mul`）的行列式。
- 模 3：`three_dvd_nCoefZ`（q−1−M ≥ 2 时系数被 3 整除）、`det_TZ_zmod_ne_zero`（T_q ≡ 1 + q(q−2)·Y，行列式模 3 为 1）；
  `cube_ne_three_mul_int`（3 ∤ D 时 a³ ≠ 3D）。
- `N_no_one_atom`：复数系数（`one_atom_rat_of_complex`）。
根模块加 import，Axioms 加 6 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_noneatom.log 读。
论文没有陈述 A26：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A26 的 Lean 一句。
每处替换断言原文出现一次；先在内存里改完全部文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_noneatom.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_noneatom.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '87'

PAPER_RE = [
    (r'consists of 78 files that start from', 'consists of 79 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`OneAtom.lean` 与 `OneAtomE.lean`）', '`OneAtom.lean`、`OneAtomE.lean` 与 `NOneAtom.lean`）'),
    ('共 78 个模块（', '共 79 个模块（'),
    ('，notes/12 定理 2(a)（每个 i 一个原子的单和不存在：U 与以上升结尾的 E）（这些论文都没有陈述）后由 2675 增加',
     '，notes/12 定理 2(a)（每个 i 一个原子的单和不存在：U 与以上升结尾的 E），notes/13 定理 5(a)（N 的同一结论）'
     '（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_oneatome.py`。',
     '补丁 `patch_paper_2026-10-10_lean_oneatome.py`。第五十三项：notes/13 定理 5(a)（猜想总表 A26 (ii) 的「每个 i 一个'
     '原子不存在」），新模块 `NOneAtom.lean`（`N_no_one_atom`：q ≥ 2 时不存在复数 γ(i)、整数 δ(i)（0 ≤ i ≤ q−1）使 '
     'N(k,q) = Σ_i γ(i)·c_i(k+δ(i)) 对充分大的 k 成立。证明：化成有理系数后由第四十八项的唯一性 '
     '`N_three_atoms_unique` 落到纤维 1，范数 N(f) = det f(M_1) 给出 γ(1)³ = 3·det S，S = Σ_{M=1}^{q−1} c_M·Y^{q−1−M}'
     '（`nOneCoeff`，Y = M_1³）；乘以 ((q−2)!·(−1)^q)³ 后是整数矩阵 T_q = Σ_M C(q,M+1)·(q−2)^{\\underline{q−1−M}}·'
     'Y^{q−1−M}（`TZ`、`nOneCoeff_mul`）的行列式；模 3 时 q−1−M ≥ 2 的系数被 3 整除（`three_dvd_nCoefZ`：j ≥ 3 时 '
     'j! 整除下降阶乘，j = 2 时用 C(q,2)C(q−2,2) = 6C(q,4)），T_q ≡ 1 + q(q−2)·Y、q(q−2) ≡ 0 或 2，两种情形行列式模 3 '
     '都是 1（`det_TZ_zmod_ne_zero`），于是 (γ(1)(q−2)!(−1)^q)³ = 3·det T_q 而 3 ∤ det T_q，与 3 进赋值矛盾'
     '（`cube_ne_three_mul_int`）。这就是 notes/13 的「T_{q−2}(z) 模 3 是 Z[ξ] 的单位，3·N(T_{q−2}(z)) 不是立方」'
     '（T_q = Y^{q−2}·T_{q−2}(Y^{−1})），整数矩阵的行列式代替了 Z[ξ] 中的范数）。A26 (ii) 的「沿最高对角线的系数不是 '
     'P-递推的」（归结为 A25(c)）与 (i) 仍未形式化。编译改了一轮（`padicValInt` 取值在 ℕ，要补 `Nat.cast_zero`；'
     '`finset_sum_coeff` 已改名 `finsetSum_coeff`），最终无错误、无警告（35 s、峰值 8.1 GB）。论文没有陈述 A26，只改第 9 节'
     '计数。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_noneatom.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_oneatome.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_oneatome.log`）。同日第五十三项：新模块 `NOneAtom.lean`（notes/13 定理 5(a)）。'
     '主定理 `N_no_one_atom` 的陈述只用到已核对的 `N` 与 `ciZ`，与 notes/13「不存在复数 γ(i)、整数 δ(i)（0 ≤ i ≤ q−1）'
     '与 k_0，使 N(k,q) = Σ_i γ(i)·c_i(k+δ(i)) 对一切 k ≥ k_0 成立」逐项对照（求和 `range q` 即 0 ≤ i ≤ q−1）。'
     '`YZ`、`Ybar`、`nCoefZ`、`TZ`、`nOneCoeff` 只在证明里用。经 `lean/lean_one.sh` 编译、重编根模块、重跑 '
     '`Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 '
     'PASS（`logs/check_lean_fresh_2026-10-10_noneatom.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；(ii) 的「每个 i 一个原子不存在」与「沿最高对角线的系数不是 P-递推的」（归结为 A25(c)），以及 (i)、(iii) 的'
     '「4 ≤ q ≤ 30 不存在」（计算机辅助证书）、(iv) 未形式化 |',
     '；(ii) 的「每个 i 一个原子不存在」（notes/13 定理 5(a)）2026-10-10 也已形式化（`NOneAtom.lean` 的 '
     '`N_no_one_atom`：由 (ii) 的唯一性落到纤维 1，范数 det f(M_1) 给出 γ(1)³ = 3·det S；乘以 ((q−2)!)³ 后是整数矩阵 '
     'T_q（`TZ`）的行列式，T_q ≡ 1 + q(q−2)·Y (mod 3)、行列式模 3 为 1，与 3 进赋值矛盾，即 notes/13 的'
     '「T_{q−2}(z) 模 3 是单位」）；(ii) 的「沿最高对角线的系数不是 P-递推的」（归结为 A25(c)），以及 (i)、(iii) 的'
     '「4 ≤ q ≤ 30 不存在」（计算机辅助证书）、(iv) 未形式化 |'),
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
