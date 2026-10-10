# -*- coding: utf-8 -*-
r"""Lean 续作第五十项（2026-10-10）：「每个 i 两个原子」的存在例子——猜想总表 A25 (d) 的 m ≤ 2（notes/12 定理 3 的两个式子）
与 A26 (iii) 的 q ≤ 3（notes/13 注 5.2 的两个式子）。新模块 `lean/A207123/TwoAtoms.lean`：
- `U_one_two_atoms`：一切 k 有 U_k(1) = c_1(k+2) + c_1(k+1) − 1（`U_one_atoms` 是 T2.5(3) 直接给出的等价写法
  c_1(k+3) + c_1(k−2) − 1）。
- `U_two_two_atoms`：k = 0 与 k ≥ 2 时 U_k(2) = 1/2 − ¼c_1(k+10) + ¼c_1(k−4) + (5/2)c_2(k+3) + 6c_2(k−2)；
  `U_two_two_atoms_one`：k = 1 时不成立（3 ≠ 11/4）。
- `N_two_two_atoms`：k ≥ 1 时 N(k,2) = c_1(k+3) + c_1(k−2) − 3；`N_three_two_atoms`：k ≥ 1 时
  N(k,3) = 13/2 − c_1(k+8) − 2c_1(k−2) + (5/2)c_2(k+3) + 6c_2(k−2)；`N_three_two_atoms_zero`：k = 0 时不成立。
- 证明：U_k(1)、U_k(2) 由 `U_F4` 在 m = 1、2 展开（`U_two_atoms_F4`），N 由容斥式 `N_eq_sum_U` 化为 U_k(0..2)，剩下的
  c_1、c_2 恒等式是递推的线性组合（`ci_one_id_C1`、`ci_two_id_C2`、`ci_one_id_C3`），小的 k 代入数值。
根模块加 import，Axioms 加 11 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_twoatoms.log 读。
论文没有陈述这些例子：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A25、A26 的 Lean 一句。
每处替换断言原文出现一次；先在内存里改完全部文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_twoatoms.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_twoatoms.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '84'

PAPER_RE = [
    (r'consists of 75 files that start from', 'consists of 76 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`NThreeAtoms.lean` 与 `HNegOneProd.lean`）', '`NThreeAtoms.lean`、`HNegOneProd.lean` 与 `TwoAtoms.lean`）'),
    ('共 75 个模块（', '共 76 个模块（'),
    ('，notes/16 命题 4(i) 的乘积式 h_k(−1) = 2(−1)^r∏(1+2z_l)（这些论文都没有陈述）后由 2675 增加',
     '，notes/16 命题 4(i) 的乘积式 h_k(−1) = 2(−1)^r∏(1+2z_l)，猜想总表 A25 (d)、A26 (iii) 中「每个 i 两个原子」在 '
     'm ≤ 2、q ≤ 3 时的存在例子（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_hnegoneprod.py`。',
     '补丁 `patch_paper_2026-10-10_lean_hnegoneprod.py`。第五十项：猜想总表 A25 (d) 与 A26 (iii) 的存在部分，新模块 '
     '`TwoAtoms.lean`（`U_one_two_atoms`：一切 k 有 U_k(1) = c_1(k+2) + c_1(k+1) − 1（notes/12 定理 3 的 m = 1；'
     '`U_one_atoms` 是 T2.5(3) 直接给出的等价写法 c_1(k+3) + c_1(k−2) − 1）；`U_two_two_atoms`：k = 0 与 k ≥ 2 时 '
     'U_k(2) = 1/2 − ¼c_1(k+10) + ¼c_1(k−4) + (5/2)c_2(k+3) + 6c_2(k−2)，k = 1 时不成立（`U_two_two_atoms_one`：'
     '3 ≠ 11/4）；`N_two_two_atoms`、`N_three_two_atoms`：k ≥ 1 时 N(k,2) = c_1(k+3) + c_1(k−2) − 3、'
     'N(k,3) = 13/2 − c_1(k+8) − 2c_1(k−2) + (5/2)c_2(k+3) + 6c_2(k−2)，后者 k = 0 时不成立'
     '（`N_three_two_atoms_zero`）；证明：U_k(1)、U_k(2) 由 T2.5(3) 的 `U_F4` 在 m = 1、2 展开（`U_two_atoms_F4`），'
     'N 由容斥式 `N_eq_sum_U` 化为 U_k(0..2)，剩下的 c_1、c_2 恒等式是递推的线性组合（`ci_one_id_C1`、'
     '`ci_two_id_C2`、`ci_one_id_C3`），小的 k 代入数值（`ci_one_vals`、`ci_two_vals`）；notes/12、notes/13 用的是'
     '「两边满足同一个 7 阶递推、核对前几项」的论证，这里换成直接的恒等式）。A25 (d) 的「m ≥ 3 不存在」与 A26 (iii) '
     '的「4 ≤ q ≤ 30 不存在」是计算机辅助证书，仍未形式化。编译改了一轮（两处 `norm_num <;> ring` 被 linter 提示，'
     '改成顺序执行；又补了 notes/12 原文的 m = 1 写法 `U_one_two_atoms`），最终无错误、无警告（39 s、峰值 8.1 GB）。'
     '论文没有陈述这些例子，只改第 9 节计数。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；'
     '`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_twoatoms.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_hnegoneprod.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_hnegoneprod.log`）。同日第五十项：新模块 `TwoAtoms.lean`（猜想总表 A25 (d) '
     '的 m ≤ 2、A26 (iii) 的 q ≤ 3 的存在例子）。没有新的承重定义：陈述只用到已核对的 `U`、`N`、`ci` 与 `ciZ`'
     '（c_i(n) = [xⁿ]1/b_i，n < 0 时取 0，与 notes/12 定理 3「c_i(n) := 0（n < 0）」的约定一致）；式子与 notes/12 '
     '定理 3、notes/13 注 5.2 逐项对照（原子下标 k+2、k+1、k+10、k−4、k+3、k−2、k+8 与系数照抄；适用范围 k ≥ 0、'
     'k = 0 与 k ≥ 2、k ≥ 1 也照抄，两处例外 k = 1、k = 0 另外形式化为不等式）。`ciZ_of_neg` 只是 `ciZ` 定义的直接推论。'
     '经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`'
     '（输出不变），`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_twoatoms.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；(a)、(c)、(d) 未形式化 |',
     '；(d) 的存在部分（m ≤ 2：U_k(1) = c_1(k+2) + c_1(k+1) − 1 对一切 k；例子 U_k(2) = 1/2 − ¼c_1(k+10) + ¼c_1(k−4) '
     '+ (5/2)c_2(k+3) + 6c_2(k−2) 对 k = 0 与 k ≥ 2，k = 1 时不成立）2026-10-10 也已形式化（`TwoAtoms.lean` 的 '
     '`U_one_two_atoms`、`U_two_two_atoms`、`U_two_two_atoms_one`：由 T2.5(3) 的 `U_F4` 在 m = 1、2 展开，再用 c_i 递推'
     '的线性组合）；(a)、(c) 与 (d) 的「m ≥ 3 不存在」（计算机辅助证书）未形式化 |'),
    ('；(ii) 的「每个 i 一个原子不存在」与「沿最高对角线的系数不是 P-递推的」（归结为 A25(c)），以及 (i)、(iii)、(iv) '
     '未形式化 |',
     '；(iii) 的存在例子（q = 2：N(k,2) = c_1(k+3) + c_1(k−2) − 3；q = 3：N(k,3) = 13/2 − c_1(k+8) − 2c_1(k−2) + '
     '(5/2)c_2(k+3) + 6c_2(k−2)；都对 k ≥ 1，q = 3 的式子在 k = 0 不成立）2026-10-10 也已形式化（`TwoAtoms.lean` 的 '
     '`N_two_two_atoms`、`N_three_two_atoms`、`N_three_two_atoms_zero`：由容斥式化为 U_k(0..2)，再用 c_1、c_2 递推的'
     '线性组合，代替 notes/13 的「同一个 7 阶递推、核对 1 ≤ k ≤ 7」）；(ii) 的「每个 i 一个原子不存在」与「沿最高对角线'
     '的系数不是 P-递推的」（归结为 A25(c)），以及 (i)、(iii) 的「4 ≤ q ≤ 30 不存在」（计算机辅助证书）、(iv) 未形式化 |'),
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
