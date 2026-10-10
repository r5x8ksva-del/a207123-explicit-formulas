# -*- coding: utf-8 -*-
r"""Lean 续作第四十一项（2026-10-10）：h_k 次高项的闭式与它和首项的符号关系（对一切 k；猜想总表 A29 (ii)，
notes/16 定理 3，c5a 定理 4.4(d)），新模块 `lean/A207123/HSecond.lean`：
- `upoly_eval_neg_second`、`hpoly_coeff_second`：互反式在 −(s_k+2) 处，h_{k,d−1} = (−1)^k(u_k(−s−2) − (k+1)u_k(−s−1))。
- `hpoly_second_three_mul`、`hpoly_second_three_mul_add_one`、`hpoly_second_three_mul_add_two`：三个剩余类的闭式
  (−1)^{a+1}·2a·a!、(−1)^a·B_1(a)、(−1)^a·B_2(a)。
- `hB2_pos`、`hB1_neg`、`hB1_pos`、`hE_pos`（整数递推）与有限核对 `hB1_table`、`hB1_fiftyfive`（内核求值）。
- `hpoly_second_sign`：k ≡ 0 异号、k ≡ 2 同号、k ≡ 1 时 k ≤ 163 异号、k ≥ 166 同号。
根模块加 import，Axioms 加 12 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_hsecond.log 读。
论文没有陈述这件事：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A29 的完成度与 Lean 一句。
每处替换断言原文出现一次；先在内存里改完四个文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_hsecond.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_hsecond.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '75'

PAPER_RE = [
    (r'consists of 66 files that start from', 'consists of 67 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`NumLow.lean` 与 `NegZerosTwo.lean`）', '`NumLow.lean`、`NegZerosTwo.lean` 与 `HSecond.lean`）'),
    ('共 66 个模块（', '共 67 个模块（'),
    ('T4.3(5) 对一切 j 的低次系数（2j 次多项式、首项与门槛）（这些论文都没有陈述）后由 2675 增加',
     'T4.3(5) 对一切 j 的低次系数（2j 次多项式、首项与门槛），T5.3(7) 中 h_k 次高项的闭式与它和首项的符号关系'
     '（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_negzerostwo.py`。',
     '补丁 `patch_paper_2026-10-10_lean_negzerostwo.py`。第四十一项：h_k 次高项的闭式与它和首项的符号关系，对一切 k'
     '（猜想总表 A29 (ii)，notes/16 定理 3、c5a 定理 4.4(d)），新模块 `HSecond.lean`（`upoly_eval_neg_second`、'
     '`hpoly_coeff_second`：互反式在 −(s_k+2) 处给出 h_{k,d−1} = (−1)^k(u_k(−s_k−2) − (k+1)u_k(−s_k−1))；代入 G_{−j} '
     '顶端各层的闭式得 `hpoly_second_three_mul`（k = 3a：(−1)^{a+1}·2a·a!）、`hpoly_second_three_mul_add_one`'
     '（k = 3a+1：(−1)^a·B_1(a)，B_1(a) = c(a+3,2) + c(a+3,3) − (a+2)! − (3a+2)c(a+2,2)）、'
     '`hpoly_second_three_mul_add_two`（k = 3a+2：(−1)^a·B_2(a)，B_2(a) = c(a+3,2) + c(a+3,3) − 3(a+1)(a+1)!）；'
     '`hB2_pos`：B_2 > 0；`hB1_neg`、`hB1_pos`：1 ≤ a ≤ 54 时 B_1 < 0、a ≥ 55 时 B_1 > 0，用整数递推 '
     'B_1(a+1) = (a+3)B_1(a) + E(a)（`hB1_succ`；`hE_pos`：a ≥ 9 时 E(a) = (a−2)c(a+2,2) − 2(a+1)(a+1)! > 0），'
     'notes/16 的 φ_1 与调和数改成了整数；a ≤ 55 的符号与 E(9) > 0 是有限核对，用内核求值 `decide +kernel`'
     '（`hB1_table`、`hB1_fiftyfive`，Stirling 数用线性递推的求值器 `c2v`、`c3v`，不引入公理）；汇总 '
     '`hpoly_second_sign`：k ≥ 3 时次高项与首项 k ≡ 0 (mod 3) 异号、k ≡ 2 同号、k ≡ 1 时 k ≤ 163 异号、k ≥ 166 同号）。'
     'A29 的 (i)（门槛 τ_1..τ_40，计算机辅助）与 (iii) 不在这里。编译前先改了一处（`push_cast [Nat.factorial_succ]` '
     '不展开 `(a+2)!`，改用 `fact_two_int`、`fact_three_int`），之后一次编译通过，无错误、无警告（38 s、峰值 8.1 GB）。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_hsecond.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_negzerostwo.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_negzerostwo.log`）。同日第四十一项：新模块 `HSecond.lean`（h_k 次高项的'
     '闭式与符号，A29 (ii)）。主定理 `hpoly_second_sign` 只用到已核对的 `hpoly`（h_k，`hpoly_spec`）及其次数、首项与'
     '系数；新定义 `hB1`、`hB2`、`hE` 已与 notes/16 §3 的 B_1(a)、B_2(a) 和递推里的差项逐项对照（c 是 Mathlib 的 '
     '`Nat.stirlingFirst`，即无符号第一类 Stirling 数），`c2v`、`c3v` 是求值器（`c2v_eq`、`c3v_eq` 证明它们等于 '
     'c(n+1,2)、c(n+1,3)），不承重。经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，'
     '只有三条标准公理；`hB1_table`、`hB1_fiftyfive` 不依赖任何公理）与 `Checks.lean`（输出不变），'
     '`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_hsecond.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('| ■■■■□（(i) 是计算机辅助；(iii) 的否定答案原是条件性的，2026-10-09 由 A30 变成无条件） |',
     '| ■■■■■（(ii)，2026-10-10）；■■■■□（(i) 是计算机辅助；(iii) 的否定答案原是条件性的，2026-10-09 由 A30 变成无条件） |'),
    ('(★) 本身已由 A30 证明（2026-10-09）。未形式化 |',
     '(★) 本身已由 A30 证明（2026-10-09）。(ii)（含 c5a 定理 4.4(d) 的三个闭式）2026-10-10 已形式化（`HSecond.lean`：'
     '`hpoly_second_three_mul`、`hpoly_second_three_mul_add_one`、`hpoly_second_three_mul_add_two`、`hpoly_second_sign`；'
     'B_1 的符号用整数递推，a≤55 的值由内核求值核对）；(i)(iii) 未形式化 |'),
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
