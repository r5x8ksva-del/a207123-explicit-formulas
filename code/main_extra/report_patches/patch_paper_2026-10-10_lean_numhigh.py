# -*- coding: utf-8 -*-
r"""Lean 续作第四十七项（2026-10-10）：报告 T4.3(6) 的 j = 2、3——Num_q 次高两项系数的闭式（猜想总表 A5 (6) 的一部分），
新模块 `lean/A207123/NumHigh.lean`：
- `Numq_coeff_step`：由三项递推 Num_q = (x + 2(q−1)x³)Num_{q−1} + (q−1)x³·b_{q−2}·Num_{q−2}（q ≥ 3）取 x^{n+6} 的系数。
- `Numq_three_eq`：Num_3 = 2x³ + 2x⁴ + 7x⁵ + 2x⁷；`Numq_coeff_top`：a_{q,0} = (q−1)!；`Numq_coeff_above`。
- `Numq_top_two`：[x^{3q−4}]Num_q = (q−1)!·(q − 1 + H_{q−1})；`Numq_top_three`：[x^{3q−5}]Num_q = (q−1)·(q−1)!·(H_{q−1} − 1)
  （q ≥ 2，H_n 为调和数，Mathlib 的 `harmonic`）；对 q 归纳，j = 0、1 的值（首项、`Numq_coeff_gap`）代入递推后化为调和数的
  恒等式。
根模块加 import，Axioms 加 5 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_numhigh.log 读。
论文没有陈述 T4.3：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A5 的 Lean 一句。
每处替换断言原文出现一次；先在内存里改完全部文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_numhigh.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_numhigh.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '81'

PAPER_RE = [
    (r'consists of 72 files that start from', 'consists of 73 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`A038718.lean` 与 `ThreeAtoms.lean`）', '`A038718.lean`、`ThreeAtoms.lean` 与 `NumHigh.lean`）'),
    ('共 72 个模块（', '共 73 个模块（'),
    ('（猜想总表 A25 (b)：每个 i 三个相邻原子的单和存在且唯一）（这些论文都没有陈述）后由 2675 增加',
     '（猜想总表 A25 (b)：每个 i 三个相邻原子的单和存在且唯一），T4.3(6) 中 j = 2、3 的次高两项系数闭式（这些论文都'
     '没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_threeatoms.py`。',
     '补丁 `patch_paper_2026-10-10_lean_threeatoms.py`。第四十七项：报告 T4.3(6) 的 j = 2、3（猜想总表 A5 (6) 的一部分），'
     '新模块 `NumHigh.lean`（a_{q,j} := [x^{3q−2−j}]Num_q；`Numq_top_two`：a_{q,2} = (q−1)!·(q − 1 + H_{q−1})，'
     '`Numq_top_three`：a_{q,3} = (q−1)·(q−1)!·(H_{q−1} − 1)，q ≥ 2，H_n 为调和数（Mathlib 的 `harmonic`）；证明：由三项'
     '递推 `Numq_three_term` 取 x^{n+6} 的系数得 a_{q,j} 的递推（`Numq_coeff_step`），代入 j = 0、1 的值（首项 (q−1)!、'
     '`Numq_coeff_gap`）后对 q 归纳，归纳步化为调和数的恒等式（`linear_combination`）；q = 2、3 直接核对，'
     '`Numq_three_eq`：Num_3 = 2x³ + 2x⁴ + 7x⁵ + 2x⁷）。一般 j 的结构（a_{q,j} 是第一类 Stirling 数 c(q,i) 的 ℚ[q] '
     '线性组合）与 T4.3(7) 的 e.g.f. 闭式仍未形式化。编译改了一轮（`C 4 = 4` 要显式用 `map_ofNat`），最终无错误、无警告'
     '（22 s、峰值 8.1 GB）。论文没有陈述 T4.3，只改第 9 节计数。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；'
     '`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_numhigh.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_threeatoms.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_threeatoms.log`）。同日第四十七项：新模块 `NumHigh.lean`（报告 T4.3(6) 的 '
     'j = 2、3）。没有新的承重定义：陈述只用到已核对的 `Numq` 与 Mathlib 的 `harmonic`（harmonic n = Σ_{i<n} 1/(i+1)，'
     '即报告的 H_n）；系数下标 3q − 4、3q − 5 就是报告的 3q − 2 − j（j = 2、3，q ≥ 2 时不出现自然数减法截断）。经 '
     '`lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`'
     '（输出不变），`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_numhigh.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；(6)(7) 未形式化 |',
     '；(6) 的 j = 2、3（a_{q,2} = (q−1)!(q−1+H_{q−1})、a_{q,3} = (q−1)(q−1)!(H_{q−1}−1)，q ≥ 2）2026-10-10 已形式化'
     '（`NumHigh.lean` 的 `Numq_top_two`、`Numq_top_three`：由三项递推推出 a_{q,j} 的递推 `Numq_coeff_step`，对 q 归纳；'
     'j = 0、1 即 `leadingCoeff_Numq`、`Numq_coeff_gap`）；(6) 的一般结构与 (7) 未形式化 |'),
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
