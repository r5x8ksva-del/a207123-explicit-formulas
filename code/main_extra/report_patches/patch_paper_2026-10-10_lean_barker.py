# -*- coding: utf-8 -*-
r"""Lean 续作第三十五项（2026-10-10）：报告 T5.4(2) 中 Colin Barker 在 A207118、A207069 的猜想，新模块
`lean/A207123/Barker.lean`：
- A207118（第 3 列）：`barker_A207118_even`、`barker_A207118_odd`（n 偶、奇时的六次闭式）、`barker_A207118_gf`
  （g.f. x(6+24x+…+x¹¹)/((1−x)^7(1+x)^5)）。
- A207069（2×n，`aAlt n 2`）：`barker_A207069_gf`（g.f. x(4+4x−…−x⁹)/((1−x)(1+x²−x³)(1−x−x³)(1−x−2x²−x³))）。
- 工具 `gf_of_rec`：由递推、前 d 项与整数表上的有限核对（`decide +kernel`）得母函数。
A326247 的三条要先形式化它在 OEIS 的原始定义，不在本项。
根模块加 import，Axioms 加 9 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_barker.log 读。
论文没有陈述 Barker 的猜想，只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A15 的 Barker 一句（A207118、A207069 已形式化，A326247 未形式化）。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_barker.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_barker.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '69'

PAPER_RE = [
    (r'consists of 60 files that start from', 'consists of 61 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`MCoeff.lean` 与 `Mobius.lean`）', '`MCoeff.lean`、`Mobius.lean` 与 `Barker.lean`）'),
    ('共 60 个模块（', '共 61 个模块（'),
    ('以及报告 T5.3(4) 的 Möbius 解释（Philip Hall 定理；论文没有陈述）后由 2675 增加',
     '以及报告 T5.3(4) 的 Möbius 解释（Philip Hall 定理）与 T5.4(2) 中 Barker 在 A207118、A207069 的猜想（这两项论文'
     '没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_mobius.py`。',
     '补丁 `patch_paper_2026-10-10_lean_mobius.py`。第三十五项：报告 T5.4(2) 中 Colin Barker 在 A207118、A207069 的'
     '猜想，新模块 `Barker.lean`（`barker_A207118_even`、`barker_A207118_odd`：a_3(n) 在 n 偶、奇时分别是 '
     '(n⁶+24n⁵+208n⁴+816n³+1600n²+1536n+576)/576、(n⁶+24n⁵+205n⁴+768n³+1315n²+936n+207)/576，由 a_3(2j) = U_3(j)²、'
     'a_3(2j+1) = U_3(j+1)U_3(j) 与 U_3 的闭式；`barker_A207118_gf`：(1−x)^7(1+x)^5·Σ_{n≥1} a_3(n)xⁿ = '
     'x(6+24x+6x²+x³+16x⁴−4x⁵−20x⁶+6x⁷+10x⁸−4x⁹−2x¹⁰+x¹¹)；`barker_A207069_gf`：'
     '(1−x)(1+x²−x³)(1−x−x³)(1−x−2x²−x³)·Σ_{n≥1} a(n)xⁿ = x(4+4x−4x²−7x³+x⁴+3x⁵+3x⁶+x⁷−x⁸−x⁹)，a(n) 是 A207069 '
     '标题规则下 2×n 矩阵的个数 `aAlt n 2`；工具 `gf_of_rec`：由递推（`parity_recurrence`、`oeis_A207069`）、前 d 项'
     '（闭式，或内核里算的 `rowList`）与整数表上的 `decide +kernel` 核对得母函数）。A326247 的三条要先形式化它在 OEIS '
     '的原始定义，不在这一项。改过两处 API 用法后编译通过（24 s、峰值 8.1 GB）。Axioms %d 条，全量扫描 %s 个声明，'
     '只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_barker.py`。'
     % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_mobius.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_mobius.log`）。同日第三十五项：新模块 `Barker.lean`（报告 T5.4(2) 中 Barker 在 '
     'A207118、A207069 的猜想）。没有新的承重定义：陈述只用 `a`、`aAlt`（A207069 标题里的列规则，已核对）、`aSer`、'
     '`PowerSeries.mk` 与显式多项式；A207118 的 `a(n)` 是 `a 3 n`，OEIS 从 n = 1 编号，所以 g.f. 写成 '
     '`aSer 3 − 1`（a_3(0) = 1）；A207069 的 `a(n)` 是 `aAlt n 2`，同样减去 `aAlt 0 2 = 1`。经 `lean/lean_one.sh` 编译、'
     '重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`（输出不变），'
     '`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_barker.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('| ■■■■■（列方向与行方向）；■■■■□（Barker 的猜想） |',
     '| ■■■■■（列方向与行方向，Barker 在 A207118、A207069 的猜想）；■■■■□（Barker 在 A326247 的猜想） |'),
    ('；Barker 的猜想未形式化 |',
     '；Barker 在 A207118（g.f. 与 n 偶、奇时的闭式）与 A207069（g.f.）的猜想 2026-10-10 已形式化（`Barker.lean` 的 '
     '`barker_A207118_gf`、`barker_A207118_even`、`barker_A207118_odd`、`barker_A207069_gf`）；A326247 的三条未形式化 |'),
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
    patch(os.path.join(ROOT, 'paper', 'main.tex'), [], PAPER_RE)
    patch(os.path.join(ROOT, 'README.md'), README, README_RE)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)
    patch(os.path.join(ROOT, '猜想总表.md'), TABLE)


if __name__ == '__main__':
    main()
