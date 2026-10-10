# -*- coding: utf-8 -*-
r"""Lean 续作第十五项（2026-10-10）：论文注记 3.3 的数值形式化（区间算术），新模块 `lean/A207123/AsympNumerics.lean`：
ρ_m 的有理区间（三次式变号，`lt_rho_of_cubic`、`rho_lt_of_cubic`）、c_m = N(ρ_m)/D(ρ_m) 的区间（`cm_eq_frac`、`cm_bounds`；
有理点上的 N、D 用可在内核里求值的 `cmNQ`、`cmDQ`，比较用 decide +kernel）、κ_m 的区间（`kappa_mem`）、U_k(m) 的精确值
（`OeisRows.lean` 的 `Ucol`）。论文的数值说法（「≈ x」理解为与 x 之差小于末位的半个单位）：`rho_one_approx`、
`cm_one_approx`、`cm_two_approx`、`cm_three_approx`、`kappa_one_approx`、`kappa_four_approx`、`kappa_twentyfour_approx`、
`kappa_increasing`（1 ≤ m ≤ 24 内递增）、`relerr_two_six`、`relerr_two_twenty`、`relerr_twentyfour_seventytwo`、
`relerr_twentyfour_twoforty`。区间端点与数值引理由 `code/main_extra/remark33_numerics_lean.py` 生成并在 Python 里核对。
新定义 `cmN`、`cmD`、`cmTailQ`、`cmNQ`、`cmDQ` 由 AI 核对（`cm_eq_frac`、`cmNQ_cast`、`cmDQ_cast` 证明它们与 c_m 一致）。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_asympnumerics.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 注记 3.3 一行去掉「exact parts」并加上数值的
  十二个名字；「Not formalized」去掉注记 3.3 的数值。
- paper/reviewer_guide.tex：第 2 节注记 3.3 一句；第 3 节第 5 条只剩行递推阶的最小性。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_asympnumerics.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_asympnumerics.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '48'

ROW33 = (r'Remark~\ref{rem:asym}, exact parts & \lean{tendsto\_ratio}, \lean{rate\_not\_improvable}, \lean{cm\_one}, '
         r'\lean{rho\_int\_iff}, \lean{cm\_four}, \lean{U\_four\_asymp}, \lean{tendsto\_one\_sub\_theta}\\')
PAPER = [
    (ROW33,
     r'Remark~\ref{rem:asym} & \lean{tendsto\_ratio}, \lean{rate\_not\_improvable}, \lean{cm\_one}, '
     r'\lean{rho\_int\_iff}, \lean{cm\_four}, \lean{U\_four\_asymp}, \lean{tendsto\_one\_sub\_theta}; numerical values: '
     r'\lean{rho\_one\_approx}, \lean{cm\_one\_approx}, \lean{cm\_two\_approx}, \lean{cm\_three\_approx}, '
     r'\lean{kappa\_one\_approx}, \lean{kappa\_four\_approx}, \lean{kappa\_twentyfour\_approx}, \lean{kappa\_increasing}, '
     r'\lean{relerr\_two\_six}, \lean{relerr\_two\_twenty}, \lean{relerr\_twentyfour\_seventytwo}, '
     r'\lean{relerr\_twentyfour\_twoforty}\\'),
    (r'the numerical values in Remark~\ref{rem:asym}; ', ''),
]
PAPER_RE = [
    (r'consists of 39 files that start from', 'consists of 40 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('with the exact statements of Remark 3.3,', 'with Remark 3.3 (its numerical values by interval arithmetic),'),
    (r'\item \textbf{Section 3:} the numerical values in Remark 3.3 and the minimality of the orders of the row '
     r'recurrences in Remark 3.5.',
     r'\item \textbf{Section 3:} the minimality of the orders of the row recurrences in Remark 3.5.'),
]

README = [
    ('`SaturatedRat.lean` 与 `OeisRows.lean`）', '`SaturatedRat.lean`、`OeisRows.lean` 与 `AsympNumerics.lean`）'),
    ('共 39 个模块（', '共 40 个模块（'),
    ('回到 38 页、无警告，各节与附录页码不变）。',
     '回到 38 页、无警告，各节与附录页码不变）。第十五项：注记 3.3 的数值，新模块 `AsympNumerics.lean`，区间算术：ρ_m 的有理区间由三次式变号得出'
     '（`lt_rho_of_cubic`、`rho_lt_of_cubic`）；c_m = N(ρ_m)/D(ρ_m)（`cm_eq_frac`），N、D 都随 x 增，故 '
     'N(lo)/D(hi) ≤ c_m ≤ N(hi)/D(lo)（`cm_bounds`）；有理点上的 N、D 用可在内核里求值的 `cmNQ`、`cmDQ`，比较用 '
     '`decide +kernel`；κ_m 的区间由 `kappa_mem` 得出；U 的精确值用 `Ucol`。论文的数值说法（「≈ x」理解为与 x 之差小于末位的'
     '半个单位）全部形式化：`rho_one_approx`、`cm_one_approx`、`cm_two_approx`、`cm_three_approx`、`kappa_one_approx`、'
     '`kappa_four_approx`、`kappa_twentyfour_approx`、`kappa_increasing`（1 ≤ m ≤ 24 内递增）、`relerr_two_six`、'
     '`relerr_two_twenty`、`relerr_twentyfour_seventytwo`、`relerr_twentyfour_twoforty`。区间端点由 '
     '`code/main_extra/remark33_numerics_lean.py` 用精确分数选出并核对（ρ 的区间宽 10^−12），数值引理由它生成。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_asympnumerics.py`。'
     % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、定理 3\.2\(2\)\(3\)、注记 3\.3 的精确部分、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、定理 3.2(2)(3)、注记 3.3（含数值）、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_oeisrows.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_oeisrows.log`）。同日第十五项：新模块 `AsympNumerics.lean`（论文注记 3.3 的'
     '数值，区间算术；新定义 `cmN`、`cmD`、`cmTailQ`、`cmNQ`、`cmDQ` 由 AI 核对，其中 `cm_eq_frac`、`cmNQ_cast`、`cmDQ_cast` '
     '证明它们与 c_m 一致；「≈ x」理解为与 x 之差小于末位的半个单位），经 `lean/lean_one.sh` 编译、重编根模块、重跑 '
     '`Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_asympnumerics.log`）。' % (_ax, DECLS, FRESH)),
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
