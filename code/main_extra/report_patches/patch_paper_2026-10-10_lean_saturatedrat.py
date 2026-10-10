# -*- coding: utf-8 -*-
r"""Lean 续作第十三项（2026-10-10）：论文推论 5.5 按原样（有理函数系数）形式化，新模块 `lean/A207123/SaturatedRat.lean`：
不构造 𝒪(k,m) 这个环，而用 ℂ(k,m) 上的正规形描述 𝒪(k,m)·L1：`TUrat q a b = q_{ab} − q_{a,b−1} − q_{a−1,b} − (m − b)·q_{a−3,b}`
（论文式 (4)，系数在 ℂ(k,m) 中；系数为多项式时就是 OreDim.lean 的 `TU`，`TUrat_algebraMap`），「T ∈ 𝒪(k,m)·L1」写成
「存在有限支撑的 q，T 的正规形系数 t_{ab} = TUrat q a b」。`saturated_one_rat`（推论 5.5(1)）、`saturated_two_rat`
（推论 5.5(2)，𝒪(k,m)·L1 ∩ 𝒪 = 𝒪·L1）；取公分母用 `exists_common_den`（Mathlib 的
`IsLocalization.exist_integer_multiples`），化到 Saturated.lean 的两条。没有形式化：𝒪(k,m) 本身（作为环）的构造，以及
它的正规形唯一、右乘 L1 由式 (4)给出这两点。新定义 `TUrat` 由 AI 对照论文式 (4)核对。
根模块加 import，Axioms 加四条（共 310 条）；全量扫描的声明数从 logs/lean_axioms_2026-10-10_saturatedrat.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 推论 5.5 一行列出有理系数的两条与分母乘掉的
  两条；「Not formalized」里推论 5.5 那一步改为 𝒪(k,m) 本身的构造（形式版本用正规形与式 (4)描述 𝒪(k,m)L1）。
- paper/reviewer_guide.tex：第 2 节推论 5.5 去掉「with denominators cleared」；第 3 节第 4 条同步。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_saturatedrat.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_saturatedrat.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
FRESH = '46'

PAPER = [
    (r'Corollary~\ref{cor:saturated} & \lean{mul\_mem\_ideal\_of\_vanish}, \lean{mem\_ideal\_of\_mul\_mem\_ideal} '
     r'(with denominators cleared)\\',
     r'Corollary~\ref{cor:saturated} & \lean{saturated\_one\_rat}, \lean{saturated\_two\_rat}; with denominators cleared: '
     r'\lean{mul\_mem\_ideal\_of\_vanish}, \lean{mem\_ideal\_of\_mul\_mem\_ideal}\\'),
    (r'the passage between Corollary~\ref{cor:saturated}, which is stated for operators with rational coefficients, and '
     r'its formalized version with denominators cleared;',
     r'the construction of $\cO(k,m)$ itself (the formal version of Corollary~\ref{cor:saturated} describes $\cO(k,m)L_1$ '
     r'by normal forms and \eqref{eq:rightmult});'),
]
PAPER_RE = [
    (r'consists of 37 files that start from', 'consists of 38 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('Corollary 5.5 (with denominators cleared), Proposition 5.6', 'Corollary 5.5, Proposition 5.6'),
    ('and the choice of a common denominator in Corollary 5.5.',
     r'and the description of $\cO(k,m)L_1$ by normal forms that the formal Corollary 5.5 uses instead of constructing '
     r'$\cO(k,m)$.'),
]

README = [
    ('`OeisRemark.lean` 与 `ThreeTermRat.lean`）', '`OeisRemark.lean`、`ThreeTermRat.lean` 与 `SaturatedRat.lean`）'),
    ('共 37 个模块（', '共 38 个模块（'),
    ('（补丁 `patch_paper_2026-10-10_lean_threetermrat.py`）。',
     '（补丁 `patch_paper_2026-10-10_lean_threetermrat.py`）。第十三项：推论 5.5 按论文原样（有理函数系数）形式化，'
     '新模块 `SaturatedRat.lean`：不构造 𝒪(k,m) 这个环，而用 ℂ(k,m) 上的正规形描述 𝒪(k,m)·L1——`TUrat q a b = '
     'q_{ab} − q_{a,b−1} − q_{a−1,b} − (m − b)·q_{a−3,b}`（论文式 (4)；系数为多项式时就是 `TU`，`TUrat_algebraMap`），'
     '「T ∈ 𝒪(k,m)·L1」写成「存在有限支撑的 q，使 T 的正规形系数 t_{ab} = TUrat q a b」；`saturated_one_rat`'
     '（推论 5.5(1)）、`saturated_two_rat`（推论 5.5(2)，𝒪(k,m)·L1 ∩ 𝒪 = 𝒪·L1），取公分母用 `exists_common_den`'
     '（Mathlib 的 `IsLocalization.exist_integer_multiples`），化到 `Saturated.lean` 的两条。没有形式化：𝒪(k,m) 本身'
     '（作为环）的构造，以及它的正规形唯一、右乘 L1 由式 (4)给出这两点。第三次编译通过（前两次：数乘实例与 '
     '`Algebra.smul_def` 的模式对不上，`ext` 拆到了多项式系数），无警告。Axioms 310 条，全量扫描 %s 个声明，只有'
     '三条标准公理；`check_lean_fresh.py` %s PASS（补丁 `patch_paper_2026-10-10_lean_saturatedrat.py`）。' % (DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、定理 3\.2\(2\)\(3\)、注记 3\.3 的精确部分、'
     r'注记 3\.5 中不靠计算的部分、推论 5\.5、推论 5\.7（含有理系数的原样陈述）、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、定理 3.2(2)(3)、注记 3.3 的精确部分、'
     '注记 3.5 中不靠计算的部分、推论 5.5 与推论 5.7（都含有理系数的原样陈述）、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_threetermrat.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_threetermrat.log`）。同日第十三项：新模块 `SaturatedRat.lean`（论文推论 5.5 的'
     '有理函数系数原样陈述；新定义 `TUrat`（右乘 L1 的正规形公式，系数在 ℂ(k, m) 中，对应论文式 (4)）由 AI 对照论文'
     '核对；「T ∈ 𝒪(k,m)·L1」按正规形写成「t_{ab} = TUrat q a b」，这一描述本身（𝒪(k,m) 的正规形唯一、右乘 L1 的公式）'
     '没有形式化），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（310 条，%s 个声明，只有三条标准公理）与 '
     '`Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_saturatedrat.log`）。'
     % (DECLS, FRESH)),
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
    print('declarations:', DECLS)
    patch(os.path.join(ROOT, 'paper', 'main.tex'), PAPER, PAPER_RE)
    patch(os.path.join(ROOT, 'paper', 'reviewer_guide.tex'), GUIDE)
    patch(os.path.join(ROOT, 'README.md'), README, README_RE)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)


if __name__ == '__main__':
    main()
