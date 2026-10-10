# -*- coding: utf-8 -*-
r"""Lean 续作第七项（2026-10-10）：论文注记 5.2（不以上升结尾的序列与 ₁F₁）形式化，新模块 `lean/A207123/EndAscent.lean`：
`P_mul_NAser`（P_m·Σ_k NA_k(m) x^k = 1，NA_k(m) 是 H_k(m) 中不以上升结尾的序列个数，即 1/P_m 的 x^k 系数）、
`remark_1F1`（在 ℚ(x)[[t]] 中 Σ_m t^m/P_m = (1/(1 − x))·₁F₁(1; 1 − λ; −t/x³)，λ = (1 − x)/x³；一般形式
`sum_inv_P_eq_hyp1F1`）。新定义 `endsAsc`、`NA`、`NAser`、`hyp1F1`（Kummer 级数 Σ (a)_n/(b)_n zⁿ/n! tⁿ）由 AI 对照论文核对。
根模块加 import，Axioms 加三条（共 273 条）；全量扫描的声明数从 logs/lean_axioms_2026-10-10_endasc.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 在定理 5.4 一行之前加注记 5.2 一行；
  「Not formalized」里「Remarks 3.5 and 5.2」改为「Remark 3.5」。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_endasc.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_endasc.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
FRESH = '40'

ROW54 = r'Theorem~\ref{thm:ideal} & \lean{RelU\_eq}'
PAPER = [
    (ROW54, r'Remark~\ref{rem:1F1} & \lean{P\_mul\_NAser}, \lean{remark\_1F1}\\' '\n' + ROW54),
    (r'Remarks~\ref{rem:oeis} and~\ref{rem:1F1};', r'Remark~\ref{rem:oeis};'),
]
PAPER_RE = [
    (r'consists of 31 files that start from', 'consists of 32 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`ThreeTerm.lean`、`GenFunXY.lean` 与 `Blocks.lean`）', '`ThreeTerm.lean`、`GenFunXY.lean`、`Blocks.lean` 与 `EndAscent.lean`）'),
    ('共 31 个模块（', '共 32 个模块（'),
    ('（补丁 `patch_paper_2026-10-10_lean_blocks.py`）。',
     '（补丁 `patch_paper_2026-10-10_lean_blocks.py`）。第七项：注记 5.2，新模块 `EndAscent.lean`：`P_mul_NAser`'
     '（P_m·Σ_k NA_k(m) x^k = 1，NA_k(m) 是 H_k(m) 中不以上升结尾的序列个数，证明照引理 1 的分类，截断块 [a, m] 以上升结尾）、'
     '`remark_1F1`（ℚ(x)[[t]] 中 Σ_m t^m/P_m = (1/(1 − x))·₁F₁(1; 1 − λ; −t/x³)，λ = (1 − x)/x³；一般形式 '
     '`sum_inv_P_eq_hyp1F1`，₁F₁ 用升阶乘 `ascPochhammer` 定义）。第一次编译四处报错（单元素集合上的 filter 要 '
     '`Finset.filter_singleton`；升阶乘那步 field_simp 消不掉 (x³)⁻¹ 的幂，改为 `linear_combination` 带 x³·(x³)⁻¹ = 1；'
     '`RatFunc.algebraMap_injective` 要显式给 ℚ），改后通过。Axioms 273 条，全量扫描 %s 个声明，只有三条标准公理；'
     '`check_lean_fresh.py` %s PASS（补丁 `patch_paper_2026-10-10_lean_endasc.py`）。' % (DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2\(1\) 的最后两句、推论 5\.5、推论 5\.7、定理 4\.2、定理 4\.4 与'
     r'引理 4\.5 的按 y 细化后由 2675 增加；',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、推论 5.5、推论 5.7、定理 4.2、定理 4.4、'
     '引理 4.5 的按 y 细化与注记 5.2 后由 2675 增加；' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_blocks.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_blocks.log`）。同日第七项：新模块 `EndAscent.lean`（论文注记 5.2；新定义 '
     '`endsAsc`（最后两项 x < y）、`NA`、`NAser`、`hyp1F1`（Σ (a)_n/(b)_n·zⁿ/n!·tⁿ）由 AI 对照论文核对），经 '
     '`lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（273 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，'
     '`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_endasc.log`）。' % (DECLS, FRESH)),
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
    patch(os.path.join(ROOT, 'README.md'), README, README_RE)
    patch(os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST)


if __name__ == '__main__':
    main()
