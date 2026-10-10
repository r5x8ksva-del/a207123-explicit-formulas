# -*- coding: utf-8 -*-
r"""Lean 续作第十项（2026-10-10）：论文注记 3.3 的精确部分形式化，新模块 `lean/A207123/AsympRemark.lean`：
`tendsto_ratio`（(U_k(m)/(c_m ρ_m^k) − 1)/θ_m^k → −κ_m）、`kappaConst_pos`（κ_m > 0）、`rate_not_improvable`
（0 ≤ θ' < θ_m 时不是 O(θ'^k)）、`cm_one`（c_1 = (10 + 15ρ_1 + 17ρ_1²)/31）、`rho_int_iff`（ρ_m 是整数 ⟺ m = y²(y − 1)）、
`cm_rat_of_rho_int`（此时 c_m 有理）、`cm_four`（c_4 = 215/2，另有 `rho_four`）、`U_four_asymp`（U_k(4) = (215/2)2^k
− c_3 ρ_3^{k+3} + O(ρ_2^k)）、`tendsto_one_sub_theta`（m(1 − θ_m) → 1/3）。注记里的数值是数值观察，不形式化。
新定义 `thetaRatio`（θ_m）、`kappaConst`（κ_m）由 AI 对照论文核对。
根模块加 import，Axioms 加九条（共 288 条）；全量扫描的声明数从 logs/lean_axioms_2026-10-10_asympremark.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 在定理 3.2(3) 一行之后加注记 3.3 一行；
  「Not formalized」里「Remark 3.3」改为「the numerical values in Remark 3.3」。
- paper/reviewer_guide.tex：第 2 节加上注记 3.3 的精确陈述；第 3 节第 5 条改为注记 3.3 的数值。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_asympremark.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_asympremark.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
FRESH = '43'

ROW323 = (r'Theorem~\ref{thm:asym}(3) & \lean{thm\_asym\_three}, \lean{cm\_zero}, \lean{U\_asymp\_bound}\\' '\n')
PAPER = [
    (ROW323, ROW323 + r'Remark~\ref{rem:asym}, except the numerical values & \lean{tendsto\_ratio}, '
     r'\lean{rate\_not\_improvable}, \lean{cm\_one}, \lean{rho\_int\_iff}, \lean{cm\_four}, \lean{U\_four\_asymp}, '
     r'\lean{tendsto\_one\_sub\_theta}\\' '\n'),
    (r'Remark~\ref{rem:asym}; Remark~\ref{rem:oeis};',
     r'the numerical values in Remark~\ref{rem:asym}; Remark~\ref{rem:oeis};'),
]
PAPER_RE = [
    (r'consists of 34 files that start from', 'consists of 35 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('Theorem 3.2 (the roots, the expansion over them and the asymptotics), Corollary 3.4',
     'Theorem 3.2 (the roots, the expansion over them and the asymptotics) with the exact statements of Remark 3.3, '
     'Corollary 3.4'),
    (r'\item \textbf{Section 3:} Remark 3.3.', r'\item \textbf{Section 3:} the numerical values in Remark 3.3.'),
]

README = [
    ('`RootExpansion.lean` 与 `RootAsymp.lean`）', '`RootExpansion.lean`、`RootAsymp.lean` 与 `AsympRemark.lean`）'),
    ('共 34 个模块（', '共 35 个模块（'),
    ('（补丁 `patch_paper_2026-10-10_lean_rootasymp.py`）。',
     '（补丁 `patch_paper_2026-10-10_lean_rootasymp.py`）。第十项：注记 3.3 的精确部分，新模块 `AsympRemark.lean`：'
     '`thetaRatio`（θ_m = ρ_{m−1}/ρ_m）、`kappaConst`（κ_m = c_{m−1}ρ_{m−1}³/c_m；`theta` 已是 NonDFinite.lean 的算子名）；'
     '`tendsto_ratio`（(U_k(m)/(c_m ρ_m^k) − 1)/θ_m^k → −κ_m）、`kappaConst_pos`、`rate_not_improvable`（0 ≤ θ\' < θ_m 时'
     '不是 O(θ\'^k)）、`cm_one`（c_1 = (10 + 15ρ_1 + 17ρ_1²)/31）、`rho_int_iff`（ρ_m 是整数 ⟺ m = y²(y − 1)）、'
     '`cm_rat_of_rho_int`、`rho_four`、`cm_four`（c_4 = 215/2）、`U_four_asymp`（U_k(4) = (215/2)2^k − c_3 ρ_3^{k+3} + '
     'O(ρ_2^k)，用 τ_4 = ρ_2）、`tendsto_one_sub_theta`（m(1 − θ_m) → 1/3，用 (ρ_m − ρ_{m−1})(ρ_m² + ρ_mρ_{m−1} + ρ_{m−1}² − '
     'ρ_m − ρ_{m−1}) = 1 与 ρ_m → ∞）。数值（ρ_1 ≈ 1.46557 等、κ_m 在 m ≤ 24 内递增、相对误差）是数值观察，不形式化。'
     '两个较长的 linear_combination 恒等式先用 `code/main_extra/check_lincomb_rem33.py` 在随机有理点上核对。第一次编译'
     '无错误，只有 linter 提示（备用分支没用上、push_neg 已弃用），改掉后无警告。Axioms 288 条，全量扫描 %s 个声明，只有'
     '三条标准公理；`check_lean_fresh.py` %s PASS（补丁 `patch_paper_2026-10-10_lean_asympremark.py`）。' % (DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、定理 3\.2\(2\)\(3\)、推论 5\.5、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、定理 3.2(2)(3)、注记 3.3 的精确部分、推论 5.5、'
     % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_rootasymp.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_rootasymp.log`）。同日第十项：新模块 `AsympRemark.lean`（论文注记 3.3 的精确部分；'
     '新定义 `thetaRatio`、`kappaConst` 与论文的 θ_m、κ_m 逐字对应，由 AI 核对），经 `lean/lean_one.sh` 编译、重编根模块、'
     '重跑 `Axioms.lean`（288 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_asympremark.log`）。' % (DECLS, FRESH)),
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
