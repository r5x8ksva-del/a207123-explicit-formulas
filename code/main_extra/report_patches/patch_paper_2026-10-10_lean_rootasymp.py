# -*- coding: utf-8 -*-
r"""Lean 续作第九项（2026-10-10）：论文定理 3.2(3)（c_m 的两个表达式、c_m > 0、U_k(m) 的渐近式）形式化，
新模块 `lean/A207123/RootAsymp.lean`：`thm_asym_three`（m ≥ 1 时 c_m = α_m(ρ_m) > 0；G_{m−1}(x_m) = Σ_k U_k(m−1)x_m^k
收敛（HasSum）且 c_m = (G_{m−1}(x_m) + m x_m²)/(x_m(1 + 3m x_m²))；τ_m < ρ_{m−1}；U_k(m) = c_m ρ_m^k − c_{m−1} ρ_{m−1}^{k+3}
+ O(τ_m^k)）、`cm_zero`（c_0 = 1）、`U_asymp_bound`（对一切 k ≥ 0 的显式误差界）。`cm` 用论文的第二个表达式定义
（m^{\underline j} 是 `Nat.descFactorial`），`tau` 照论文定义；由 AI 对照论文核对。
根模块加 import，Axioms 加三条（共 279 条）；全量扫描的声明数从 logs/lean_axioms_2026-10-10_rootasymp.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 在定理 3.2(2) 一行之后加定理 3.2(3) 一行；
  「Not formalized」里「Theorem 3.2(3) and Remark 3.3」改为「Remark 3.3」。
- paper/reviewer_guide.tex：第 2 节改为整个定理 3.2；第 3 节第 5 条只剩注记 3.3。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_rootasymp.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_rootasymp.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
FRESH = '42'

ROW322 = r'Theorem~\ref{thm:asym}(2) & \lean{thm\_asym\_two}, \lean{alpha\_unique}, \lean{alpha\_eq}\\' '\n'
PAPER = [
    (ROW322, ROW322 + r'Theorem~\ref{thm:asym}(3) & \lean{thm\_asym\_three}, \lean{cm\_zero}, '
     r'\lean{U\_asymp\_bound}\\' '\n'),
    (r'Theorem~\ref{thm:asym}(3) and Remark~\ref{rem:asym};', r'Remark~\ref{rem:asym};'),
]
PAPER_RE = [
    (r'consists of 33 files that start from', 'consists of 34 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('the roots in Theorem 3.2(1) and the expansion over them in Theorem 3.2(2), Corollary 3.4',
     'Theorem 3.2 (the roots, the expansion over them and the asymptotics), Corollary 3.4'),
    ('part (3) of Theorem 3.2 (asymptotics) and Remark 3.3.', 'Remark 3.3.'),
]

README = [
    ('`EndAscent.lean` 与 `RootExpansion.lean`）', '`EndAscent.lean`、`RootExpansion.lean` 与 `RootAsymp.lean`）'),
    ('共 33 个模块（', '共 34 个模块（'),
    ('（补丁 `patch_paper_2026-10-10_lean_rootexp.py`）。',
     '（补丁 `patch_paper_2026-10-10_lean_rootexp.py`）。第九项：定理 3.2(3)，新模块 `RootAsymp.lean`：`cm`（论文的第二个'
     '表达式 ρ_m^{3m+3}/(m!(ρ_m² + 3m))·(1 + Σ_j j·m^{\\underline j}·ρ_m^{−3j−2})，m^{\\underline j} 用 `Nat.descFactorial`）、'
     '`tau`（τ_1 = √(ρ_1(ρ_1 − 1))，m ≥ 2 时 max(ρ_{m−2}, √(ρ_m(ρ_m − 1)))）；`thm_asym_three`（m ≥ 1 时 c_m = α_m(ρ_m) > 0；'
     'G_{m−1}(x_m) 作为级数 Σ_k U_k(m−1)x_m^k 的和（`HasSum`）收敛到 W_{m−1}(x_m)/P_{m−1}(x_m)，且 c_m = (G_{m−1}(x_m) + '
     'm x_m²)/(x_m(1 + 3m x_m²))；τ_m < ρ_{m−1}；U_k(m) = c_m ρ_m^k − c_{m−1} ρ_{m−1}^{k+3} + O(τ_m^k)）、`cm_zero`（c_0 = 1）、'
     '`U_asymp_bound`（对一切 k ≥ 0 的显式误差界 Σ‖α_m(σ)‖·τ_m^k）。证明照论文：1 − x_m = m x_m³ 给出 b_v(x_m) = (m − v)x_m³ '
     '与 P_{j−1}(x_m) = m^{\\underline j} x_m^{3j}；b_m = (1 − ρ_m x)(1 + (ρ_m − 1)x + ρ_m(ρ_m − 1)x²)；由定理 3.2(2) 分出 '
     'ρ_m、ρ_{m−1} 两项，α_m(ρ_{m−1}) = −c_{m−1}ρ_{m−1}³，其余根的模 ≤ τ_m（定理 3.2(1)）。第一次编译只有一处多余的 `ring`'
     '（rw 已经按定义相等关掉了目标），删掉后通过、无警告。Axioms 279 条，全量扫描 %s 个声明，只有三条标准公理；'
     '`check_lean_fresh.py` %s PASS（补丁 `patch_paper_2026-10-10_lean_rootasymp.py`）。' % (DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、定理 3\.2\(2\)、推论 5\.5、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、定理 3.2(2)(3)、推论 5.5、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_rootexp.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_rootexp.log`）。同日第九项：新模块 `RootAsymp.lean`（论文定理 3.2(3)；新定义 '
     '`cm`、`tau` 由 AI 对照论文核对：`cm` 是论文 c_m 的第二个表达式，`alpha_rho` 证明它等于 α_m(ρ_m)，`cm_eq_G` 与 '
     '`hasSum_G` 给出第一个表达式；`tau` 与论文的 τ_m 逐字对应），经 `lean/lean_one.sh` 编译、重编根模块、重跑 '
     '`Axioms.lean`（279 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_rootasymp.log`）。' % (DECLS, FRESH)),
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
