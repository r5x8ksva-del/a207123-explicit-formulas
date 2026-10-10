# -*- coding: utf-8 -*-
r"""Lean 续作第三十四项（2026-10-10）：报告 T5.3(4) 的 Möbius 解释（Philip Hall 定理），新模块
`lean/A207123/Mobius.lean`：
- `mu_eq_sum_chains`：有限偏序集中 a < b 时 μ(a,b) = Σ_n (−1)^{n+1}·#{a < x_1 < ⋯ < x_n < b}（μ 取 Mathlib 的
  `IncidenceAlgebra.mu`；对 b 良基归纳，链按最大元分类 `chainsIn_succ`）。
- `chainsIn_lam`：Λ_k 中 0̂、1̂ 之间的 n 元链就是 Λ̄_k 的 n 元链（`numChainsBar`）；`mobius_lam`：μ_{Λ_k}(0̂,1̂) =
  Σ_q (−1)^q N(k,q)（k ≥ 1），`mobius_lam_eq_upoly`、`mobius_lam_eq_zero`（k ≥ 4 时为 0）、`mobius_lam_small`。
根模块加 import，Axioms 加 10 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_mobius.log 读。
论文没有陈述 T5.3(4)，只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A14 升为 ■■■■■，Lean 一句改为已形式化。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_mobius.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_mobius.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '68'

PAPER_RE = [
    (r'consists of 59 files that start from', 'consists of 60 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`ShapeRemarks.lean` 与 `MCoeff.lean`）', '`ShapeRemarks.lean`、`MCoeff.lean` 与 `Mobius.lean`）'),
    ('共 59 个模块（', '共 60 个模块（'),
    ('第 7 节的 p_2、p_3 与表 4 后由 2675 增加',
     '第 7 节的 p_2、p_3 与表 4，以及报告 T5.3(4) 的 Möbius 解释（Philip Hall 定理；论文没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_mcoeff.py`。',
     '补丁 `patch_paper_2026-10-10_lean_mcoeff.py`。第三十四项：报告 T5.3(4) 的 Möbius 解释，新模块 `Mobius.lean`'
     '（`mu_eq_sum_chains`：Philip Hall 定理，有限偏序集中 a < b 时 μ(a,b) = Σ_n (−1)^{n+1}·#{a < x_1 < ⋯ < x_n < b}，'
     'μ 取 Mathlib 的 `IncidenceAlgebra.mu`，对 b 良基归纳、链按最大元分类（`chainsIn_succ`）；`chainsIn_lam`：Λ_k 中 '
     '0̂、1̂ 之间的链就是 Λ̄_k 的链；`mobius_lam`：k ≥ 1 时 μ_{Λ_k}(0̂,1̂) = Σ_q (−1)^q N(k,q)，`mobius_lam_eq_upoly`'
     '（= u_k(−2)）、`mobius_lam_eq_zero`（k ≥ 4 时为 0）、`mobius_lam_small`（k = 1, 2, 3 时为 −1, 1, 1）；Λ_k 的局部'
     '有限序取 `Fintype.toLocallyFiniteOrder`，局部有限序结构唯一，μ 与这个选择无关）。一次编译通过（21 s、峰值 8.0 GB）。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_mobius.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_mcoeff.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_mcoeff.log`）。同日第三十四项：新模块 `Mobius.lean`（报告 T5.3(4) 的 Möbius '
     '解释）。新的承重定义一个：`chainsIn a b n` = 满足 `StrictMono c` 且每个 `c i` 严格介于 a、b 之间的 '
     '`c : Fin n → α` 的个数，即 a < x_1 < ⋯ < x_n < b 的 n 元链数（n = 0 时为 1，`chainsIn_zero`），已人工核对；'
     'μ 是 Mathlib 的 `IncidenceAlgebra.mu`（μ(a,a) = 1、μ(a,b) = −Σ_{a≤x<b} μ(a,x)），0̂、1̂ 是已核对的 `lamBot`、'
     '`lamTop`（全 0 行、全 1 行，`lamBot_le`、`le_lamTop`）；实例 `lamLocallyFiniteOrder` 取 '
     '`Fintype.toLocallyFiniteOrder`，Mathlib 有 `Subsingleton (LocallyFiniteOrder α)`，所以陈述与实例的选择无关。'
     '经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 '
     '`Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_mobius.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('| ■■■■■（Möbius 解释除外） |', '| ■■■■■ |'),
    ('(4) 中「μ(0̂,1̂)=Σ_q(−1)^qN(k,q)」引用 Philip Hall 定理（未重证、未形式化） |',
     '(4) 中「μ(0̂,1̂)=Σ_q(−1)^qN(k,q)」（Philip Hall 定理）2026-10-10 已形式化（`Mobius.lean`：`mu_eq_sum_chains`'
     '（有限偏序集中 a<b 时 μ(a,b)=Σ_n(−1)^{n+1}·#{a<x_1<⋯<x_n<b}，μ 取 Mathlib 的 IncidenceAlgebra.mu）、'
     '`chainsIn_lam`、`mobius_lam`（k≥1）、`mobius_lam_eq_upoly`、`mobius_lam_eq_zero`（k≥4 时为 0）、'
     '`mobius_lam_small`（k=1,2,3 时为 −1,1,1）） |'),
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
