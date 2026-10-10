# -*- coding: utf-8 -*-
r"""Lean 续作第八项（2026-10-10）：论文定理 3.2(2)（U_k(m) 按 (y − 1)∏_{i=1}^{m}(y³ − y² − i) 的根展开）形式化，
新模块 `lean/A207123/RootExpansion.lean`：`thm_asym_two`（`sig m` 有 3m + 1 个元素、系数 α_m(σ) 都不为 0、对一切
k ≥ 0 有 U_k(m) = Σ_σ α_m(σ)·σ^k）、`alpha_unique`（系数由 U 唯一确定）、`alpha_eq`（σ ≠ 0、σ³ − σ² = j ≤ m 时
α_m(σ) = α_j(σ)·(−σ³)^{m−j}/(m − j)!）。新定义 `Qpoly`、`sig`、`cof`、`alpha`、`geom` 由 AI 对照论文核对。
根模块加 import，Axioms 加三条（共 276 条）；全量扫描的声明数从 logs/lean_axioms_2026-10-10_rootexp.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 在定理 3.2(1) 一行之后加定理 3.2(2) 一行；
  「Not formalized」里「Theorem 3.2(2)(3)」改为「Theorem 3.2(3)」。
- paper/reviewer_guide.tex：第 2 节加上定理 3.2(2)；第 3 节第 5 条只剩定理 3.2(3) 与注记 3.3。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_rootexp.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_rootexp.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
FRESH = '41'

ROW321_END = r'\lean{norm\_lt\_rho\_of\_root}, \lean{root\_P\_min}\\' '\n'
PAPER = [
    (ROW321_END, ROW321_END + r'Theorem~\ref{thm:asym}(2) & \lean{thm\_asym\_two}, \lean{alpha\_unique}, '
     r'\lean{alpha\_eq}\\' '\n'),
    (r'Theorem~\ref{thm:asym}(2)(3) and Remark~\ref{rem:asym};', r'Theorem~\ref{thm:asym}(3) and Remark~\ref{rem:asym};'),
]
PAPER_RE = [
    (r'consists of 32 files that start from', 'consists of 33 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('the roots in Theorem 3.2(1), Corollary 3.4',
     'the roots in Theorem 3.2(1) and the expansion over them in Theorem 3.2(2), Corollary 3.4'),
    ('parts (2) and (3) of Theorem 3.2 (asymptotics) and Remark 3.3.',
     'part (3) of Theorem 3.2 (asymptotics) and Remark 3.3.'),
]

README = [
    ('`Blocks.lean` 与 `EndAscent.lean`）', '`Blocks.lean`、`EndAscent.lean` 与 `RootExpansion.lean`）'),
    ('共 32 个模块（', '共 33 个模块（'),
    ('（补丁 `patch_paper_2026-10-10_lean_endasc.py`）。',
     '（补丁 `patch_paper_2026-10-10_lean_endasc.py`）。第八项：定理 3.2(2)，新模块 `RootExpansion.lean`：`Qpoly`'
     '（(X − 1)∏_{i=1}^{m}(X³ − X² − i)）、`sig`（它的根的集合）、`alpha`（α_m(σ) = W_m(1/σ)/∏_{τ≠σ}(1 − τ/σ)，即 G_m = W_m/P_m '
     '的部分分式系数）；`thm_asym_two`（`sig m` 有 3m + 1 个元素、α_m(σ) ≠ 0、对一切 k ≥ 0 有 U_k(m) = Σ_σ α_m(σ)σ^k）、'
     '`alpha_unique`（系数唯一）、`alpha_eq`（σ ≠ 0、σ³ − σ² = j ≤ m 时 α_m(σ) = α_j(σ)(−σ³)^{m−j}/(m − j)!）。证明：'
     'P_m = ∏_σ(1 − σx)（两边次数 ≤ 3m + 1，在 0 与 P_m 的 3m + 1 个根处相等）；W_m 与 Σ_σ α_m(σ)∏_{τ≠σ}(1 − τx) 次数 ≤ 3m，'
     '在 3m + 1 个点 1/σ 处相等；两边除以 P_m 比较系数；α ≠ 0 由 W_m、P_m 互素；第二句用 W_{m+1}(1/σ) = W_m(1/σ) 与余因子多乘 '
     'b_{m+1}(1/σ) = (j − m − 1)/σ³。编译一次通过、无警告。Axioms 276 条，全量扫描 %s 个声明，只有三条标准公理；'
     '`check_lean_fresh.py` %s PASS（补丁 `patch_paper_2026-10-10_lean_rootexp.py`）。' % (DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、推论 5\.5、推论 5\.7、定理 4\.2、定理 4\.4、'
     r'引理 4\.5 的按 y 细化与注记 5\.2 后由 2675 增加；',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、定理 3.2(2)、推论 5.5、推论 5.7、定理 4.2、'
     '定理 4.4、引理 4.5 的按 y 细化与注记 5.2 后由 2675 增加；' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_endasc.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_endasc.log`）。同日第八项：新模块 `RootExpansion.lean`（论文定理 3.2(2)；新定义 '
     '`Qpoly`、`sig`、`cof`、`alpha`、`geom` 由 AI 对照论文核对：`sig m` 是 `Qpoly m` 的根的集合（`Multiset.toFinset`，'
     '`card_sig` 证明恰有 3m + 1 个，即根两两不同），`alpha` 是部分分式系数，`alpha_unique` 说明它就是论文里由展开式确定的 '
     'α_m(σ)），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（276 条，%s 个声明，只有三条标准公理）与 '
     '`Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_rootexp.log`）。'
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
