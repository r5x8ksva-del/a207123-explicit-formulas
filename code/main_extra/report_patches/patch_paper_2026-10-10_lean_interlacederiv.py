# -*- coding: utf-8 -*-
r"""Lean 续作第二十三项（2026-10-10）：论文引理 8.7(3)（`g ≪ f`、`deg g ≥ 1` 推出 `g' ≪ f'`），
新模块 `lean/A207123/InterlaceDeriv.lean`：
- `interlaces_derivative_of_interlaces`（不要求首项系数为正）、`interlaces_derivative_of_interlaces_pos`；
  论文用 Pick 判据（引理 8.5(1)）与 Gauss–Lucas 定理，这里用下锥：`g = c·f + Σ_a w_a·f/(z−a)` 求导后，
  每个 `(f/(z−a))'` 都与 `f'` 交错（`inCone_derivative_of_eq_mul`，由引理 8.7(1) 与引理 8.6），下锥对非负组合封闭。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_interlacederiv.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；表 6 第一行改为整条引理 8.7 并加 `interlaces_derivative_of_interlaces`；
  「Not formalized」只剩引理 8.5（括号说明改为：论文用到它的地方，形式化证明改用锥的表示）。
- paper/reviewer_guide.tex：第 2 节引理列表改为 8.4、8.6--8.9，并删去上一项留下的重复半句「and part of Lemma 8.12」；
  第 3 节 Section 8 一条。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A19 的形式化一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_interlacederiv.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_interlacederiv.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '57'

PAPER = [
    (r'Lemmas~\ref{lem:il-factor}, \ref{lem:il-sum}, \ref{lem:il-ops}(1)(2) & \lean{interlaces\_mul\_iff}, '
     r'\lean{Interlaces.add\_left}, \lean{Interlaces.add\_right}, \lean{interlaces\_X\_sub\_C\_mul}, '
     r'\lean{interlaces\_derivative}, \lean{Interlaces.X\_mul}\\' + '\n',
     r'Lemmas~\ref{lem:il-factor}, \ref{lem:il-sum}, \ref{lem:il-ops} & \lean{interlaces\_mul\_iff}, '
     r'\lean{Interlaces.add\_left}, \lean{Interlaces.add\_right}, \lean{interlaces\_X\_sub\_C\_mul}, '
     r'\lean{interlaces\_derivative}, \lean{Interlaces.X\_mul}, \lean{interlaces\_derivative\_of\_interlaces}\\' + '\n'),
    (r'and in Section~\ref{sec:realroots} Lemmas~\ref{lem:il-pick} and~\ref{lem:il-ops}(3) (the formal proof of '
     r'Lemma~\ref{lem:il-T}(2) writes $g\ll f$ as $g=cf+\sum_aw_a\,f/(z-a)$ with $c,w_a\ge0$ instead), ',
     r'and in Section~\ref{sec:realroots} Lemma~\ref{lem:il-pick} (where it is used, the formal proofs write '
     r'$g\ll f$ as $g=cf+\sum_aw_a\,f/(z-a)$ with $c,w_a\ge0$ instead), '),
]
PAPER_RE = [
    (r'consists of 48 files that start from', 'consists of 49 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('Lemmas 8.4, 8.6, 8.8, 8.9, Propositions 8.10 and 8.11', 'Lemmas 8.4 and 8.6--8.9, Propositions 8.10 and 8.11'),
    # 第二十二项把「Lemma 8.12 and Corollary 8.13」插在这半句前面时没有删掉它
    ('Corollary 8.15 and part of Lemma 8.12. The axiom check', 'and Corollary 8.15. The axiom check'),
    ('by a route that replaces Lemmas 8.5 and 8.7(3) (upper half-plane, Gauss--Lucas) with $g=cf+\\sum_aw_af/(z-a)$. '
     'Not formalized: Lemmas 8.5 and 8.7(3) themselves and Corollary 8.14',
     'by a route that replaces Lemma 8.5 (upper half-plane) with $g=cf+\\sum_aw_af/(z-a)$; Lemma 8.7(3) is formalized '
     'by the same route, without Gauss--Lucas. Not formalized: Lemma 8.5 itself and Corollary 8.14'),
]

README = [
    ('`LogConcave.lean` 与 `RootLocation.lean`）', '`LogConcave.lean`、`RootLocation.lean` 与 `InterlaceDeriv.lean`）'),
    ('共 48 个模块（', '共 49 个模块（'),
    ('引理 8.12（λ_k 的符号）与推论 8.13（h_k 的根的位置、系数的变号次数）后由 2675 增加',
     '引理 8.12（λ_k 的符号）、推论 8.13（h_k 的根的位置、系数的变号次数）与引理 8.7(3)（求导保持交错）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_rootlocation.py`。',
     '补丁 `patch_paper_2026-10-10_lean_rootlocation.py`。第二十三项：论文引理 8.7(3)（g ≪ f、deg g ≥ 1 推出 '
     'g′ ≪ f′），新模块 `InterlaceDeriv.lean`（`interlaces_derivative_of_interlaces`，不要求首项系数为正；论文用 Pick '
     '判据与 Gauss–Lucas 定理，这里用下锥：g = c·f + Σ_a w_a·f/(z−a) 求导后，每个 (f/(z−a))′ 都与 f′ 交错'
     '（`inCone_derivative_of_eq_mul`，由引理 8.7(1) 与引理 8.6），下锥对非负组合封闭）。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_interlacederiv.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_rootlocation.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_rootlocation.log`）。同日第二十三项：新模块 `InterlaceDeriv.lean`（论文引理 '
     '8.7(3)；没有新定义，主陈述 `interlaces_derivative_of_interlaces` 只用到已有的 `Interlaces` 与 Mathlib 的 '
     '`derivative`），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）'
     '与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_interlacederiv.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；中心极限定理未形式化',
     '；第二十三项把论文引理 8.7(3)（求导保持交错）本身也形式化了（`InterlaceDeriv.lean`，同样用锥的表示，'
     '不用 Gauss–Lucas）；中心极限定理未形式化'),
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
    patch(os.path.join(ROOT, '猜想总表.md'), TABLE)


if __name__ == '__main__':
    main()
