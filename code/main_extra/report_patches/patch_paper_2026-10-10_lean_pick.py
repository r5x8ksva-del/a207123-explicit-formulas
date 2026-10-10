# -*- coding: utf-8 -*-
r"""Lean 续作第二十四项（2026-10-10）：论文引理 8.5（Pick 判据：交错关系与上半平面上虚部的符号），
新模块 `lean/A207123/Pick.lean`：
- `lemma_il_pick_one`（`deg g ≤ deg f` 时 `g ≪ f` ⟺ 上半平面上 `Im(g/f) ≤ 0`）、`lemma_il_pick_two`
  （`deg f ≤ deg g ≤ deg f + 1` 时 `f ≪ g` ⟺ `Im(g/f) ≥ 0`）、`realRooted_of_im_nonpos`、`realRooted_of_im_nonneg`
  （上半平面的条件推出 `g` 实根）。「⇒」由锥的表示直接算虚部；「⇐」按论文在 `f` 的根附近做局部分析
  （`exists_im_pos_of_local`、`exists_omega_of_two_le`、`isRoot_of_im_nonpos`、`weight_nonneg_of_im_nonpos`），
  对 `deg f` 归纳、逐个除去公共根，单根时插值（`cone_of_im_nonpos`、`ucone_of_im_nonneg`）。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_pick.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；表 6 第一行改为引理 8.4–8.7 并加 `lemma_il_pick_one`、`lemma_il_pick_two`；
  「Not formalized」删去引理 8.5，改为另起一句说明它已形式化、而第 8 节其余的形式化证明用锥的表示代替它。
- paper/reviewer_guide.tex：第 2 节引理列表改为 8.4--8.9；第 3 节 Section 8 一条。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A19 的形式化一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_pick.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_pick.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '58'

PAPER = [
    (r'Lemmas~\ref{lem:il-factor}, \ref{lem:il-sum}, \ref{lem:il-ops} & \lean{interlaces\_mul\_iff}, '
     r'\lean{Interlaces.add\_left}, ',
     r'Lemmas~\ref{lem:il-factor}--\ref{lem:il-ops} & \lean{interlaces\_mul\_iff}, \lean{lemma\_il\_pick\_one}, '
     r'\lean{lemma\_il\_pick\_two}, \lean{Interlaces.add\_left}, '),
    (r'and in Section~\ref{sec:realroots} Lemma~\ref{lem:il-pick} (where it is used, the formal proofs write '
     r'$g\ll f$ as $g=cf+\sum_aw_a\,f/(z-a)$ with $c,w_a\ge0$ instead), Corollary~\ref{cor:clt}, and '
     r'Remark~\ref{rem:chains}.',
     r'and in Section~\ref{sec:realroots} Corollary~\ref{cor:clt} and Remark~\ref{rem:chains}. '
     r'Lemma~\ref{lem:il-pick} is formalized, but the other formal proofs in Section~\ref{sec:realroots} write '
     r'$g\ll f$ as $g=cf+\sum_aw_a\,f/(z-a)$ with $c,w_a\ge0$ instead of using it.'),
]
PAPER_RE = [
    (r'consists of 49 files that start from', 'consists of 50 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('Lemmas 8.4 and 8.6--8.9, Propositions 8.10 and 8.11', 'Lemmas 8.4--8.9, Propositions 8.10 and 8.11'),
    ('$g=cf+\\sum_aw_af/(z-a)$; Lemma 8.7(3) is formalized by the same route, without Gauss--Lucas. '
     'Not formalized: Lemma 8.5 itself and Corollary 8.14',
     '$g=cf+\\sum_aw_af/(z-a)$; Lemma 8.5 itself and Lemma 8.7(3) (without Gauss--Lucas) are formalized too. '
     'Not formalized: Corollary 8.14'),
]

README = [
    ('`RootLocation.lean` 与 `InterlaceDeriv.lean`）', '`RootLocation.lean`、`InterlaceDeriv.lean` 与 `Pick.lean`）'),
    ('共 49 个模块（', '共 50 个模块（'),
    ('与引理 8.7(3)（求导保持交错）后由 2675 增加', '、引理 8.7(3)（求导保持交错）与引理 8.5（Pick 判据）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_interlacederiv.py`。',
     '补丁 `patch_paper_2026-10-10_lean_interlacederiv.py`。第二十四项：论文引理 8.5（Pick 判据），新模块 `Pick.lean`'
     '（`lemma_il_pick_one`：deg g ≤ deg f 时 g ≪ f 当且仅当上半平面上 Im(g/f) ≤ 0；`lemma_il_pick_two`：'
     'deg f ≤ deg g ≤ deg f + 1 时 f ≪ g 当且仅当 Im(g/f) ≥ 0；`realRooted_of_im_nonpos`、`realRooted_of_im_nonneg`：'
     '上半平面的条件推出 g 实根。「⇒」由锥的表示直接算虚部；「⇐」按论文在 f 的根附近做局部分析：f = (z−a)^L·q 时在 '
     'z = a + εω 处 g/f = ε^{−L}ω^{−L}·(g/q)(z)，L ≥ 2 取 ω = e^{iπ/(2L)} 或 e^{3iπ/(2L)} 得重根处 g(a) = 0，L = 1 取 '
     'ω = i 得权重非负；对 deg f 归纳、逐个除去公共根（论文先除以最大公因式），单根时插值）。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_pick.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_interlacederiv.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_interlacederiv.log`）。同日第二十四项：新模块 `Pick.lean`（论文引理 8.5；'
     '没有新定义，主陈述 `lemma_il_pick_one`、`lemma_il_pick_two` 用到已有的 `Interlaces`、`RealRooted` 与 Mathlib 的 '
     '`aeval`（实系数多项式在复数点的值）、`Complex.im`；上半平面写成 `0 < z.im`），经 `lean/lean_one.sh` 编译、'
     '重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` '
     '%s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_pick.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；中心极限定理未形式化',
     '；第二十四项形式化了论文引理 8.5（Pick 判据）本身（`Pick.lean` 的 `lemma_il_pick_one`、`lemma_il_pick_two`：'
     '「⇒」由锥的表示直接算虚部，「⇐」按论文在 f 的根附近做局部分析）；中心极限定理未形式化'),
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
