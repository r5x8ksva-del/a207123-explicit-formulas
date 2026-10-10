# -*- coding: utf-8 -*-
r"""Lean 续作第二十项（2026-10-10）：论文第 8 节命题 8.11（n_k 除 −1 外只有单根）与定理 8.1 的其余部分（h_k 的根
都是实数且互不相同），新模块 `lean/A207123/SimpleRoots.lean`：
- 交错的推论（论文定义 ≪ 之后的说明）`Interlaces.eval_mul_derivative_nonneg`；实根多项式的导数在非根处至多单根
  `count_roots_of_derivative`；
- 命题 8.11：`nR_no_common_root`（论文对最小的 j 反证，写成强归纳）、`count_roots_nR_le_one`；
- 定理 8.1：`rootMultiplicity_nrowPoly_le_one`（ℂ 中除 −1 外的根重数 ≤ 1）、`hpoly_root_im_eq_zero`、
  `separable_hpoly`（h_k 可分，即根都是单根）、`thm_realroots`（合在一起）。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_simpleroots.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 中命题 8.10 一行扩成命题 8.10、8.11 与
  定理 8.1；「Not formalized」里删去命题 8.11 与定理 8.1 的那半句。这一行先列了 13 个名字（含 n_k、h_k 各自的
  分项），表 5 变成整页浮动体、第 29 页出 underfull \vbox；在草稿目录试了四个版本（行距 0.88、只列 8 个名字、
  只列 4 个名字、8 个名字加行距 0.88），取只列 8 个名字、行距不变：仍 38 页、无警告，第 30 页排表 5 与第 10 节 (3)。
- paper/reviewer_guide.tex：第 2 节与第 3 节 Section 8 一条。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A19 的完成度与「未形式化」一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_simpleroots.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_simpleroots.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '54'

PAPER = [
    (r'Proposition~\ref{prop:four}, Theorem~\ref{thm:realroots} & \lean{prop\_four\_relations}, \lean{alpha\_two}, '
     r'\lean{beta\_two}; zeros of $n_k$ real: \lean{realRooted\_nR}, \lean{nrowPoly\_root\_im\_eq\_zero}\\',
     r'Propositions~\ref{prop:four}, \ref{prop:simple}, Theorem~\ref{thm:realroots} & \lean{prop\_four\_relations}, '
     r'\lean{alpha\_two}, \lean{beta\_two}, \lean{nR\_no\_common\_root}, \lean{count\_roots\_nR\_le\_one}, '
     r'\lean{realRooted\_nR}, \lean{separable\_hpoly}, \lean{thm\_realroots}\\'),
    (r'with $c,w_a\ge0$ instead), Proposition~\ref{prop:simple}, hence the simplicity of the zeros and the statement '
     r'about $h_k$ in Theorem~\ref{thm:realroots}, Corollary~\ref{cor:logconcave},',
     r'with $c,w_a\ge0$ instead), Corollary~\ref{cor:logconcave},'),
]
PAPER_RE = [
    (r'consists of 45 files that start from', 'consists of 46 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('Lemmas 8.4, 8.6, 8.8, 8.9 and Proposition 8.10 (so all zeros of every $n_k$ are real),',
     'Lemmas 8.4, 8.6, 8.8, 8.9, Propositions 8.10 and 8.11 and Theorem 8.1 (the zeros of every $n_k$ are real and, '
     'except $-1$, simple; those of $h_k$ are real and simple),'),
    ('Proposition 8.10 and the real-rootedness of the $n_k$ are formalized, by a route that replaces',
     'Propositions 8.10 and 8.11 and Theorem 8.1 are formalized, by a route that replaces'),
    ('Not formalized: Lemmas 8.5 and 8.7(3) themselves, Proposition 8.11 (simplicity of the zeros, hence the rest of '
     'Theorem 8.1), Corollary 8.2 and Lemma 8.12',
     'Not formalized: Lemmas 8.5 and 8.7(3) themselves, Corollary 8.2 and Lemma 8.12'),
]

README = [
    ('`Interlace.lean` 与 `RealRoots.lean`）', '`Interlace.lean`、`RealRoots.lean` 与 `SimpleRoots.lean`）'),
    ('共 45 个模块（', '共 46 个模块（'),
    ('与命题 8.10（行多项式只有实根，含引理 8.4、8.6、8.8、8.9）后由 2675 增加',
     '、命题 8.10（行多项式只有实根，含引理 8.4、8.6、8.8、8.9）与命题 8.11、定理 8.1（n_k 除 −1 外只有单根，'
     'h_k 的根都是实数且互不相同）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_realroots.py`。',
     '补丁 `patch_paper_2026-10-10_lean_realroots.py`。第二十项：论文第 8 节命题 8.11 与定理 8.1 的其余部分，新模块 '
     '`SimpleRoots.lean`（交错的推论 `Interlaces.eval_mul_derivative_nonneg`：g ≪ f、a 是 f 的单根时 g(a)·f′(a) ≥ 0；'
     '`count_roots_of_derivative`：实根多项式的导数在非根处至多单根；命题 8.11：`nR_no_common_root`（论文对最小的 j '
     '反证，写成强归纳）、`count_roots_nR_le_one`；定理 8.1：`rootMultiplicity_nrowPoly_le_one`（ℂ 中除 −1 外的根重数 '
     '≤ 1）、`hpoly_root_im_eq_zero`、`separable_hpoly`（h_k 可分，即根都是单根；证明：n_k 除 −1 外的 ⌊2k/3⌋ 个不同'
     '的根经 z ↦ z/(1+z) 映成 h_k 的不同的根，而 deg h_k = ⌊2k/3⌋）与 `thm_realroots`）。推论 8.2 等仍未形式化。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_simpleroots.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_realroots.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_realroots.log`）。同日第二十项：新模块 `SimpleRoots.lean`（论文第 8 节命题 '
     '8.11 与定理 8.1 的其余部分；新定义 `hR k`（`hpoly k` 映到 `ℝ[X]`）与 `zToT`（z ↦ z/(1+z)）只是记号；主陈述 '
     '`thm_realroots` 只用到 `N`、`nrowPoly`、`hpoly` 与 Mathlib 的 `aeval`、`rootMultiplicity`、`Separable`），经 '
     '`lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，'
     '`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_simpleroots.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('N 的每一行单峰、对数凹 | ■■■■□ |',
     'N 的每一行单峰、对数凹 | ■■■■■（实根与单根，2026-10-10）；■■■■□（推论） |'),
    ('未形式化（Mathlib 没有交错多项式理论）',
     '2026-10-10 Lean 续作第十九、二十项形式化了实根与单根（论文命题 8.10、8.11 与定理 8.1：`Interlace.lean`、'
     '`RealRoots.lean`、`SimpleRoots.lean` 的 `thm_realroots`；交错取论文定义后的计数刻画，论文的 Pick 判据与 '
     'Gauss–Lucas 一步改用锥的表示 g = c·f + Σ_a w_a·f/(z−a)）；推论（对数凹、单峰、根的分布、变号、中心极限定理）'
     '未形式化'),
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
