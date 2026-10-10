# -*- coding: utf-8 -*-
r"""Lean 续作第十八项（2026-10-10）：论文命题 4.7 的形式化（双射的存在，比较两边个数），新模块
`lean/A207123/Bijection.lean`：`NAs k m s`（恰有 s 个上升且不以上升结尾的好序列个数）满足细化引理 1 去掉截断块的
递推，等于 1/∏_{v=0}^{m}(1−x−v·y·x³) 的 x^k y^s 系数（`NAs_eq_g`），即 [3s ≤ k]·S(m+s,m)·C(k+m−2s, k−3s)
（`NAs_explicit`）；于是 3s ≤ k 时它与「{1,…,k+m−2s} 的 (k−3s) 元子集」×「{1,…,m+s} 分成 m 块的集合划分」等势
（`prop_bijection`，`Nonempty (… ≃ …)`；划分用第十七项的 `setParts`）。论文给出的显式双射本身没有形式化。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_bijection.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 加命题 4.7 一行；「Not formalized」里命题 4.7
  一句改为只剩显式的双射。
- paper/reviewer_guide.tex：第 2 节加命题 4.7（计数）；第 3 节 Section 4 一条改为显式双射。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_bijection.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_bijection.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '51'

ROW44 = (r'Theorem~\ref{thm:gfxy}, Lemma~\ref{lem:coef} & \lean{Gxy\_zero}, \lean{Gxy\_rec}, \lean{Gxy\_prod}, '
         r'\lean{coef\_formula\_xy}, \lean{lemma\_coef\_partitions}, \lean{stirlingSecond\_eq\_partCount}\\')
PAPER = [
    (ROW44 + '\n', ROW44 + '\n' + r'Proposition~\ref{prop:bijection} & \lean{NAs\_eq\_g}, \lean{NAs\_explicit}, '
     r'\lean{prop\_bijection}\\' + '\n'),
    (r'the bijection of Proposition~\ref{prop:bijection} (the formal proofs of Theorems~\ref{thm:gfxy} and~\ref{thm:explicit} '
     r'go through the recurrence instead, refined by ascents);',
     r'the explicit form of the bijection of Proposition~\ref{prop:bijection} (the formal version compares the two '
     r'cardinalities);'),
    # 表 5 加了一行后第 30 页放不下（溢出到 39 页、附录 A 移到第 32 页并出 underfull \vbox）；只在表 5 的环境里把
    # 行距压到 0.96 倍，回到 38 页
    ('\\footnotesize\n\\begin{tabular}{l>{\\raggedright\\arraybackslash}p{0.62\\textwidth}}',
     '\\footnotesize\n\\renewcommand{\\arraystretch}{0.96}\n'
     '\\begin{tabular}{l>{\\raggedright\\arraybackslash}p{0.62\\textwidth}}'),
]
PAPER_RE = [
    (r'consists of 42 files that start from', 'consists of 43 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('Lemma 4.5, including the set-partition meaning of $H(m,s,j)$)',
     'Lemma 4.5, including the set-partition meaning of $H(m,s,j)$; Proposition 4.7 by counting)'),
    ('the bijection of Proposition 4.7 (the formal proofs of Theorems 4.4 and 4.6 avoid it).',
     'the explicit bijection of Proposition 4.7 (the formal version only compares the two cardinalities).'),
]

README = [
    ('`OeisRowOrders.lean` 与 `RStirling.lean`）', '`OeisRowOrders.lean`、`RStirling.lean` 与 `Bijection.lean`）'),
    ('共 42 个模块（', '共 43 个模块（'),
    ('引理 4.5（按 y 细化与集合划分的意义）与注记 5.2 后由 2675 增加',
     '引理 4.5（按 y 细化与集合划分的意义）、命题 4.7（双射的存在）与注记 5.2 后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_rstirling.py`。',
     '补丁 `patch_paper_2026-10-10_lean_rstirling.py`。第十八项：命题 4.7（双射的存在），新模块 `Bijection.lean`：'
     '`NAs k m s`（恰有 s 个上升且不以上升结尾的好序列个数）按最大值首次出现的位置分类，满足细化引理 1 去掉截断块'
     '（它以上升结尾）的递推（`NAs_split`、`NAs_rec`、`NAs_one`、`NAs_two`），所以等于 1/∏_{v=0}^{m}(1−x−v·y·x³) 的 '
     'x^k y^s 系数（`NAs_eq_g`），即 [3s ≤ k]·S(m+s,m)·C(k+m−2s, k−3s)（`NAs_explicit`）；于是 3s ≤ k 时它与'
     '「{1,…,k+m−2s} 的 (k−3s) 元子集」×「{1,…,m+s} 分成 m 块的集合划分」等势（`prop_bijection`，陈述为 '
     '`Nonempty (… ≃ …)`）。论文给出的显式双射没有形式化（论文第 9 节与审读指南已改为只剩它）。Axioms %d 条，全量扫描 '
     '%s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_bijection.py`。'
     % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_rstirling.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_rstirling.log`）。同日第十八项：新模块 `Bijection.lean`（论文命题 4.7，'
     '双射的存在；新定义 `NAs`（L k m 中上升数为 s 且 `endsAsc` 为假的个数）由 AI 核对，陈述 `prop_bijection` 用到 `L`、'
     '`asc`、`endsAsc`、`powersetCard` 与第十七项的 `setParts`），经 `lean/lean_one.sh` 编译、重编根模块、重跑 '
     '`Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_bijection.log`）。' % (_ax, DECLS, FRESH)),
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
