# -*- coding: utf-8 -*-
r"""Lean 续作第三十三项（2026-10-10）：报告 T5.2 的其余部分与 T4.1 的 p_3–p_5（论文第 7 节的 p_2、p_3 与表 4），
新模块 `lean/A207123/MCoeff.lean`：
- T5.2：`B_d(k) = (k−d)!·[m^{k−d}]u_k` 在 k ≥ 2d+2 时等于 2d 次多项式 `bPoly d`（首项 2/(2^d·d!)），门槛精确
  （`B_eq_bPoly`、`bPoly_natDegree`、`B_threshold`、`B_threshold_exact`；ẽ_j 的多项式性用前向差分与
  `descPochhammer` 整除）；`T5_2_coeff_two`、`T5_2_coeff_three`（[m^{k−2}]、[m^{k−3}] 的显式式）；`T5_2_asymp`
  （U_k(m) = (2/k!)(m+μ_k)^k(1+O(m^{−2}))）；`upoly_top_three`（C(m+1,·) 基下的前三项）。
- T4.1：`N_sub_three`、`N_sub_four`、`N_sub_five`（p_3、p_4、p_5 的显式式），基点由三角递推算出（`N_table`；写法沿用
  `N_six_four`，不让内核展开 N 的组合定义）；论文第 7 节的 `ndPoly_two`、`ndPoly_three` 与表 4（`table_exc`）。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_mcoeff.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数；表 5 在定理 7.1 一行后加一行「表 4、p_2、p_3」（try_layout 试了两种写法，
  都是 39 页、无警告，取单列一行）。
- paper/reviewer_guide.tex：第 2 节近对角线一句加上表 4。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A4、A11 升为 ■■■■■，B10 记一笔（前六个锚点已核对）。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_mcoeff.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_mcoeff.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '67'

PAPER = [
    (r'Theorem~\ref{thm:neardiag}, Proposition~\ref{prop:newton} & \lean{T4\_1}, \lean{T4\_1\_threshold}, '
     r'\lean{T4\_2\_3}\\',
     r'Theorem~\ref{thm:neardiag}, Proposition~\ref{prop:newton} & \lean{T4\_1}, \lean{T4\_1\_threshold}, '
     r'\lean{T4\_2\_3}\\' '\n'
     r'Table~\ref{tab:exc}, $p_2$, $p_3$ & \lean{ndPoly\_two}, \lean{ndPoly\_three}, \lean{table\_exc}\\'),
]
PAPER_RE = [
    (r'consists of 58 files that start from', 'consists of 59 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('the near-diagonal theorem (Theorem 7.1, Proposition 7.2)',
     'the near-diagonal theorem (Theorem 7.1, Proposition 7.2, the polynomials $p_2$, $p_3$ and Table 4)'),
]

README = [
    ('`ShapeCases.lean` 与 `ShapeRemarks.lean`）', '`ShapeCases.lean`、`ShapeRemarks.lean` 与 `MCoeff.lean`）'),
    ('共 58 个模块（', '共 59 个模块（'),
    ('注记 6.4 的最后两句除外）后由 2675 增加', '注记 6.4 的最后两句除外）、第 7 节的 p_2、p_3 与表 4 后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_shaperemarks.py`。',
     '补丁 `patch_paper_2026-10-10_lean_shaperemarks.py`。第三十三项：报告 T5.2 的其余部分与 T4.1 的 p_3–p_5，新模块 '
     '`MCoeff.lean`（`exists_poly_of_fwdDiff_iter`：前向差分 D+1 次为 0 的数列是 ≤ D 次多项式；e_j(−1,…,n−2) 是 n 的 '
     '2j 次多项式，在 0,…,j−1 处为 0，被 n^{\\underline j} 整除，商 ẽ_j 是 ≤ j 次多项式（`esQ`）；`B_eq_bPoly`、'
     '`bPoly_natDegree`、`B_threshold`、`B_threshold_exact`：B_d(k) = (k−d)!·[m^{k−d}]U_k 在 k ≥ 2d+2 时是 2d 次多项式、'
     '首项 2/(2^d·d!)，B_d(2d+1) 与多项式之差为 (−1)^{d+1}(d+1)!，门槛精确；`T5_2_coeff_two`、`T5_2_coeff_three`：'
     '[m^{k−2}]U_k = (3k⁴−36k³+162k²−313k+422)/(12·(k−2)!)（k ≥ 6）、[m^{k−3}]U_k = (k⁶−30k⁵+379k⁴−2533k³+9570k²'
     '−19331k+13380)/(24·(k−3)!)（k ≥ 8）；`T5_2_asymp`：U_k(m) = (2/k!)(m+μ_k)^k(1+O(m^{−2}))；`upoly_top_three`；'
     '`N_sub_three`、`N_sub_four`、`N_sub_five`：p_3、p_4、p_5 的显式式（k ≥ 8、10、12），基点 N(8,5) = 574、'
     'N(10,6) = 6012、N(12,7) = 70674 由三角递推算出（`N_table`，写法沿用 `N_six_four`：实例先用 rw 代入数字等式，'
     '算术在变量层面做，不让内核展开 N 的组合定义）；论文第 7 节的 `ndPoly_two`、`ndPoly_three` 与表 4 `table_exc`）。'
     'Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_mcoeff.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_shaperemarks.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_shaperemarks.log`）。同日第三十三项：新模块 `MCoeff.lean`（报告 T5.2 的其余部分、'
     'T4.1 的 p_3–p_5 与论文表 4；没有新的承重定义：陈述只用 `upoly`、`N`、`ndPoly`、`ndEsym`（都是已有定义）与显式'
     '多项式；`esPoly`、`esQ`、`bPoly` 是证明里构造的多项式，`bPoly d` 出现在 `B_eq_bPoly`、`bPoly_natDegree` 的陈述里，'
     '门槛精确的陈述 `B_threshold_exact` 不用它；`muK k` 就是 (k²−2k−1)/2），经 `lean/lean_one.sh` 编译、重编根模块、'
     '重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_mcoeff.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('| ■■■■■（一般定理与门槛）；■■■■□（p_3–p_5 的显式式） |', '| ■■■■■ |'),
    ('ndPoly_zero_one（第四轮；p_2 见 NumStruct 的 N_sub_two） |',
     'ndPoly_zero_one（第四轮；p_2 见 NumStruct 的 N_sub_two）；p_3–p_5 的显式式与论文表 4（门槛以下的值与缺陷）'
     '2026-10-10 已形式化（`MCoeff.lean` 的 `N_sub_three`、`N_sub_four`、`N_sub_five`、`ndPoly_two`、`ndPoly_three`、'
     '`table_exc`；基点 N(8,5) = 574、N(10,6) = 6012、N(12,7) = 70674 由三角递推算出，`N_table`） |'),
    ('| ■■■■■（B_d(k) 的公式与前两个系数）；■■■■□（其余） |', '| ■■■■■ |'),
    ('；「k≥2d+2 时是 2d 次多项式、门槛精确」与 [m^{k−2}]、[m^{k−3}] 未形式化 |',
     '；其余部分 2026-10-10 已形式化（`MCoeff.lean`：`B_eq_bPoly`、`bPoly_natDegree`、`B_threshold_exact`（k≥2d+2 时 '
     'B_d(k) 是 2d 次多项式，门槛精确），`T5_2_coeff_two`、`T5_2_coeff_three`（[m^{k−2}]、[m^{k−3}] 的显式式），'
     '`T5_2_asymp`（U_k(m) = (2/k!)(m+μ_k)^k(1+O(m^{−2}))），`upoly_top_three`（C(m+1,·) 基下的前三项）） |'),
    ('模式总数 2, 7, 51, 459, 4990, 63537, 928393 没有公式 |',
     '模式总数 2, 7, 51, 459, 4990, 63537, 928393 没有公式；前六个锚点 D(2d+2,d)（d ≤ 5）2026-10-10 已在 Lean 中由三角'
     '递推算出（`MCoeff.lean` 的 `N_table`） |'),
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
