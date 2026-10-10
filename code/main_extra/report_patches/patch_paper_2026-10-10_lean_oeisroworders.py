# -*- coding: utf-8 -*-
r"""Lean 续作第十六项（2026-10-10）：论文注记 3.5 后半句的形式化，新模块 `lean/A207123/OeisRowOrders.lean`：
行递推的阶 10、22、28、49、55、85 是最小的（`row_min_order_two` … `row_min_order_seven`，`IsLeast`），且等于两个因子的
特征根之积中不同值的个数（`card_row_products_two` … `card_row_products_seven`）。最小性：`k ↦ a_k(n)` 从 k = 0 起满足
常数项非零的 `rowPoly` 递推，只对 k ≥ k₀ 成立的递推可以向后延拓，d < e 时 e×e 的 Hankel 矩阵退化；Hankel 行列式
非零的证书是它模 97 的逆，按 B = 2^20 进位打包、每列一次乘法核对（Kronecker 代换，decide +kernel）。不同乘积的个数：
每个乘积都是 OEIS 特征多项式的根（按层约化），故 ≤ e；`∏_λ (X − λ)` 给出递推，由最小性 ≥ e。系数表与逆矩阵的列由
`code/main_extra/oeis_row_orders_lean.py` 生成并在 Python 里核对。另把 `OeisRemark.lean`、`OeisRows.lean` 文件头里
「没有形式化的」说明改为「本文件没有形式化的」并注明后来在哪个模块补上（重编了这两个模块及其下游）。
根模块加 import，Axioms 加条目；全量扫描的声明数从 logs/lean_axioms_2026-10-10_oeisroworders.log 读。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数（正则替换，只认唯一匹配）；表 5 推论 3.4 与注记 3.5 一行去掉「in part」并加上
  `row_min_order_*`、`card_row_products_*`；「Not formalized」去掉注记 3.5 的阶的最小性。
- paper/reviewer_guide.tex：第 2 节注记 3.5 一句；第 3 节删去 Section 3 一条（已无未形式化的内容）。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_oeisroworders.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_oeisroworders.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '49'

ROW35 = (r'Corollary~\ref{cor:columns}, Remark~\ref{rem:oeis} in part & \lean{T1\_9}, \lean{parity\_min\_order}, '
         r'\lean{oeis\_A207118}--\lean{oeis\_A207122}, \lean{row\_rec}, \lean{row\_rec\_of\_consecutive}, '
         r'\lean{aAlt\_two}, \lean{aAlt\_three}, \lean{oeis\_A207069}, \lean{oeis\_A207070}, '
         r'\lean{oeis\_A207124}--\lean{oeis\_A207127}\\')
PAPER = [
    (ROW35,
     r'Corollary~\ref{cor:columns}, Remark~\ref{rem:oeis} & \lean{T1\_9}, \lean{parity\_min\_order}, '
     r'\lean{oeis\_A207118}--\lean{oeis\_A207122}, \lean{row\_rec}, \lean{row\_rec\_of\_consecutive}, '
     r'\lean{aAlt\_two}, \lean{aAlt\_three}, \lean{oeis\_A207069}, \lean{oeis\_A207070}, '
     r'\lean{oeis\_A207124}--\lean{oeis\_A207127}, \lean{row\_min\_order\_two}--\lean{row\_min\_order\_seven}, '
     r'\lean{card\_row\_products\_two}--\lean{card\_row\_products\_seven}\\'),
    (r'the minimality of the orders of the row recurrences in Remark~\ref{rem:oeis}; ', ''),
]
PAPER_RE = [
    (r'consists of 40 files that start from', 'consists of 41 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

GUIDE = [
    ('Corollary 3.4 with the OEIS recurrences for the columns and the rows in Remark 3.5,',
     'Corollary 3.4 with Remark 3.5 (the OEIS recurrences for the columns and the rows, and the minimality of the row '
     'orders),'),
    ('\\item \\textbf{Section 3:} the minimality of the orders of the row recurrences in Remark 3.5.\n', ''),
]

README = [
    ('`OeisRows.lean` 与 `AsympNumerics.lean`）', '`OeisRows.lean`、`AsympNumerics.lean` 与 `OeisRowOrders.lean`）'),
    ('共 40 个模块（', '共 41 个模块（'),
    ('注记 3.3（含数值）、注记 3.5（行递推阶的最小性除外）、', '注记 3.3（含数值）、注记 3.5、'),
    ('补丁 `patch_paper_2026-10-10_lean_asympnumerics.py`。',
     '补丁 `patch_paper_2026-10-10_lean_asympnumerics.py`。第十六项：注记 3.5 后半句（行递推的阶 10、22、28、49、55、85 是'
     '最小的，且等于两个因子的特征根之积中不同值的个数），新模块 `OeisRowOrders.lean`。最小性：`k ↦ a_k(n)` 从 k = 0 起满足'
     '常数项非零的 `rowPoly` 递推，所以只对 k ≥ k₀ 成立的递推可以向后延拓（`eq_zero_of_rec_of_eventually`），阶 d < e 时'
     ' e×e 的 Hankel 矩阵退化（`hankel_det_eq_zero`、`order_ge_of_hankel`）；Hankel 行列式非零的证书是它模 97 的逆，按 '
     'B = 2^20 进位打包、每列一次乘法核对（Kronecker 代换，`kronCheck`、`hankel_det_ne_zero_of_kron`，decide +kernel；'
     '逐项核对 e³ 次乘加的做法在第 7 行内存超过看门狗上限、被结束，改用这种做法后第 7 行内核核对约 3 秒）。不同乘积的'
     '个数：每个乘积都是 OEIS 特征多项式的根（按层约化，`lvCheck`），故 ≤ e；`∏_λ (X − λ)` 给出递推，由最小性 ≥ e。'
     '`row_min_order_two` … `row_min_order_seven`（`IsLeast`：最小阶就是 e）、`card_row_products_two` … '
     '`card_row_products_seven`。系数表与逆矩阵的列由 `code/main_extra/oeis_row_orders_lean.py` 生成并在 Python 里核对'
     '（另用 BM 模 1000003 与 numpy 数值核对）。`OeisRemark.lean`、`OeisRows.lean` 文件头里「没有形式化的」改为「本文件'
     '没有形式化的」并注明后来在哪个模块补上（两者及下游重编）。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；'
     '`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_oeisroworders.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_asympnumerics.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_asympnumerics.log`）。同日第十六项：新模块 `OeisRowOrders.lean`（论文注记 3.5 '
     '后半句：行递推阶的最小性与不同乘积的个数；陈述 `row_min_order_*`、`card_row_products_*` 只用 `a`、`sig`、'
     '`IsLeast` 与有限集的元素个数，新定义 `ofDig`、`digs`、`hkUnit`、`kronCheck`、`listPoly`、`IsLevel`、`lvStep`、'
     '`lvGet`、`lvAcc`、`lvCheck`、`lvEval`、`lvIter` 与数据 `rowGam2`–`rowGam7`、`rowCols2`–`rowCols7` 只在证明里用，'
     '由 AI 核对），经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）'
     '与 `Checks.lean`，`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_oeisroworders.log`）。'
     % (_ax, DECLS, FRESH)),
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
