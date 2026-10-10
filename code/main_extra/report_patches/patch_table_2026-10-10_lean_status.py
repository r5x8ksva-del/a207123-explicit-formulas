# -*- coding: utf-8 -*-
r"""猜想总表 Lean 状态核对（2026-10-10，第三十二项，只改 `猜想总表.md`）。

前面各项（2026-10-10）形式化了论文定理 3.2(2)(3)、注记 3.3、注记 3.5、定理 4.2、定理 4.4、引理 4.5、注记 5.2，
但 A1、A8、A9、A15 四行的 Lean 一句还是旧的。逐条对照 Lean 文件（引用的名字都在 `lean/A207123/` 里，并经
`Axioms.lean` 的全量扫描）改正：
- A1：渐近式、c_m 的闭式与误差率已形式化，完成度升为 ■■■■■。
- A8：T3.1（不以上升结尾的部分 = ₁F₁）已形式化（`remark_1F1`）；T3.2、T3.3 仍未形式化，完成度不变。
- A9：T2.1–T2.3(1)(2) 已形式化（块分解、带上升数的母函数、系数提取与 r-Stirling 识别）。
- A15：行方向（注记 3.5）已形式化；Barker 的猜想仍未形式化。
每处替换断言原文出现一次；按字节读写（LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_table_2026-10-10_lean_status.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

TABLE = [
    ('| ■■■■□（根的部分 ■■■■■） | 书面证明；c_m 数值核对 m≤20，c_4、c_18 另用精确零化多项式；Lean 只做了「根」的部分'
     '（Growth：existsUnique_rho、rho_strictMono、root_P_min 等），渐近式未形式化 |',
     '| ■■■■■ | 书面证明；c_m 数值核对 m≤20，c_4、c_18 另用精确零化多项式；Lean：根的部分（Growth：existsUnique_rho、'
     'rho_strictMono、root_P_min 等）；渐近式、c_m 的闭式与误差率 2026-10-10 已形式化（论文定理 3.2(2)(3) 与注记 3.3：'
     '`RootExpansion.lean` 的 `thm_asym_two`，`RootAsymp.lean` 的 `thm_asym_three`、`U_asymp_bound`、`cm_eq_W`、`cm_eq_G`，'
     '`AsympRemark.lean` 的 `tendsto_ratio`、`rate_not_improvable`、`cm_four`（c_4 = 215/2））；「主项要 k≫3m 才占优」'
     '是数值观察（论文注记 3.3） |'),
    ('；₁F₁、Laplace 与 Humbert 闭式未形式化；一元 ₁F₁ 版本没找到，见 B6 |',
     '；T3.1（「不以上升结尾」部分 = ₁F₁(1;1−λ;−t/x³)/(1−x)，论文注记 5.2）2026-10-10 已形式化（`EndAscent.lean` 的 '
     '`remark_1F1`、`sum_inv_P_eq_hyp1F1`）；整表的形式 Laplace 表示（T3.2）、₁F₁ 和式与 Humbert 闭式（T3.3）未形式化；'
     '一元 ₁F₁ 版本没找到，见 B6 |'),
    ('| ■■■■■（主公式、T1.5、T2.5 的公式部分） |', '| ■■■■■（主公式、T2.1–T2.3、T1.5、T2.5 的公式部分） |'),
    ('块分解的组合证明（T2.1、T2.3）未形式化；',
     '块分解（T2.1，论文定理 4.2：`Blocks.lean` 的 `blocks_bijOn`、`asc_concatBlk`）、带上升数的母函数（T2.2，论文'
     '定理 4.4：`GenFunXY.lean` 的 `Gxy_rec`、`Gxy_prod`）与系数提取、r-Stirling 识别（T2.3(1)(2)，论文引理 4.5：'
     '`GenFunXY.lean` 的 `coef_formula_xy`，`RStirling.lean` 的 `lemma_coef_partitions`、`stirlingSecond_eq_partCount`）'
     '2026-10-10 已形式化；T2.3 的「竖线模型」组合证明没有形式化（形式证明走代数路线）；'),
    ('| ■■■■■（列方向）；■■■■□（行方向与 Barker 的猜想） |', '| ■■■■■（列方向与行方向）；■■■■□（Barker 的猜想） |'),
    ('行方向与 Barker 的猜想未形式化 |',
     '行方向（n = 2..7 的行递推对一切 k 成立、阶数最小，论文注记 3.5）2026-10-10 已形式化（`OeisRemark.lean` 的 '
     '`row_rec`，`OeisRows.lean` 的 `oeis_A207069` 等，`OeisRowOrders.lean` 的 `row_min_order_two`–`row_min_order_seven`）；'
     'Barker 的猜想未形式化 |'),
]


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    path = os.path.join(ROOT, '猜想总表.md')
    raw = open(path, 'rb').read()
    assert b'\r\n' not in raw
    s = raw.decode('utf-8')
    for old, new in TABLE:
        c = s.count(old)
        assert c == 1, (c, old[:60])
        s = s.replace(old, new)
    open(path, 'wb').write(s.encode('utf-8'))
    print('猜想总表.md: %d edits' % len(TABLE))


if __name__ == '__main__':
    main()
