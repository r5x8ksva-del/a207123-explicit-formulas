# -*- coding: utf-8 -*-
r"""Lean 续作第三十八项（2026-10-10）：报告 T3.1 的 Kummer 形式与下不完全 Gamma 形式、T3.3(1) 的整表 ₁F₁ 和式
（猜想总表 A8 的一部分），新模块 `lean/A207123/Kummer.lean`：
- `sum_choose_div_sub`：部分分式恒等式 Σ_{q≤n} (−1)^q C(n,q)/(λ − q) = (−1)^n n!/∏_{q≤n}(λ − q)。
- `kummer_1F1`、`remark_kummer`：₁F₁(1; 1−λ; a) = e^a·₁F₁(−λ; 1−λ; −a)。
- `sum_inv_P_eq_lowerGamma`、`remark_lowerGamma`：Σ_m t^m/P_m = −x^{−3}·e^a·a^λγ(−λ,a)（报告的形式定义）。
- `W_div_P_eq_sum`、`coeff_hyp1F1_shift`、`T3_3_one_coeff`、`T3_3_one`、`remark_T3_3_one`：
  F = Σ_j κ_j·(t^j/b_j)·₁F₁(1; j+1−λ; −t/x³)（逐系数，t 进收敛）。
根模块加 import，Axioms 加 10 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_kummer.log 读。
论文注记 5.2 只写了 ₁F₁ 形式，没有陈述这些；只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A8 的 Lean 一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_kummer.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_kummer.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '72'

PAPER_RE = [
    (r'consists of 63 files that start from', 'consists of 64 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`A326247.lean` 与 `NegZeros.lean`）', '`A326247.lean`、`NegZeros.lean` 与 `Kummer.lean`）'),
    ('共 63 个模块（', '共 64 个模块（'),
    ('以及 T5.3(2) 中负整数零点的同余、显式根界与顶端两层（论文没有陈述）后由 2675 增加',
     '以及 T5.3(2) 中负整数零点的同余、显式根界与顶端两层，T3.1 的 Kummer 与下不完全 Gamma 形式和 T3.3(1) 的整表 '
     '₁F₁ 和式（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_negzeros.py`。',
     '补丁 `patch_paper_2026-10-10_lean_negzeros.py`。第三十八项：报告 T3.1 的 Kummer 形式与下不完全 Gamma 形式、T3.3(1) '
     '的整表 ₁F₁ 和式（猜想总表 A8 的一部分），新模块 `Kummer.lean`（`sum_choose_div_sub`：部分分式恒等式 '
     'Σ_{q≤n} (−1)^q C(n,q)/(λ−q) = (−1)^n n!/∏_{q≤n}(λ−q)，按 n 归纳；`kummer_1F1`：特征 0 的域里 λ 不是自然数时 '
     '₁F₁(1; 1−λ; a) = e^a·₁F₁(−λ; 1−λ; −a)，`remark_kummer` 取 ℚ(x)；`sum_inv_P_eq_lowerGamma`、`remark_lowerGamma`：'
     'Σ_m t^m/P_m = −x^{−3}·e^a·a^λγ(−λ,a)，a^λγ(−λ,a) 按报告取形式定义 Σ_n (−a)^n/(n!(n−λ))；`T3_3_one`、'
     '`remark_T3_3_one`：F = Σ_m G_m t^m = Σ_j κ_j·(t^j/b_j)·₁F₁(1; j+1−λ; −t/x³)（κ_0 = 1、κ_j = j·x²；和按 t 进收敛，陈述成'
     '逐系数相等，`T3_3_one_coeff`），用 `W_div_P_eq_sum`（G_m = W_m/P_m = Σ_j κ_j/∏_{i=j}^m b_i）与 '
     '(j+1−λ)_n = (−1)^n x^{−3n}∏ b_{j+i}）。T3.3(1) 的 Kummer 单级数形式、T3.2 的形式 Laplace 表示与 T3.3(2) 的 Humbert '
     '闭式不在这里。编译改了四轮（field_simp 收尾与否、`hΠ` 这个名字里的 Π 是关键字、`∏ … / b` 的优先级、'
     '`linear_combination` 的系数），最终无错误、无警告（24 s、峰值 8.1 GB）。Axioms %d 条，全量扫描 %s 个声明，只有'
     '三条标准公理；`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_kummer.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_negzeros.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_negzeros.log`）。同日第三十八项：新模块 `Kummer.lean`（报告 T3.1 的 Kummer 与'
     '下不完全 Gamma 形式、T3.3(1)）。新的承重定义三个，已与报告逐条对照：`expSer z = Σ_n zⁿ tⁿ/n!`（即 e^{zt}）；'
     '`lowerGammaSer λ z = Σ_n (−z)ⁿ tⁿ/(n!(n − λ))`，取 z = −1/x³ 时就是报告对 a^λγ(−λ,a) 的形式定义 '
     'Σ_n (−a)ⁿ/(n!(n−λ))（a = −t/x³）；`kappa x j` 是 κ_0 = 1、κ_j = j·x²。`hyp1F1`（已有）的参数含义：'
     '`hyp1F1 a b z = Σ_n (a)_n/(b)_n·zⁿ/n!·tⁿ`，即 ₁F₁(a; b; z t)。T3.3(1) 的整表写成 `W_m(x)/P_m(x)`，它就是 G_m（`P_mul_G`）；'
     '无穷和按 t 进收敛的含义陈述成逐系数相等。经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个'
     '声明，只有三条标准公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_kummer.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；整表的形式 Laplace 表示（T3.2）、₁F₁ 和式与 Humbert 闭式（T3.3）未形式化；一元 ₁F₁ 版本没找到，见 B6 |',
     '；T3.1 的 Kummer 形式与下不完全 Gamma 形式、T3.3(1) 的整表 ₁F₁ 和式 F = Σ_j κ_j(t^j/b_j)₁F₁(1; j+1−λ; −t/x³) '
     '2026-10-10 已形式化（`Kummer.lean` 的 `kummer_1F1`、`remark_kummer`、`sum_inv_P_eq_lowerGamma`、`remark_lowerGamma`、'
     '`T3_3_one`、`remark_T3_3_one`；共同的部分分式恒等式 `sum_choose_div_sub`）；整表的形式 Laplace 表示（T3.2）、T3.3(1) '
     '的 Kummer 单级数形式与 Humbert 闭式（T3.3(2)）未形式化；一元 ₁F₁ 版本没找到，见 B6 |'),
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
