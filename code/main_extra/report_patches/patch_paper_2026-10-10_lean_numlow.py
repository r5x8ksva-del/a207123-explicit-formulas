# -*- coding: utf-8 -*-
r"""Lean 续作第三十九项（2026-10-10）：报告 T4.3(5) 对一切 j 的部分（猜想总表 A5），新模块 `lean/A207123/NumLow.lean`：
- `piSeq`、`piSeq_poly`、`piPoly`、`piPoly_eval`：π_i(q) = [x^i]P_{q−1} 是 q 的次数 ≤ i 的多项式。
- `numLowPoly`、`numLowPoly_spec`、`numLowPoly_natDegree`、`numLowPoly_threshold`：q ≥ j+2 时 ν_j(q) = [x^{q+j}]Num_q
  是 q 的 2j 次多项式，首项 2/(2^j j!)，q = j+1 处缺陷 (−1)^{j+1}(j+1)!。
- `T4_3_five`（汇总）、`T4_3_five_threshold`（门槛精确）；`numLowPoly_one`、`numLowPoly_two`（与 j = 1, 2 的显式式一致）。
根模块加 import，Axioms 加 11 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_numlow.log 读。
论文没有陈述 T4.3：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A5 的完成度与 Lean 一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_numlow.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_numlow.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '73'

PAPER_RE = [
    (r'consists of 64 files that start from', 'consists of 65 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`A326247.lean`、`NegZeros.lean` 与 `Kummer.lean`）', '`A326247.lean`、`NegZeros.lean`、`Kummer.lean` 与 `NumLow.lean`）'),
    ('共 64 个模块（', '共 65 个模块（'),
    ('T3.1 的 Kummer 与下不完全 Gamma 形式和 T3.3(1) 的整表 ₁F₁ 和式（这些论文都没有陈述）后由 2675 增加',
     'T3.1 的 Kummer 与下不完全 Gamma 形式和 T3.3(1) 的整表 ₁F₁ 和式，T4.3(5) 对一切 j 的低次系数（2j 次多项式、'
     '首项与门槛）（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_kummer.py`。',
     '补丁 `patch_paper_2026-10-10_lean_kummer.py`。第三十九项：报告 T4.3(5) 对一切 j 的部分（猜想总表 A5），新模块 '
     '`NumLow.lean`（`piSeq`、`piPoly`：π_i(q) = [x^i]P_{q−1} 是 q 的次数 ≤ i 的多项式，前向差分是 '
     '−π_{i−1}(q) − q·π_{i−3}(q)，用 `MCoeff.lean` 的 `exists_poly_of_fwdDiff_iter` 对 i 归纳，`piPoly_eval`；'
     '`numLowPoly j` = Σ_{i≤j} π_i(X)·p_{j−i}(X + j − i)（p_d 是 T4.1 的 `ndPoly`）；`numLowPoly_spec`：q ≥ j+2 时 '
     'ν_j(q) = [x^{q+j}]Num_q 等于它在 q 处的值；`numLowPoly_natDegree`：2j 次、首项 2/(2^j j!)（i ≥ 1 的项次数 ≤ 2j − i）；'
     '`numLowPoly_threshold`：ν_j(j+1) − numLowPoly j (j+1) = (−1)^{j+1}(j+1)!（只有 i = 0 项偏离，偏差是 T4.1 的缺陷）；'
     '汇总 `T4_3_five`（唯一性、次数、首项、缺陷，写法同 `T4_1`）与 `T4_3_five_threshold`（没有多项式在一切 q ≥ j+1 处'
     '等于 ν_j）；`numLowPoly_one`、`numLowPoly_two` 与 j = 1, 2 的显式式一致）。T4.3(4) 与 A000262 组合定义的等同、'
     '(6)–(8) 不在这里。一次编译通过，无错误、无警告（22 s、峰值 8.0 GB）。Axioms %d 条，全量扫描 %s 个声明，只有'
     '三条标准公理；`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_numlow.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_kummer.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_kummer.log`）。同日第三十九项：新模块 `NumLow.lean`（报告 T4.3(5) 对一切 j）。'
     '主定理 `T4_3_five`、`T4_3_five_threshold` 的陈述只用到已核对的 `Numq`（按 T4.3(2) 的容斥闭式定义，`P_mul_Nser` '
     '说明它等于 P_{q−1}·Σ_k N(k,q)x^k）与 ℚ[X] 的次数、首项；ν_j(q) 写成 `(Numq q).coeff (q + j)`，与报告 '
     '[x^{q+j}]Num_q 一致。`piSeq i n`（[x^i]∏_{v<n} b_v）、`piPoly`（用 `Classical.choose` 取的多项式，由 `piPoly_eval` '
     '刻画）、`numLowPoly` 只是证明里的辅助对象，不承重。经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`'
     '（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_numlow.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('| ■■■■■（(1)–(3)）；■■■■□（(4)–(7)）；■■■□□（(8)） |',
     '| ■■■■■（(1)–(3)、(5)）；■■■■□（(4)、(6)、(7)）；■■■□□（(8)） |'),
    ('Lean：NumStruct 覆盖 (1)–(3)，以及 (4)(5) 的一部分（x=1 处的递推与初值、低次系数的一般恒等式、j≤2 的显式式与门槛） |',
     'Lean：NumStruct 覆盖 (1)–(3)，(4) 的一部分（x=1 处的递推与初值；与 A000262 组合定义的等同未形式化），以及 (5) 的'
     '一般恒等式、j≤2 的显式式与门槛；(5) 对一切 j 的「q≥j+2 时是 q 的 2j 次多项式、首项 2/(2^j j!)、门槛精确（q=j+1 处'
     '缺陷 (−1)^{j+1}(j+1)!）」2026-10-10 已形式化（`NumLow.lean` 的 `T4_3_five`、`T4_3_five_threshold`；证明里 π_i(q) '
     '是 q 的次数 ≤i 的多项式，`piPoly_eval`）；(6)–(8) 未形式化 |'),
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
