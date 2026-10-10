# -*- coding: utf-8 -*-
r"""Lean 续作第四十九项（2026-10-10）：notes/16 命题 4(i) 的乘积式（猜想总表 A29 (iii) 的一部分）——k ≥ 2 时
h_k(−1) = 2(−1)^r ∏_l (1 + 2z_l)，z_l 取遍 n_k 的 r = ⌊2k/3⌋ 个不等于 −1 的根。新模块 `lean/A207123/HNegOneProd.lean`：
- `prod_roots_nR_one_add_two`：n_k 全部根上 ∏(1 + 2a) = (−1)^{−1 的重数}·∏_{z ≠ −1}(1 + 2z)（其余根都是单根）。
- `hpoly_eval_neg_one_prod`：n_k 只有实根、首项系数 N(k,k) = 2，在 −1/2 处展开，−1/2 − a = −(1 + 2a)/2，
  再用 h_k(−1) = 2^{k−1}·n_k(−1/2) 与 k − 1 = (⌈k/3⌉ − 1) + ⌊2k/3⌋。
- `hpoly_one_eval_neg_one`：k = 1 时不成立（h_1(−1) = 1，右边是 2）。
根模块加 import，Axioms 加 3 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_hnegoneprod.log 读。
论文没有陈述 h_k(−1)：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A29 的 Lean 一句。
每处替换断言原文出现一次；先在内存里改完全部文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_hnegoneprod.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_hnegoneprod.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '83'

PAPER_RE = [
    (r'consists of 74 files that start from', 'consists of 75 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`NumHigh.lean` 与 `NThreeAtoms.lean`）', '`NumHigh.lean`、`NThreeAtoms.lean` 与 `HNegOneProd.lean`）'),
    ('共 74 个模块（', '共 75 个模块（'),
    ('，notes/13 定理 5(b)（猜想总表 A26 (ii)：N 的三原子单和存在且唯一）（这些论文都没有陈述）后由 2675 增加',
     '，notes/13 定理 5(b)（猜想总表 A26 (ii)：N 的三原子单和存在且唯一），notes/16 命题 4(i) 的乘积式 '
     'h_k(−1) = 2(−1)^r∏(1+2z_l)（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_nthreeatoms.py`。',
     '补丁 `patch_paper_2026-10-10_lean_nthreeatoms.py`。第四十九项：notes/16 命题 4(i) 的乘积式（猜想总表 A29 (iii) '
     '的一部分），新模块 `HNegOneProd.lean`（`hpoly_eval_neg_one_prod`：k ≥ 2 时 h_k(−1) = 2(−1)^r ∏_l (1 + 2z_l)，'
     'z_l 取遍 n_k 的不等于 −1 的根，共 r = ⌊2k/3⌋ 个、两两不同（已有的 `card_roots_nR_ne`）；证明：n_k 只有实根、'
     '首项系数 N(k,k) = 2，在 −1/2 处展开，−1/2 − a = −(1 + 2a)/2，−1 的重数是 ⌈k/3⌉ − 1、其余根都是单根'
     '（`prod_roots_nR_one_add_two`），再用 h_k(−1) = 2^{k−1}·n_k(−1/2)（`hpoly_eval_neg_one_nrow`）与 '
     'k − 1 = (⌈k/3⌉ − 1) + ⌊2k/3⌋；k = 1 时不成立：h_1(−1) = 1，右边是 2（`hpoly_one_eval_neg_one`））。'
     'A29 (iii) 的 Gevrey 型上界、limsup 与非 P-递推仍未形式化。一次编译通过，无错误、无警告（33 s、峰值 8.0 GB；看门狗'
     '上限同第四十八项取 10000 MB）。论文没有陈述 h_k(−1)，只改第 9 节计数。Axioms %d 条，全量扫描 %s 个声明，只有'
     '三条标准公理；`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_hnegoneprod.py`。'
     % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_nthreeatoms.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_nthreeatoms.log`）。同日第四十九项：新模块 `HNegOneProd.lean`（notes/16 '
     '命题 4(i) 的乘积式）。没有新的承重定义：陈述只用到已核对的 `hpoly` 与 `nR`（n_k = Σ_q N(k,q)·z^{q−1} 映到 '
     'ℝ[X]）；乘积取遍 `(nR k).roots.toFinset.erase (-1)`，即 n_k 的不等于 −1 的不同实根，个数是 ⌊2k/3⌋（已有的 '
     '`card_roots_nR_ne`），这些根都是单根，所以与 notes/16「z_l 为 n_k 的 r 个不等于 −1 的根」一致；h_k(−1) 在 ℚ 中'
     '计算，映到 ℝ 后比较。经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条'
     '标准公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_hnegoneprod.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；(i) 与 (iii) 其余（Gevrey 型上界、limsup、非 P-递推）未形式化 |',
     '；notes/16 命题 4(i) 的乘积式 h_k(−1) = 2(−1)^r∏_l(1+2z_l)（k ≥ 2，z_l 为 n_k 的 r = ⌊2k/3⌋ 个不等于 −1 的根）'
     '2026-10-10 也已形式化（`HNegOneProd.lean` 的 `hpoly_eval_neg_one_prod`；k = 1 时不成立，'
     '`hpoly_one_eval_neg_one`）；(i) 与 (iii) 其余（Gevrey 型上界、limsup、非 P-递推）未形式化 |'),
]


def patched(path, reps, regex=()):
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
    return s, len(reps) + len(regex)


def main():
    if not sys.stdout.isatty():
        sys.stdout.reconfigure(encoding='utf-8')
    print('declarations:', DECLS, ' Axioms lines:', _ax)
    jobs = [(os.path.join(ROOT, 'paper', 'main.tex'), [], PAPER_RE),
            (os.path.join(ROOT, 'README.md'), README, README_RE),
            (os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST, ()),
            (os.path.join(ROOT, '猜想总表.md'), TABLE, ())]
    out = [(path,) + patched(path, reps, regex) for path, reps, regex in jobs]
    for path, s, n in out:
        open(path, 'wb').write(s.encode('utf-8'))
        print('%s: %d edits' % (os.path.relpath(path, ROOT), n))


if __name__ == '__main__':
    main()
