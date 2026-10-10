# -*- coding: utf-8 -*-
r"""Lean 续作第四十二项（2026-10-10）：h_k(−1) 的公式与符号（猜想总表 A29 (iii) 的前两句，notes/16 命题 4(i)(ii)），
新模块 `lean/A207123/HNegOne.lean`：
- `hpoly_eval_neg_one`、`hpoly_eval_neg_one_nrow`：k ≥ 1 时 h_k(−1) = Σ_q (−1)^{q−1}2^{k−q}N(k,q) = 2^{k−1}n_k(−1/2)。
- `hpoly_eval_neg_one_sign`（辅助 `prod_mul_add_one_sign`）：h_k(−1) ≠ 0 时符号是 (−1)^{#{h_k 在 (−1,0) 中的根}}。
- `hpoly_two_eval_neg_one`：h_2(−1) = 0。
根模块加 import，Axioms 加 5 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_hnegone.log 读。
论文没有陈述这件事：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A29 的 Lean 一句。
每处替换断言原文出现一次；先在内存里改完四个文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_hnegone.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_hnegone.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '76'

PAPER_RE = [
    (r'consists of 67 files that start from', 'consists of 68 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`NegZerosTwo.lean` 与 `HSecond.lean`）', '`NegZerosTwo.lean`、`HSecond.lean` 与 `HNegOne.lean`）'),
    ('共 67 个模块（', '共 68 个模块（'),
    ('T5.3(7) 中 h_k 次高项的闭式与它和首项的符号关系（这些论文都没有陈述）后由 2675 增加',
     'T5.3(7) 中 h_k 次高项的闭式与它和首项的符号关系、h_k(−1) 的公式与符号（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_hsecond.py`。',
     '补丁 `patch_paper_2026-10-10_lean_hsecond.py`。第四十二项：h_k(−1) 的公式与符号（猜想总表 A29 (iii) 的前两句，'
     'notes/16 命题 4(i)(ii)），新模块 `HNegOne.lean`（`hpoly_eval_neg_one`、`hpoly_eval_neg_one_nrow`：k ≥ 1 时 '
     'h_k(−1) = Σ_q (−1)^{q−1}2^{k−q}N(k,q) = 2^{k−1}n_k(−1/2)；`hpoly_eval_neg_one_sign`：h_k(−1) ≠ 0 时符号是 '
     '(−1)^{#{h_k 在 (−1,0) 中的根}}（h_k 只有实根、h_k(0) = 1，h_k(−1)·h_k(0) = lc²∏_t t(t+1)，辅助引理 '
     '`prod_mul_add_one_sign`）；`hpoly_two_eval_neg_one`：h_2(−1) = 0）。命题 4(i) 的乘积式、3 ≤ k ≤ 1000 时 h_k(−1) ≠ 0 '
     '的计算、(iii) 的 Gevrey 型上界与 (★)（A30）不在这里。编译改了一处（`Multiset.filter_cons_of_pos` 的谓词要显式给出，'
     '否则被推成 `And (−1 < a)`），最终无错误、无警告（21 s、峰值 8.0 GB）。Axioms %d 条，全量扫描 %s 个声明，只有三条'
     '标准公理；`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_hnegone.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_hsecond.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_hsecond.log`）。同日第四十二项：新模块 `HNegOne.lean`（h_k(−1) 的公式与符号）。'
     '没有新定义；陈述只用到已核对的 `hpoly`、`nrowPoly`、`N` 与 `hR`（h_k 映到 ℝ[X]，`SimpleRoots.lean`）；'
     '「(−1,0) 中的根数」写成 `hR k` 的根（计重数）中满足 −1 < t < 0 的个数。经 `lean/lean_one.sh` 编译、重编根模块、重跑 '
     '`Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_hnegone.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；(i)(iii) 未形式化 |',
     '；(iii) 的前两句（h_k(−1) = Σ_q(−1)^{q−1}2^{k−q}N(k,q) = 2^{k−1}n_k(−1/2)，h_k(−1)≠0 时符号是 (−1)^{(−1,0) 中的根数}，'
     'h_2(−1)=0）2026-10-10 也已形式化（`HNegOne.lean` 的 `hpoly_eval_neg_one`、`hpoly_eval_neg_one_nrow`、'
     '`hpoly_eval_neg_one_sign`、`hpoly_two_eval_neg_one`）；(i) 与 (iii) 其余（Gevrey 型上界、limsup、非 P-递推）未形式化 |'),
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
