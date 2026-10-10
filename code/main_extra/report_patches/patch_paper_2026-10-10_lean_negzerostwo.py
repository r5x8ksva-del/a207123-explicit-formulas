# -*- coding: utf-8 -*-
r"""Lean 续作第四十项（2026-10-10）：报告 T5.3(2)(a) 中 p = 2 的放宽（猜想总表 A28 (i)），新模块
`lean/A207123/NegZerosTwo.lean`：
- `N_even_top`：k ≥ 4、k − 1 ≤ q ≤ k 时 N(k,q) 是偶数（N(k,k) = 2、N(k,k−1) = k² − k − 4）。
- `uInt_add_two_pow`、`uInt_add_mul_two_pow`：k ≥ 4、2^e ≥ k − 1 时 u_k(m + 2^e) ≡ u_k(m) (mod 2)。
- `uInt_neg_modEq_one_two`、`upoly_eval_neg_ne_zero_of_two_pow`：此时 2^e ∣ j 推出 u_k(−j) ≡ 1 (mod 2)、不为 0。
- `two_pow_factorization_lt_of_upoly_eval_neg_eq_zero`：k ≥ 4、u_k(−j) = 0 时 2^{v_2(j)} < k − 1。
根模块加 import，Axioms 加 6 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_negzerostwo.log 读。
论文没有陈述 T5.3(2)：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A28 的 Lean 一句。
每处替换断言原文出现一次；先在内存里改完四个文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_negzerostwo.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_negzerostwo.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '74'

PAPER_RE = [
    (r'consists of 65 files that start from', 'consists of 66 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`Kummer.lean` 与 `NumLow.lean`）', '`Kummer.lean`、`NumLow.lean` 与 `NegZerosTwo.lean`）'),
    ('共 65 个模块（', '共 66 个模块（'),
    ('以及 T5.3(2) 中负整数零点的同余、显式根界与顶端两层，',
     '以及 T5.3(2) 中负整数零点的同余（含 p = 2 的放宽）、显式根界与顶端两层，'),
    ('补丁 `patch_paper_2026-10-10_lean_numlow.py`。',
     '补丁 `patch_paper_2026-10-10_lean_numlow.py`。第四十项：报告 T5.3(2)(a) 中 p = 2 的放宽（猜想总表 A28 (i)，'
     'notes/15 注 1.1），新模块 `NegZerosTwo.lean`（`N_even_top`：k ≥ 4、k − 1 ≤ q ≤ k 时 N(k,q) 是偶数；'
     '`uInt_add_two_pow`、`uInt_add_mul_two_pow`：k ≥ 4、2^e ≥ k − 1 时 u_k(m + 2^e) ≡ u_k(m) (mod 2)（q < 2^e 的项'
     '沿用 `choose_add_prime_pow_sub`，其余的项只有 q ∈ {k−1, k}，系数是偶数）；`uInt_neg_modEq_one_two`、'
     '`upoly_eval_neg_ne_zero_of_two_pow`：此时 2^e ∣ j 推出 u_k(−j) ≡ 1 (mod 2)、不为 0；'
     '`two_pow_factorization_lt_of_upoly_eval_neg_eq_zero`：k ≥ 4、u_k(−j) = 0 时 j 的 2-部分 2^{v_2(j)} < k − 1）。'
     '注 1.1 关于计算量（约 1%%）的说法与 (iv) 的 k ≤ 300 计算不在这里。编译改了一处（`rfl` 消去 q = k 时换掉的是 k），'
     '最终无错误、无警告（19 s、峰值 8.0 GB）。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；'
     '`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_negzerostwo.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_numlow.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_numlow.log`）。同日第四十项：新模块 `NegZerosTwo.lean`（报告 T5.3(2)(a) 中 '
     'p = 2 的放宽）。没有新定义；陈述只用到已核对的 `N`、`uInt`（u_k 在整数点的值，第三十七项已核对）与 `upoly`。'
     '经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 '
     '`Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_negzerostwo.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；(i) 中 p=2 的放宽与 (iv) 的 k≤300 计算未形式化 |',
     '；(i) 中 p=2 的放宽（k≥4、2^e≥k−1）2026-10-10 也已形式化（`NegZerosTwo.lean`：`uInt_add_two_pow`、'
     '`upoly_eval_neg_ne_zero_of_two_pow`、`two_pow_factorization_lt_of_upoly_eval_neg_eq_zero`（零点 −j 的 2-部分 '
     '2^{v_2(j)}<k−1））；(iv) 的 k≤300 计算未形式化 |'),
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
