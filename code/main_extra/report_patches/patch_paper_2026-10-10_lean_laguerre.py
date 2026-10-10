# -*- coding: utf-8 -*-
r"""Lean 续作第四十三项（2026-10-10）：报告 T4.3(8) 证明中引用的 Laguerre 零点定理（Szegő；报告 ⑥ 第 3 处），
在证明实际用到的 α 为自然数的情形，新模块 `lean/A207123/Laguerre.lean`：
- `lagM`、`lagM_monic_natDegree`、`lagM_interlaces`、`realRooted_lagM`、`lagM_aeval_ne_zero`：首一 Laguerre 多项式
  M_n = (−1)^n n! L_n^{(α)}（三项递推）只有实根、相邻两个交错，虚部非零的复数不是根。
- `lagS`、`coeff_lagS`、`lagS_key`、`lagS_rec`、`lagS_aeval`、`lagS_aeval_ne_zero`、`lagS_aeval_ofReal_ne_zero`：
  s_n(v) = Σ_t C(n+α,t) n^{\underline t} v^t = (−v)^n M_n(−1/v) 在虚部非零处与非负实数处都不为零。
根模块加 import，Axioms 加 10 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_laguerre.log 读。
论文没有陈述 T4.3：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A5 的 Lean 一句。
每处替换断言原文出现一次；先在内存里改完四个文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_laguerre.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_laguerre.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '77'

PAPER_RE = [
    (r'consists of 68 files that start from', 'consists of 69 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`HSecond.lean` 与 `HNegOne.lean`）', '`HSecond.lean`、`HNegOne.lean` 与 `Laguerre.lean`）'),
    ('共 68 个模块（', '共 69 个模块（'),
    ('T5.3(7) 中 h_k 次高项的闭式与它和首项的符号关系、h_k(−1) 的公式与符号（这些论文都没有陈述）后由 2675 增加',
     'T5.3(7) 中 h_k 次高项的闭式与它和首项的符号关系、h_k(−1) 的公式与符号，T4.3(8) 证明中引用的 Laguerre 零点定理'
     '（α 为自然数）（这些论文都没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_hnegone.py`。',
     '补丁 `patch_paper_2026-10-10_lean_hnegone.py`。第四十三项：报告 T4.3(8) 证明中引用的 Laguerre 零点定理（Szegő，报告 '
     '⑥ 第 3 处；证明只用到 α 为自然数的情形），新模块 `Laguerre.lean`（`lagM`：首一 Laguerre 多项式 '
     'M_n = (−1)^n n! L_n^{(α)}，按三项递推 M_{n+2} = (X − (2n+3+α))M_{n+1} − (n+1)(n+1+α)M_n 定义；'
     '`lagM_interlaces`：M_n ≪ M_{n+1}，对 n 归纳，用 `Interlace.lean` 的下锥表示 `cone_of_interlaces` 与上锥交错 '
     '`interlaces_uconeSum`，不用正交性与积分；`realRooted_lagM`、`lagM_aeval_ne_zero`：M_n 只有实根，虚部非零的复数不是根；'
     '`lagS`：s_n(v) = Σ_t C(n+α,t)·n^{\\underline t}·v^t（T4.3(8) 证明里的 S_{q,i} 看成 v = x³ 的多项式），`lagS_rec`'
     '（系数恒等式 `lagS_key` 借 `descPochhammer` 在 ℚ 中证）、`lagS_aeval`：v ≠ 0 时 s_n(v) = (−v)^n M_n(−1/v)；'
     '`lagS_aeval_ne_zero`、`lagS_aeval_ofReal_ne_zero`：s_n 在虚部非零处与非负实数处都不为零）。T4.3(8) 本身'
     '（同余引理与互素性）在下一项。编译改了两轮（缺 `open scoped Nat`、两处 `simp` 把等式化成了析取、一处缺 `ring`、'
     '两个未用的 simp 参数），最终无错误、无警告（22 s、峰值 8.1 GB）。Axioms %d 条，全量扫描 %s 个声明，只有三条标准'
     '公理；`check_lean_fresh.py` %s PASS；补丁 `patch_paper_2026-10-10_lean_laguerre.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_hnegone.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_hnegone.log`）。同日第四十三项：新模块 `Laguerre.lean`（T4.3(8) 证明中引用的 '
     'Laguerre 零点定理，α 为自然数）。新定义两个，已与报告 T4.3(8) 的证明对照：`lagM α n` 按三项递推定义，'
     '`lagS_aeval` 说明 s_n(v) = (−v)^n·M_n(−1/v)，所以 M_n = (−1)^n·n!·L_n^{(α)}（L_n^{(α)}(X) = '
     'Σ_k (−1)^k C(n+α, n−k) X^k/k!）；`lagS α n = Σ_{t≤n} C(n+α,t)·n^{\\underline t}·v^t`，取 n = q−1−i、α = i+1 时'
     '就是报告的 S_{q,i}（x 的多项式里 v = x³）。经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个'
     '声明，只有三条标准公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS'
     '（`logs/check_lean_fresh_2026-10-10_laguerre.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('；(6)–(8) 未形式化 |',
     '；(8) 证明中引用的 Laguerre 零点定理（α 为自然数，即证明实际用到的情形）2026-10-10 已形式化（`Laguerre.lean` 的 '
     '`realRooted_lagM`、`lagS_aeval_ne_zero`：首一 Laguerre 多项式只有实根，S_{q,i} 作为 x³ 的多项式在虚部非零处不为零；'
     '不用正交性，用三项递推与根交错）；(6)(7) 与 (8) 的其余部分未形式化 |'),
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
