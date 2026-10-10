# -*- coding: utf-8 -*-
r"""Lean 续作第四十四项（2026-10-10）：报告 T4.3(8) 完整形式化——对一切 q ≥ 1，gcd(Num_q, P_{q−1}) = 1，Σ_k N(k,q)x^k
的最简分母恰为 P_{q−1}（猜想总表 A5 的 (8)，报告 ⑥ 第 3 处），新模块 `lean/A207123/NumGcd.lean`：
- `numS`、`numS_eq_comp`：S_{q,i} = Σ_t C(q,t)(q−1−i)^{\underline t} x^{3t} = s_n(x³)（`Laguerre.lean` 的 `lagS`）。
- `bpoly_eq_add`、`prod_Ico_sub_eq`、`term_modEq`、`Numq_modEq`：同余引理 b_i ∣ Num_q − W_i·S_{q,i}。
- `numS_aeval_ne_zero`：S_{q,i} 在 b_i 的每个复根处不为零（对每个 i 统一处理，不分 b_i 是否可约）。
- `Numq_isCoprime_Ppoly`（T4.3(8)）与推论 `Nser_denom_dvd`（若 B·Σ_k N(k,q)x^k 是多项式，则 P_{q−1} ∣ B）。
根模块加 import，Axioms 加 8 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_numgcd.log 读。
论文没有陈述 T4.3：只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md（模块数、声明数、这一项、开头对报告 ⑥ 的说明）、ROADMAP.md（⑥ 第 3 处的待做项）、
  notes/Lean定义核对清单.md。
- 猜想总表.md：A5 的完成度、证据与 Lean 一句，汇总与「与报告的对应」「整理者判断」中关于 A5 的 (8) 的说法。
每处替换断言原文出现一次；先在内存里改完全部文件，全部断言通过后才写盘；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_numgcd.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_numgcd.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '78'

PAPER_RE = [
    (r'consists of 69 files that start from', 'consists of 70 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('两次重新排序），见「当前状态与待办」。',
     '两次重新排序；其中第 3 处 T4.3(8) 2026-10-10 已在 Lean 中完整形式化），见「当前状态与待办」。'),
    ('`HNegOne.lean` 与 `Laguerre.lean`）', '`HNegOne.lean`、`Laguerre.lean` 与 `NumGcd.lean`）'),
    ('共 69 个模块（', '共 70 个模块（'),
    ('，T4.3(8) 证明中引用的 Laguerre 零点定理（α 为自然数）（这些论文都没有陈述）后由 2675 增加',
     '，T4.3(8)（对一切 q，gcd(Num_q, P_{q−1}) = 1）及其证明中引用的 Laguerre 零点定理（α 为自然数）（这些论文都没有陈述）'
     '后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_laguerre.py`。',
     '补丁 `patch_paper_2026-10-10_lean_laguerre.py`。第四十四项：报告 T4.3(8) 的完整形式化（猜想总表 A5 的 (8)，报告 ⑥ '
     '第 3 处），新模块 `NumGcd.lean`（`numS`：S_{q,i} = Σ_t C(q,t)(q−1−i)^{\\underline t} x^{3t}，`numS_eq_comp`：它等于 '
     's_n(x³)；`Numq_modEq`：同余引理 b_i ∣ Num_q − W_i·S_{q,i}，由容斥闭式（`Numq` 就按它定义）逐项在 `AdjoinRoot b_i` '
     '中计算（`term_modEq`：b_v ≡ (i−v)x³、j ≤ i 的项含 b_i、W_{j−1} ≡ W_i，两处符号 (−1)^{q−j} 抵消，`prod_Ico_sub_eq`）；'
     '`numS_aeval_ne_zero`：S_{q,i} 在 b_i 的每个复根 z 处不为零——z³ 虚部非零时用上一项的 Laguerre 结论，z³ 为实数时 '
     'z 也是正实数，S 是正项和；对每个 i 统一处理，不分 b_i 是否可约；`Numq_isCoprime_Ppoly`：q ≥ 1 时 Num_q 与 P_{q−1} 互素'
     '（W_i 与 b_i 互素用已有的 `isCoprime_W_b`，S_{q,i} 与 b_i 互素用 Mathlib 的 '
     '`isCoprime_iff_aeval_ne_zero_of_isAlgClosed`）；推论 `Nser_denom_dvd`：若 B·Σ_k N(k,q)x^k 是多项式，则 P_{q−1} ∣ B，'
     '即最简分母恰为 P_{q−1}）。报告的证明在 b_i 不可约时用共轭根、可约时引用 Szegő；这里两者都不需要。编译改了两轮'
     '（`sum_comp` 有歧义、多写一次 `← map_mul`、`push_neg` 已弃用、互素判据的底域参数是显式的），最终无错误、无警告'
     '（22 s、峰值 8.0 GB）。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_numgcd.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

ROADMAP = [
    ('| 在笔记里补上零点定理的标准证明（正交性加变号点计数，几行），或给出原书的准确出处 |',
     '| 原建议：在笔记里补上零点定理的标准证明，或给出原书的准确出处。2026-10-10 已在 Lean 中解决：对证明用到的情形'
     '（α = i+1 为自然数）用三项递推与根交错证明零点全为实数（`lean/A207123/Laguerre.lean`），并完整形式化 T4.3(8)'
     '（`lean/A207123/NumGcd.lean` 的 `Numq_isCoprime_Ppoly`，对每个 i 统一处理，不分 b_i 是否可约） |'),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_laguerre.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_laguerre.log`）。同日第四十四项：新模块 `NumGcd.lean`（T4.3(8)）。主定理 '
     '`Numq_isCoprime_Ppoly` 的陈述只用到已核对的 `Numq`（容斥闭式）与 `Ppoly`（P_m = ∏_{i≤m} b_i）；推论 '
     '`Nser_denom_dvd` 还用到 `Nser q = Σ_k N(k,q)x^k`。新定义 `numS` 已与报告 T4.3(8) 的 S_{q,i} 对照（求和到 t ≤ q，'
     't > q−1−i 的项因 (q−1−i)^{\\underline t} = 0 而为零），它只出现在证明里。经 `lean/lean_one.sh` 编译、重编根模块、'
     '重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 `Checks.lean`（输出不变），`check_lean_fresh.py` %s 项'
     '全部 PASS（`logs/check_lean_fresh_2026-10-10_numgcd.log`）。' % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('| ■■■■■（(1)–(3)、(5)）；■■■■□（(4)、(6)、(7)）；■■■□□（(8)） |',
     '| ■■■■■（(1)–(3)、(5)、(8)）；■■■■□（(4)、(6)、(7)） |'),
    ('时引用 Szegő 的 Laguerre 零点定理（未重证），',
     '时引用 Szegő 的 Laguerre 零点定理（未重证；2026-10-10 Lean 中已对证明用到的情形证明它，并完整形式化了 (8)），'),
    ('；(8) 证明中引用的 Laguerre 零点定理（α 为自然数，即证明实际用到的情形）2026-10-10 已形式化（',
     '；(8)（对一切 q，gcd(Num_q, P_{q−1}) = 1，最简分母恰为 P_{q−1}）2026-10-10 已完整形式化（`NumGcd.lean` 的 '
     '`Numq_isCoprime_Ppoly`、`Nser_denom_dvd`，同余引理 `Numq_modEq`；对每个 i 统一处理，不分 b_i 是否可约），其中引用的 '
     'Laguerre 零点定理（α 为自然数，即证明实际用到的情形）也已证明（'),
    ('；(6)(7) 与 (8) 的其余部分未形式化 |', '；(6)(7) 未形式化 |'),
    ('证据偏薄（■■■□□）：A5 的 (8)（2026-10-07 加固后，',
     '证据偏薄（■■■□□）：原来只有 A5 的 (8)，2026-10-10 已在 Lean 中完整形式化，升为 ■■■■■（2026-10-07 加固后，'),
    ('A5 的 (8)（b_i 可约时引用的 Laguerre 零点定理）；',
     'A5 的 (8)（b_i 可约时引用的 Laguerre 零点定理；2026-10-10 已在 Lean 中完整形式化）；'),
    ('A5 的 (8)（后者补一段教科书证明即可）',
     'A5 的 (8)（后者补一段教科书证明即可；2026-10-10 已在 Lean 中完整形式化，不再是不确定项）'),
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
            (os.path.join(ROOT, 'ROADMAP.md'), ROADMAP, ()),
            (os.path.join(ROOT, 'notes', 'Lean定义核对清单.md'), CHECKLIST, ()),
            (os.path.join(ROOT, '猜想总表.md'), TABLE, ())]
    out = [(path,) + patched(path, reps, regex) for path, reps, regex in jobs]
    for path, s, n in out:
        open(path, 'wb').write(s.encode('utf-8'))
        print('%s: %d edits' % (os.path.relpath(path, ROOT), n))


if __name__ == '__main__':
    main()
