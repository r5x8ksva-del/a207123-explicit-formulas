# -*- coding: utf-8 -*-
r"""Lean 续作第三十七项（2026-10-10）：报告 T5.3(2) 中 u_k 负整数零点的三件对一切 k 成立的事（猜想总表 A28 (i)–(iii)），
新模块 `lean/A207123/NegZeros.lean`：
- (a) `uInt_add_prime_pow`：p 素数、p^e > k 时 u_k(m + p^e) ≡ u_k(m) (mod p)；`uInt_neg_modEq_one`、
  `upoly_eval_neg_ne_zero_of_prime_pow`、`dvd_lcm_of_upoly_eval_neg_eq_zero`（零点 −j 只能有 j ∣ lcm(1..k)）。
- (b) `upoly_eval_neg_sign`：k ≥ 4、y > J_k 时 (−1)^k u_k(−y) > 0。
- (c) `upoly_eval_neg_ne_zero_two`：u_k(−(s_k+2)) ≠ 0，G_{−j} 顶端第 4–6 层的闭式 `coeff_gnegPoly_top_three/four/five`。
根模块加 import，Axioms 加 13 条；全量扫描的声明数从 logs/lean_axioms_2026-10-10_negzeros.log 读。
论文没有陈述这三件事（只在开放问题里提到 k ≤ 300 的计算），只改第 9 节的文件数与声明数；审读指南不变。
本补丁同步：
- paper/main.tex：第 9 节文件数、声明数。
- README.md、notes/Lean定义核对清单.md：模块数、声明数与这一项。
- 猜想总表.md：A28 的 Lean 一句。
每处替换断言原文出现一次；按字节读写（都是 LF）。

用法（在任务 C 根目录）：py -3.14 code/main_extra/report_patches/patch_paper_2026-10-10_lean_negzeros.py
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

AXLOG = os.path.join(ROOT, 'logs', 'lean_axioms_2026-10-10_negzeros.log')
_m = re.search(r'A207123 各模块共 (\d+) 个声明；出现过的公理：\[[^\]]*\]；依赖其他公理的声明：0 个',
               open(AXLOG, encoding='utf-8').read())
assert _m, 'no clean full scan in ' + AXLOG
DECLS = _m.group(1)
_ax = len(re.findall(r'^#print axioms', open(os.path.join(ROOT, 'lean', 'Axioms.lean'), encoding='utf-8').read(), re.M))
FRESH = '71'

PAPER_RE = [
    (r'consists of 62 files that start from', 'consists of 63 files that start from'),
    (r'all \d+ declarations of the development', 'all %s declarations of the development' % DECLS),
]

README = [
    ('`Barker.lean` 与 `A326247.lean`）', '`Barker.lean`、`A326247.lean` 与 `NegZeros.lean`）'),
    ('共 62 个模块（', '共 63 个模块（'),
    ('以及引言里的 U_4(m) = A326247(m+2)（A326247 按条目定义）后由 2675 增加',
     '以及引言里的 U_4(m) = A326247(m+2)（A326247 按条目定义），以及 T5.3(2) 中负整数零点的同余、显式根界与'
     '顶端两层（论文没有陈述）后由 2675 增加'),
    ('补丁 `patch_paper_2026-10-10_lean_a326247.py`。',
     '补丁 `patch_paper_2026-10-10_lean_a326247.py`。第三十七项：报告 T5.3(2) 中 u_k 负整数零点的三件对一切 k 成立的事'
     '（猜想总表 A28 (i)–(iii)），新模块 `NegZeros.lean`（(a) `uInt k m` 是 u_k 在整数 m 处的值 Σ_q N(k,q)·C(m+1,q)'
     '（`Ring.choose`，`upoly_eval_int`）；`uInt_add_prime_pow`：p 素数、p^e > k 时 u_k(m+p^e) ≡ u_k(m) (mod p)'
     '（Vandermonde 与 p ∣ C(p^e,i)）；`uInt_neg_modEq_one`、`upoly_eval_neg_ne_zero_of_prime_pow`：p^e ∣ j 时 '
     'u_k(−j) ≡ 1 (mod p)、不为零；`dvd_lcm_of_upoly_eval_neg_eq_zero`：u_k(−j) = 0（j ≥ 1）推出 j ∣ lcm(1..k)；'
     '(b) `upoly_eval_neg_sign`：k ≥ 4、y > J_k = k(k²−k−4)/2 − k + 2 时 (−1)^k u_k(−y) > 0（N(k,·) 严格对数凹给出 '
     'N(k,q+1)/N(k,q) ≥ 2/(k²−k−4)，于是 0 = T_0 < T_1 < ⋯ < T_k，交错和配对为正）；(c) '
     '`upoly_eval_neg_ne_zero_two`：u_k(−(s_k+2)) ≠ 0，用 G_{−j} 顶端第 4–6 层的闭式 (j−1)!、c(j,2)+c(j,3)、'
     '(j−1)!−c(j,2)−c(j,3)（`coeff_gnegPoly_top_three/four/five`）与 (j−1)! < c(j,2)（j ≥ 3）。(i) 中 p = 2 的放宽'
     '与 (iv) 的 k ≤ 300 计算不在这里。第一次编译 7 处错（Ring.choose 被提升到 ℚ、反对角线成员引理名、Pochhammer '
     '引理的环参数、一处下标、gnegPoly_two 的改写等），改后无错误、无警告（25 s、峰值 8.1 GB）。论文没有陈述这三件事，'
     '只改第 9 节计数。Axioms %d 条，全量扫描 %s 个声明，只有三条标准公理；`check_lean_fresh.py` %s PASS；补丁 '
     '`patch_paper_2026-10-10_lean_negzeros.py`。' % (_ax, DECLS, FRESH)),
]
README_RE = [
    (r'\d+ 个声明只依赖三条标准公理（2026-10-10 补了定理 3\.2\(1\) 的最后两句、',
     '%s 个声明只依赖三条标准公理（2026-10-10 补了定理 3.2(1) 的最后两句、' % DECLS),
]

CHECKLIST = [
    ('（`logs/check_lean_fresh_2026-10-10_a326247.log`）。',
     '（`logs/check_lean_fresh_2026-10-10_a326247.log`）。同日第三十七项：新模块 `NegZeros.lean`（报告 T5.3(2) 的 (a)(b)(c)）。'
     '新的承重定义一个：`uInt k m = Σ_{q≤k} N(k,q)·Ring.choose (m+1) q`（`Ring.choose` 是 Mathlib 二项式环上的广义二项式，'
     '对负整数也有定义），已核对它就是 u_k 在整数点的值（`upoly_eval_int` 证明了 `(upoly k).eval m = uInt k m`），所以'
     '同余陈述说的确实是 u_k(m)；其余陈述直接用 `upoly`、`gnegPoly`（已有）与 `Nat.stirlingFirst`（Mathlib）；`negTerm` 只在'
     '证明里用。经 `lean/lean_one.sh` 编译、重编根模块、重跑 `Axioms.lean`（%d 条，%s 个声明，只有三条标准公理）与 '
     '`Checks.lean`（输出不变），`check_lean_fresh.py` %s 项全部 PASS（`logs/check_lean_fresh_2026-10-10_negzeros.log`）。'
     % (_ax, DECLS, FRESH)),
]

TABLE = [
    ('最近 3.6·10⁻⁴（k=30）。未形式化 |',
     '最近 3.6·10⁻⁴（k=30）。(i)–(iii) 2026-10-10 已形式化（`NegZeros.lean`：`uInt_add_prime_pow`（同余）、'
     '`upoly_eval_neg_ne_zero_of_prime_pow`、`dvd_lcm_of_upoly_eval_neg_eq_zero`（零点 −j 只能有 j ∣ lcm(1..k)），'
     '`upoly_eval_neg_sign`（k≥4、y>J_k 时 (−1)^k u_k(−y)>0），`upoly_eval_neg_ne_zero_two`（u_k(−(s_k+2))≠0，'
     'G_{−j} 顶端第 4–6 层闭式 `coeff_gnegPoly_top_three/four/five`））；(i) 中 p=2 的放宽与 (iv) 的 k≤300 计算未形式化 |'),
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
