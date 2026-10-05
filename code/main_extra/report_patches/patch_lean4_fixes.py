# -*- coding: utf-8 -*-
"""Lean 形式化第四轮（2026-10-05）发现的三处报告文字问题，按用户同意补上。

1. T1.6 逐项形式漏写「指标越界取 0」（notes/c1.md §7 原有）。若沿用 T1.1 的 U_{-1}≡1，
   (k,m)=(2,1) 时左边 4-2-1-1=0、右边 1，不成立；若再用 T1.4 的 U_0(-1)=1，(k,m)=(0,0) 时左边 -1、右边 1。
2. T1.2 的多项式恒等式在 k=1,2 时要用 u_{-1}≡1、u_{-2}≡0（报告只对 U 写了约定）。
3. T1.3(3) 的判别式 -i(4+27i)<0 只对 i>=1 成立；b_0=1-x 是一次式。

结论本身都不变，只补约定。用法：py -3.14 code/main_extra/report_patches/patch_lean4_fixes.py，
然后运行 code/main_extra/assemble_report.py 重新拼接报告。每处替换都断言原文恰好出现一次。
"""
import sys

ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
P = ROOT + r'\notes\report_parts' + '\\'
if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')


def patch(path, pairs):
    s = open(path, encoding='utf-8').read()
    for a, b in pairs:
        n = s.count(a)
        assert n == 1, (path[-24:], a[:90], n)
        s = s.replace(a, b)
    open(path, 'w', encoding='utf-8').write(s)
    print('patched', path[-28:], len(pairs))


OLD_16 = r"逐项形式：[x^k t^m] 左边 = U_k(m)−U_{k−1}(m)−U_k(m−1)−mU_{k−3}(m)，右边 = [k=m=0]+m[k=2]。"
NEW_16 = (r"逐项形式（指标越界取 0）：[x^k t^m] 左边 = U_k(m)−U_{k−1}(m)−U_k(m−1)−mU_{k−3}(m)，右边 = [k=m=0]+m[k=2]。"
          r"这里不能沿用 T1.1 的 U_{−1}≡1：那样 (k,m)=(2,1) 时左边 = 4−2−1−1 = 0，右边 = 1；再用 T1.4 的 U_0(−1)=1，"
          r"(k,m)=(0,0) 时左边 = −1，右边 = 1。（「越界取 0」原在 notes/c1.md §7，第一版报告漏写，Lean 形式化第四轮发现后补上。）")

OLD_12 = r"且多项式恒等式 u_k(y)−u_k(y−1)=u_{k−1}(y)+y·u_{k−3}(y)。"
NEW_12 = (r"且多项式恒等式 u_k(y)−u_k(y−1)=u_{k−1}(y)+y·u_{k−3}(y)"
          r"（k=1,2 时按 T1.1 对 U 的约定取 u_{−1}≡1、u_{−2}≡0；第一版报告没有对 u 写出这条约定）。")

OLD_133 = r"（b_i 两两互素：公共根会给 (i−j)x³=0；z³−z²−i 判别式 −i(4+27i)<0）"
NEW_133 = (r"（b_i 两两互素：公共根会给 (i−j)x³=0；每个 b_i 无重根：i≥1 时 b_i 的反转多项式 z³−z²−i 的判别式 "
           r"−i(4+27i)<0，b_0=1−x 是一次式）")

patch(P + '02_C1.md', [(OLD_16, NEW_16), (OLD_12, NEW_12), (OLD_133, NEW_133)])
print('done')
