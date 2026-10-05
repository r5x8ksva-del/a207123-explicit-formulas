# -*- coding: utf-8 -*-
"""r2：C4-24（A000262）与 C4-25（非负性、支撑、正项全历史递推）的独立复核。
Num_q 用自写三项递推（r1 已把它对原始定义 DP 锚定到 q<=47）。"""
import json
import time
from fractions import Fraction
from math import comb, factorial
from rlib import *

try:
    import sys
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
t0 = time.time()
L = Log('r2_positivity')

QM = 220
Num = num_by_recurrence(QM)
with open(os.path.join(HERE, 'numdp.json')) as f:
    numdp = {int(k): v for k, v in json.load(f).items()}
L.check('r2-anchor', all(Num[q] == numdp[q] for q in numdp), '自写递推 Num_q == r1 中 DP 锚定的 Num_q（q<=47）')

# ---- C4-25 支撑与非负
ok = True
first_bad = None
for q in range(2, QM + 1):
    p = Num[q]
    supp = [i for i, c in enumerate(p) if c != 0]
    if any(c < 0 for c in p) or supp != list(range(q, 3 * q - 3)) + [3 * q - 2]:
        ok = False
        first_bad = first_bad or q
L.check('r2-support', ok, '2<=q<=%d：Num_q 系数全非负，非零项恰为 x^q..x^{3q-4} 与 x^{3q-2}（首个反例 %s）' % (QM, first_bad))

# ---- C4-25 正项全历史递推（逐字按 claims 的式子）
ok = True
for q in range(3, 141):
    s = shift(Num[q - 1], 1)
    for m in range(2, q - 1):
        term = mul(shift([q - 1 - m, 1], 3 * (q - 1 - m)), Num[m])
        s = add(s, scl(term, factorial(q - 1) // factorial(m)))
    bd = [0] * (3 * q - 1)
    bd[3 * q - 5] += q - 2
    bd[3 * q - 4] += q
    bd[3 * q - 2] += 1
    s = add(s, scl(bd, factorial(q - 1)))
    if s != Num[q]:
        ok = False
        L.out('  posrec fail q=%d' % q)
L.check('r2-posrec', ok, '正项全历史递推对 3<=q<=140 与三项递推结果逐系数相等')

# ---- 中间引理 Y_q^{(c)} = (1+(c-1)x)Num_{q-2} + c(q-2)x^3 Y_{q-1}^{(2-1/c)}（关于 c 是仿射+1/c 项乘 c 后为仿射，取 3 个 c 值）
def Y(q, c):
    return add(scl(Num[q - 1], c), mul(bpoly(q - 2), Num[q - 2]))


ok = True
for q in range(4, 80):
    for c in (Fraction(2), Fraction(3, 2), Fraction(-7, 5)):
        lhs = Y(q, c)
        rhs = add(mul([1, c - 1], Num[q - 2]), scl(shift(Y(q - 1, 2 - 1 / c), 3), c * (q - 2)))
        if lhs != rhs:
            ok = False
L.check('r2-Ylemma', ok, 'Y_q^(c) 递推对 4<=q<80、c in {2,3/2,-7/5} 成立（两边对 c 的依赖为 c 的仿射函数，3 个值足以证明对一切 c≠0 成立）')

# ---- 迭代展开后的 Y_q^(2) 公式（c4.md §4.6 中间式）
ok = True
for q in range(3, 80):
    s = []
    for n in range(1, q - 2):
        s = add(s, scl(mul(shift([n, 1], 3 * n - 3), Num[q - n - 1]), factorial(q - 2) // factorial(q - n - 1)))
    s = add(s, scl(shift([0, q - 2, q, 0, 1], 3 * q - 9), factorial(q - 2)))
    if s != Y(q, 2):
        ok = False
        L.out('  Y2 expansion fail q=%d' % q)
L.check('r2-Y2expand', ok, 'Y_q^(2) = sum_{n=1}^{q-3} (q-2)!/(q-n-1)! x^{3n-3}(n+x)Num_{q-n-1} + (q-2)! x^{3q-9}((q-2)x+qx^2+x^4)，3<=q<80')

# ---- C4-24：Num_q(1) = A000262(q)
a = [1, 1]
for n in range(2, QM + 1):
    a.append((2 * n - 1) * a[n - 1] - (n - 1) * (n - 2) * a[n - 2])
lah = lambda n: sum(factorial(n) * comb(n - 1, j - 1) // factorial(j) for j in range(1, n + 1))
oeis = [1, 1, 3, 13, 73, 501, 4051, 37633, 394353, 4596553, 58941091, 824073141, 12470162233,
        202976401213, 3535017524403, 65573803186921, 1290434218669921, 26846616451246353,
        588633468315403843, 13564373693588558173, 327697927886085654441, 8281153039765859726341]
ok = all(ev(Num[q], 1) == a[q] == lah(q) for q in range(1, QM + 1))
ok = ok and all(ev(Num[q], 1) == oeis[q] for q in range(1, len(oeis)))
L.check('r2-A000262', ok, 'Num_q(1) == A000262 递推 == Lah 数之和 (q<=%d)，且 == OEIS 快照 %%S/%%T/%%U 行 (q<=21)' % QM)

# 我的独立推导：Num_q(1) = sum_{j=1}^q C(q,j)(q-1)!/(j-1)!（由容斥式在 x=1 取值，所有 j<=0 项含 b_0(1)=0）
ok = all(ev(Num[q], 1) == sum(comb(q, j) * factorial(q - 1) // factorial(j - 1) for j in range(1, q + 1))
         for q in range(1, QM + 1))
L.check('r2-A000262-alt', ok, '另一证明的核对：Num_q(1) = sum_j C(q,j)(q-1)!/(j-1)!（容斥式在 x=1 处只剩 i>=1 的项），q<=%d' % QM)

# A000262 全为奇数（用于二次因子的 mod 2 论证）
ok = all(a[n] % 2 == 1 for n in range(1, QM + 1))
L.check('r2-A000262-odd', ok, 'A000262(q) 对 1<=q<=%d 全为奇数（递推 (n-1)(n-2) 偶、2n-1 奇，归纳对一切 q 成立）' % QM)
L.close(t0)
