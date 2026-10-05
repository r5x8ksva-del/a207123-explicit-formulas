# -*- coding: utf-8 -*-
"""T4.3（(C7) 分子 Num_q）核对（final-audit math-c4c5）。N 取自自写三角递推（已在 s1 中与 core 的 DP 容斥核对 k<=40）。"""
import time
from fractions import Fraction
from math import comb, factorial

from alib import (say, check, N_tri, ptrim, padd, pmul, pscale, peval, pdivmod, stirling1_unsigned, H, write_log)

t0 = time.time()
F = Fraction
KM = 260
NT = N_tri(KM)
QMAX = 40


def b(i):
    return ptrim([1, -1, 0, -i])


def P(m):
    p = [1]
    for i in range(m + 1):
        p = pmul(p, b(i))
    return p


def W(m):
    w = [1]
    for j in range(1, m + 1):
        w = padd(w, [0, 0] + pscale(P(j - 1), j))
    return w


def Fser(q, n=KM + 1):
    if q < 0:
        return [0] * n
    return [NT[k][q] if 0 <= q <= k <= KM else (1 if (k == 0 and q == 0) else 0) for k in range(n)]


def smul(a, bb, n):
    r = [0] * n
    for i, x in enumerate(a[:n]):
        if x:
            for j in range(min(len(bb), n - i)):
                r[i + j] += x * bb[j]
    return r


# ---- 1. F_q 的一阶递推（含 [q=2]x^2）
NS = 200
bad = []
for q in range(1, 31):
    lhs = smul(b(q - 1), Fser(q, NS), NS)
    rhs = smul(ptrim([0, 1, 0, 2 * (q - 1)]) or [0], Fser(q - 1, NS), NS)
    r2 = smul([0, 0, 0, q - 1], Fser(q - 2, NS), NS) if q >= 2 else [0] * NS
    rhs = [rhs[i] + r2[i] + (1 if (q == 2 and i == 2) else 0) for i in range(NS)]
    if lhs != rhs:
        bad.append(q)
# 若不加 [q=2]x^2，q=2 失败
lhs = smul(b(1), Fser(2, NS), NS)
rhs = [a + c for a, c in zip(smul([0, 1, 0, 2], Fser(1, NS), NS), smul([0, 0, 0, 1], Fser(0, NS), NS))]
need = [lhs[i] - rhs[i] for i in range(NS)]
check('T4.3.1-Frec', not bad and need[:5] == [0, 0, 1, 0, 0] and not any(need[5:]),
      'b_{q-1}F_q=(x+2(q-1)x^3)F_{q-1}+(q-1)x^3F_{q-2}+[q=2]x^2，1<=q<=30，到 x^%d；去掉边界项时 q=2 恰差 x^2' % (NS - 1))

# ---- 2. Num_q = P_{q-1} F_q，多项式性 + 三项递推 + 显式 Num_1..Num_4
NUM = {}
polybad = []
for q in range(1, QMAX + 1):
    pr = smul(P(q - 1), Fser(q, KM + 1), KM + 1)
    if any(pr[3 * q - 1:]):
        polybad.append(q)
    NUM[q] = ptrim(pr[:3 * q - 1])
NUM[0] = [1]
NUM[-1] = []
rec = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for q in range(3, QMAX + 1):
    rec[q] = padd(pmul(ptrim([0, 1, 0, 2 * (q - 1)]), rec[q - 1]), pmul(pmul([0, 0, 0, q - 1], b(q - 2)), rec[q - 2]))
ok = all(rec[q] == NUM[q] for q in range(1, QMAX + 1))
given = {1: [0, 1], 2: [0, 0, 2, 0, 1], 3: [0, 0, 0, 2, 2, 7, 0, 2], 4: [0, 0, 0, 0, 2, 8, 13, 15, 29, 0, 6]}
ok2 = all(NUM[q] == given[q] for q in given)
check('T4.3.1-Numrec', not polybad and ok and ok2,
      'P_{q-1}F_q 是多项式（x^{3q-1}..x^%d 为 0，q<=%d），== 三项递推（q>=3，Num_1=x，Num_2=2x^2+x^4），Num_1..Num_4 == 提示词四式' % (KM, QMAX))
# 次数、首项递推、最低项
L = {q: NUM[q][-1] for q in range(1, QMAX + 1)}
ok = all(len(NUM[q]) - 1 == 3 * q - 2 and L[q] == factorial(q - 1) for q in range(1, QMAX + 1))
ok = ok and all(L[q] == (q - 1) * (2 * L[q - 1] - (q - 2) * L[q - 2]) for q in range(3, QMAX + 1))
low = all(next(i for i, c in enumerate(NUM[q]) if c) == q and NUM[q][q] == 2 for q in range(2, QMAX + 1)) and NUM[1] == [0, 1]
check('T4.3.1-deg-lead-low', ok and low, 'deg=3q-2，L_q=(q-1)[2L_{q-1}-(q-2)L_{q-2}]=(q-1)!（q<=%d），最低项 2x^q（2<=q<=%d），Num_1=x' % (QMAX, QMAX))

# ---- 3. 容斥闭式
bad = []
for q in range(1, 21):
    s = []
    for i in range(q + 1):
        term = [1] if i == 0 else W(i - 1)
        for v in range(i, q):
            term = pmul(term, b(v))
        s = padd(s, pscale(term, (-1) ** (q - i) * comb(q, i)))
    if s != NUM[q]:
        bad.append(q)
check('T4.3.2-IE', not bad, 'Num_q=Σ_i(-1)^{q-i}C(q,i)W_{i-1}∏_{v=i}^{q-1}b_v（W_{-1}=1），1<=q<=20; bad=%s' % bad)

# ---- 4. 正项全历史递推与支撑
def posrec(q):
    r = pmul([0, 1], NUM[q - 1])
    for m in range(2, q - 1):
        coef = F(factorial(q - 1), factorial(m))
        r = padd(r, pscale(pmul([0] * (3 * (q - 1 - m)) + [q - 1 - m, 1], NUM[m]), coef))
    tail = [0] * (3 * q - 1)
    tail[3 * q - 5] += (q - 2)
    tail[3 * q - 4] += q
    tail[3 * q - 2] += 1
    r = padd(r, pscale(ptrim(tail), factorial(q - 1)))
    return ptrim(r)


fails = [q for q in range(2, 16) if posrec(q) != NUM[q]]
q2 = posrec(2)
check('T4.3.3-posrec', fails == [2] and q2 == [0, 0, 3, 0, 1],
      '正项全历史递推：2<=q<=15 中只有 q=2 不成立（右端 %s = 3x^2+x^4），3<=q<=15 全部成立' % q2)
fails40 = [q for q in range(3, QMAX + 1) if posrec(q) != NUM[q]]
sup = all(all(c >= 0 for c in NUM[q]) and [i for i, c in enumerate(NUM[q]) if c] == list(range(q, 3 * q - 3)) + [3 * q - 2]
          for q in range(2, QMAX + 1))
check('T4.3.3-support', not fails40 and sup, '3<=q<=%d 正项递推成立；2<=q<=%d 系数全非负，非零项恰为 x^q..x^{3q-4} 与 x^{3q-2}' % (QMAX, QMAX))

# ---- 5. Num_q(1) = A000262(q)
A262 = {0: 1, 1: 1}
for n in range(2, QMAX + 1):
    A262[n] = (2 * n - 1) * A262[n - 1] - (n - 1) * (n - 2) * A262[n - 2]
lah = {n: sum(comb(n - 1, j - 1) * factorial(n) // factorial(j) for j in range(1, n + 1)) for n in range(1, QMAX + 1)}
ok = all(peval(NUM[q], 1) == A262[q] == lah[q] for q in range(1, QMAX + 1))
# e.g.f. exp(z/(1-z)) 的系数直接展开（q<=12）
from fractions import Fraction as Fr
N_E = 14
u = [Fr(0)] + [Fr(1)] * (N_E - 1)          # z/(1-z)
ex = [Fr(0)] * N_E
term = [Fr(1)] + [Fr(0)] * (N_E - 1)
for n in range(N_E):
    ex = [ex[i] + Fr(term[i]) / factorial(n) for i in range(N_E)]
    term = smul(term, u, N_E)
ok = ok and all(ex[q] * factorial(q) == A262[q] for q in range(1, N_E))
check('T4.3.4-A262', ok, 'Num_q(1) == a(q)=(2q-1)a(q-1)-(q-1)(q-2)a(q-2) == Σ_j Lah(q,j) == q![z^q]exp(z/(1-z))（q<=%d / 13），前几项 %s' % (QMAX, [A262[q] for q in range(1, 6)]))

# ---- 6. 低次系数
bad = []
for q in range(1, QMAX + 1):
    v1 = NUM[q][q + 1] if q + 1 < len(NUM[q]) else 0
    v2 = NUM[q][q + 2] if q + 2 < len(NUM[q]) else 0
    f1 = q * q - q - 4
    f2 = F(q ** 4 - 6 * q ** 3 + 7 * q * q - 2 * q + 76, 4)
    if q >= 3 and v1 != f1:
        bad.append(('j1', q))
    if q >= 4 and v2 != f2:
        bad.append(('j2', q))
    if q == 2 and v1 - f1 != (-1) ** 2 * 2:
        bad.append(('j1thr', q, v1, f1))
    if q == 3 and v2 - f2 != (-1) ** 3 * 6:
        bad.append(('j2thr', q, v2, f2))
check('T4.3.5-low', not bad, '[x^{q+1}]Num_q=q^2-q-4（q>=3）、[x^{q+2}]=(q^4-6q^3+7q^2-2q+76)/4（q>=4）；门槛处缺陷 (-1)^{j+1}(j+1)!（j=1: q=2，j=2: q=3），q<=%d; bad=%s' % (QMAX, bad))

# ---- 7. 高次系数 j=0..3
c1 = stirling1_unsigned(QMAX + 2)
bad = []
for q in range(1, QMAX + 1):
    def a(j):
        i = 3 * q - 2 - j
        return NUM[q][i] if 0 <= i < len(NUM[q]) else 0
    fq = factorial(q - 1)
    want = [fq, 0, fq * (q - 1 + H(q - 1)), (q - 1) * fq * (H(q - 1) - 1)]
    if [a(j) for j in range(4)] != want:
        bad.append(q)
    # 与 Stirling 形式一致：j=2: (q-1)c1 + c2；j=3: (q-1)(c2-c1)
    if a(2) != (q - 1) * c1[q][1] + c1[q][2] or a(3) != (q - 1) * (c1[q][2] - c1[q][1]):
        bad.append(('stir', q))
check('T4.3.6-high', not bad, 'a_{q,j}=[x^{3q-2-j}]Num_q：j=0:(q-1)!，j=1:0，j=2:(q-1)!(q-1+H_{q-1})，j=3:(q-1)(q-1)!(H_{q-1}-1)（1<=q<=%d，含 q<=15）; bad=%s' % (QMAX, bad))

# 子断言（用 c4.md 表 6，j<=8；先核对表 6 数值）
def c(q, i):
    return c1[q][i] if 0 <= i <= q else 0


TAB6 = {
    0: lambda q: c(q, 1),
    1: lambda q: 0,
    2: lambda q: (q - 1) * c(q, 1) + c(q, 2),
    3: lambda q: (q - 1) * (c(q, 2) - c(q, 1)),
    4: lambda q: (q - 1) * c(q, 1) - c(q, 2) + c(q, 3),
    5: lambda q: F((q - 1) * (q - 2), 2) * c(q, 1) - (q - 2) * c(q, 2) + (q - 2) * c(q, 3),
    6: lambda q: -F((q - 1) * (5 * q - 6), 4) * c(q, 1) + F(q * q + q - 4, 2) * c(q, 2) - q * c(q, 3) + c(q, 4),
    7: lambda q: F(3 * (q - 1) * (q - 2), 4) * c(q, 1) - (q - 2) * c(q, 2) - (q - 3) * c(q, 3) + (q - 3) * c(q, 4),
    8: lambda q: F((q - 1) * (2 * q * q - q + 54), 24) * c(q, 1) - F(2 * q * q - 4 * q + 5, 2) * c(q, 2) + F(q * q + 3 * q - 8, 2) * c(q, 3) - 2 * (q - 1) * c(q, 4) + c(q, 5),
}
bad = []
for j in range(9):
    for q in range(1, QMAX + 1):
        i = 3 * q - 2 - j
        val = NUM[q][i] if 0 <= i < len(NUM[q]) else 0
        if TAB6[j](q) != val:
            bad.append((j, q))
check('T4.3.6-table6', not bad, 'c4.md 表 6（j<=8）的 Stirling 形式 == 真实 a_{q,j}（1<=q<=%d）; bad=%s' % (QMAX, bad[:5]))

# ---- 8. A_j(z) 与 (7) 的自洽：R_q(y)=y^{3q-2}Num_q(1/y)=Σ_j a_{q,j}y^j；A_0=L，A_1=0，A_2=u-L+L^2/2，A_3=uL-u-L^2/2+L
NZ = 16
Ls = [F(0)] + [F(1, n) for n in range(1, NZ)]      # L=-ln(1-z)
us = [F(0)] + [F(1)] * (NZ - 1)
L2 = smul(Ls, Ls, NZ)
uL = smul(us, Ls, NZ)
A = {0: Ls, 1: [F(0)] * NZ,
     2: [us[i] - Ls[i] + L2[i] / 2 for i in range(NZ)],
     3: [uL[i] - us[i] - L2[i] / 2 + Ls[i] for i in range(NZ)]}
ok = True
for j in range(4):
    for q in range(1, NZ):
        i = 3 * q - 2 - j
        val = NUM[q][i] if 0 <= i < len(NUM[q]) else 0
        if A[j][q] * factorial(q) != val:
            ok = False
# R_q 的定义：[y^j]R_q = a_{q,j}
okR = True
for q in range(1, 15):
    R = [NUM[q][3 * q - 2 - j] if 3 * q - 2 - j >= 0 else 0 for j in range(3 * q - 1)]
    for yv in (F(2), F(-1, 3), F(5, 7)):
        if peval(R, yv) != yv ** (3 * q - 2) * peval(NUM[q], 1 / yv):
            okR = False
check('T4.3.6-Aj', ok and okR, 'R_q(y)=y^{3q-2}Num_q(1/y) 的 y^j 系数 = a_{q,j}（q<=14，三个 y 值）；A_0=L、A_1=0、A_2=u-L+L^2/2、A_3=uL-u-L^2/2+L（到 z^%d），指标 ι 分别为 1、-、2、2 <= floor(j/2)+1' % (NZ - 1))

say('elapsed %.1fs' % (time.time() - t0))
write_log('final_audit_math-c4c5_s3.log')
