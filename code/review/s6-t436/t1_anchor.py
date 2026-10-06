# -*- coding: utf-8 -*-
"""t1：数据锚定。
 (1) 按报告递推构造 Num_q（q<=QN），核对 次数=3q-2、首项=(q-1)!、无常数项；
 (2) 反转多项式 R_q(y)=y^{3q-2}Num_q(1/y) 与反转递推 (R) 逐系数一致（q<=QN，全部系数）；
     截断版 (R)（mod y^J）一直算到 q<=QR，与前者在 q<=QN 上一致；
 (3) Stirling 数 c(q,i)：按定义（L^i/i! 的 e.g.f.）与按递推两种算法一致；
 (4) 小 j 的已知结果：j=0: (q-1)!；j=1: 0；j=2: (q-1)!(q-1+H_{q-1})；j=3: (q-1)(q-1)!(H_{q-1}-1)。
"""
import sys
sys.dont_write_bytecode = True
import time
from fractions import Fraction
from math import factorial
import s6lib as L

t0 = time.time()
QN, QR, J = 80, 300, 41
ok_all = True


def report(name, ok, extra=''):
    global ok_all
    ok_all = ok_all and ok
    print('[%s] %s %s' % ('OK ' if ok else 'BAD', name, extra))


N = L.num_polys(QN)
ok = all(len(N[q]) == 3 * q - 1 and N[q][-1] == factorial(q - 1) and N[q][0] == 0 for q in range(1, QN + 1))
report('Num_q 次数 3q-2、首项 (q-1)!、无常数项', ok, '(q<=%d)' % QN)
print('   Num_1..Num_4 =', [N[q] for q in range(1, 5)])

Rfull = L.R_trunc(QN, 3 * QN)
ok = True
for q in range(1, QN + 1):
    rev = list(reversed(N[q]))                     # 下标 j -> [x^{3q-2-j}]Num_q
    rev = rev + [0] * (3 * QN - len(rev))
    if rev != Rfull[q]:
        ok = False
        print('   mismatch at q =', q)
        break
report('反转递推 (R) 与 Num_q 的反转逐系数一致（全部系数）', ok, '(q<=%d)' % QN)

R = L.R_trunc(QR, J)
ok = all(R[q] == Rfull[q][:J] for q in range(1, QN + 1))
report('截断版 (R) mod y^%d 与全系数版一致' % J, ok, '(q<=%d)' % QN)

c_rec = L.stirling1_rec(QR, 25)
c_egf = L.stirling1_egf(70, 12)
ok = all(c_rec[q][i] == c_egf[q][i] for q in range(71) for i in range(13))
report('c(q,i)：e.g.f. 定义与递推一致', ok, '(q<=70, i<=12)')
ok = all(c_rec[q][0] == (1 if q == 0 else 0) for q in range(QR + 1)) and \
     all(c_rec[q][1] == factorial(q - 1) for q in range(1, QR + 1))
report('c(q,0)=[q=0]，c(q,1)=(q-1)!', ok, '(q<=%d)' % QR)
H = [Fraction(0)]
for n in range(1, QR + 1):
    H.append(H[-1] + Fraction(1, n))
ok = all(c_rec[q][2] == factorial(q - 1) * H[q - 1] for q in range(1, QR + 1))
report('c(q,2)=(q-1)! H_{q-1}', ok, '(q<=%d)' % QR)

# 小 j
ok0 = all(R[q][0] == factorial(q - 1) for q in range(1, QR + 1))
ok1 = all(R[q][1] == 0 for q in range(1, QR + 1))
ok1full = all(L.a_from_num(N, q, 1) == 0 for q in range(1, QN + 1))
ok2 = all(R[q][2] == factorial(q - 1) * (q - 1 + H[q - 1]) for q in range(1, QR + 1))
ok3 = all(R[q][3] == (q - 1) * factorial(q - 1) * (H[q - 1] - 1) for q in range(1, QR + 1))
report('j=0: a_{q,0}=(q-1)!', ok0, '(q<=%d)' % QR)
report('j=1: a_{q,1}=0（子断言 (c)，截断递推）', ok1, '(q<=%d)' % QR)
report('j=1: a_{q,1}=0（子断言 (c)，直接由 Num_q）', ok1full, '(q<=%d)' % QN)
report('j=2: a_{q,2}=(q-1)!(q-1+H_{q-1})', ok2, '(q<=%d)' % QR)
report('j=3: a_{q,3}=(q-1)(q-1)!(H_{q-1}-1)', ok3, '(q<=%d)' % QR)

print('   a_{q,j}, q=1..6, j=0..6:')
for q in range(1, 7):
    print('   q=%d:' % q, [R[q][j] for j in range(7)])
print('ALL_OK' if ok_all else 'SOME_BAD', '  time %.1fs' % (time.time() - t0))
