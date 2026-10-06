# -*- coding: utf-8 -*-
"""t5：把 notes/c4.md §4.8 表 6（j<=8）逐多项式与 s6-t436 构造法的 π_{j,i} 比较，
并直接与真实 a_{q,j}（q<=300 截断递推，q<=80 Num_q）比较。
（本脚本是在 s6-t436 的证明与 t1–t4 全部完成之后、读过表 6 才写的，只做对照。）"""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
from math import factorial
import s6lib as L

ok_all = True


def report(name, ok, extra=''):
    global ok_all
    ok_all = ok_all and ok
    print('[%s] %s %s' % ('OK ' if ok else 'BAD', name, extra))


def P(*cs):          # 升幂系数
    return L.tp_trim([F(c) for c in cs])

def mul(*ps):
    r = [F(1)]
    for p in ps:
        r = L.tp_mul(r, p)
    return r

q1, q2, q3 = P(-1, 1), P(-2, 1), P(-3, 1)
table6 = {
    0: {1: P(1)},
    1: {},
    2: {1: q1, 2: P(1)},
    3: {1: L.tp_scale(q1, -1), 2: q1},
    4: {1: q1, 2: P(-1), 3: P(1)},
    5: {1: L.tp_scale(mul(q1, q2), F(1, 2)), 2: L.tp_scale(q2, -1), 3: q2},
    6: {1: L.tp_scale(mul(q1, P(-6, 5)), F(-1, 4)), 2: L.tp_scale(P(-4, 1, 1), F(1, 2)), 3: P(0, -1), 4: P(1)},
    7: {1: L.tp_scale(mul(q1, q2), F(3, 4)), 2: L.tp_scale(q2, -1), 3: L.tp_scale(q3, -1), 4: q3},
    8: {1: L.tp_scale(mul(q1, P(54, -1, 2)), F(1, 24)), 2: L.tp_scale(P(5, -4, 2), F(-1, 2)),
        3: L.tp_scale(P(-8, 3, 1), F(1, 2)), 4: L.tp_scale(q1, -2), 5: P(1)},
}

Pj = L.P_family(8)
QR, QN = 300, 80
R = L.R_trunc(QR, 9)
N = L.num_polys(QN)
c = L.stirling1_rec(QR, 6)
ok_con = True
ok_dat = True
for j in range(9):
    K = j // 2 + 1
    p, _, const = L.decompose(Pj[j], K)
    mine = {i: L.tp_trim(L.tp_scale(p[i], factorial(i))) for i in range(1, K + 1)}
    theirs = {i: table6[j].get(i, []) for i in range(1, K + 1)}
    if mine != theirs:
        ok_con = False
        print('   j=%d 不同：mine=%s theirs=%s' % (j, mine, theirs))
    for q in range(1, QR + 1):
        s = sum(L.tp_eval(theirs[i], q) * c[q][i] for i in theirs)
        if s != R[q][j] or (q <= QN and s != L.a_from_num(N, q, j)):
            ok_dat = False
            print('   表 6 在 j=%d, q=%d 与真实值不符' % (j, q))
            break
report('表 6（c4.md §4.8，j<=8）与 s6-t436 构造法的 π_{j,i} 逐多项式相同', ok_con)
report('表 6 直接与真实 a_{q,j} 相符', ok_dat, '(j<=8，q<=%d；q<=%d 另用 Num_q)' % (QR, QN))
print('ALL_OK' if ok_all else 'SOME_BAD')
