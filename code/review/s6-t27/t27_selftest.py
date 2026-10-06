# -*- coding: utf-8 -*-
"""t27_selftest：库函数自检（与报告内容无关的锚点）。
 (1) 阶乘约定：良定义 ⇔ 分子参数 ≥0；分母参数 <0 时值为 0；与 math.comb 对照二项式；
 (2) 多项式平移、展开与乘积形式的 Q_ω 一致（随机点）；
 (3) 精确零空间与模 p 零空间维数在已知矩阵上正确；
 (4) 多项式二项式 C(x,b) 的前向差分 ΔC(x,b)=C(x,b-1)（含 b=0、负 x）；
 (5) 网格核对的「次数 < 边长 ⇒ 恒为 0」在一个已知非零多项式上确实报出非零。
"""
import sys
sys.dont_write_bytecode = True
import random
from fractions import Fraction
from math import comb, factorial
import t27lib as L

R = L.Reporter()
rnd = random.Random(20261007)

# (1) 约定
T = L.Term('C(m,j)C(k,j)', 1, num=[((1, 0, 0), 0), ((0, 1, 0), 0)],
           den=[((0, 0, 1), 0), ((0, 1, -1), 0), ((0, 0, 1), 0), ((1, 0, -1), 0)])
ok = True
for k in range(0, 9):
    for m in range(0, 9):
        for j in range(-4, 13):
            want = comb(m, j) * comb(k, j) if 0 <= j else 0
            ok = ok and T.val((k, m, j)) == want
ok = ok and T.val((-1, 3, 0)) is None and T.val((3, -1, 0)) is None and T.tt((-1, 3, 0)) == 0
R.check('C(m,j)C(k,j)：与 math.comb 一致；k<0 或 m<0 时不良定义（分子 k!、m!）', ok)

Tc = L.Term('C(2j,j)', 1, num=[((0, 0, 2), 0)], den=[((0, 0, 1), 0), ((0, 0, 1), 0)])
ok = Tc.val((0, 0, -1)) is None and Tc.val((0, 0, 0)) == 1 and Tc.val((0, 0, 3)) == 20
Ti = L.Term('1/j!', 1, num=[], den=[((0, 0, 1), 0)])
ok = ok and Ti.val((0, 0, -1)) == 0 and Ti.val((0, 0, 2)) == Fraction(1, 2)
R.check('约定：C(2j,j) 在 j=-1 不良定义；1/j! 在 j=-1 良定义且为 0', ok)

# (2) 多项式工具与 Q_ω 的两种算法
P = {(1, 0, 0): Fraction(1), (0, 0, 1): Fraction(-2), (0, 0, 0): Fraction(1), (0, 2, 1): Fraction(3, 5)}
ok = True
for _ in range(200):
    x = tuple(rnd.randint(-9, 9) for _ in range(3))
    w = tuple(rnd.randint(-4, 4) for _ in range(3))
    ok = ok and L.p_eval(L.p_shift(P, w), x) == L.p_eval(P, tuple(a - b for a, b in zip(x, w)))
R.check('p_shift：p(x-w) 展开后求值与直接求值一致（200 个随机点）', ok)

T4 = L.Term('E4 型', 1, num=[((1, 0, 1), 0), ((0, 1, 0), 0)],
            den=[((0, 0, 2), 0), ((1, 0, -1), 0), ((0, 0, 1), 0), ((0, 1, -1), 0)],
            P=P, z=(3, Fraction(1, 2), 2))
LA = L.LemmaA(T4, 2, 2)
ok = True
for w in LA.Omega[::3]:
    Qe = LA.Q_expanded(w)
    for _ in range(15):
        x = tuple(rnd.randint(-12, 12) for _ in range(3))
        ok = ok and L.p_eval(Qe, x) == LA.Q(w, x)
    dq = L.p_degs(Qe, 3)
    ok = ok and all(dq[i] <= LA.degQ[w][i] for i in range(3))
R.check('Q_ω：展开式与乘积形式在随机点一致；各变量次数 ≤ degQ 的界', ok)

# (3) 线性代数
M = [[1, 2, 3, 4], [2, 4, 6, 8], [1, 0, 1, 0]]
B = L.nullspace_exact(M, 4)
ok = len(B) == 2 and all(sum(Fraction(a) * b for a, b in zip(row, v)) == 0 for row in M for v in B)
ok = ok and L.nullity_modp(M, 4) == 2 and L.nullity_modp([[1, 0], [0, 1]], 2) == 0
R.check('零空间：精确与模 p 维数正确（已知 3×4 矩阵）', ok)

# (4) 多项式二项式的差分
ok = True
for x in range(-7, 8):
    for b in range(-2, 6):
        ok = ok and L.binom_poly(x + 1, b) - L.binom_poly(x, b) == L.binom_poly(x, b - 1)
ok = ok and L.binom_poly(-1, 1) == -1 and L.binom_poly(5, 2) == 10 and L.binom_poly(3, -1) == 0
R.check('ΔC(x,b)=C(x,b-1)（x∈[-7,7]，b∈[-2,5]，含 C(x,-1)=0）', ok)

# (5) 网格核对能报出非零：故意把一个系数改错
TE1 = T
LA1 = L.LemmaA(TE1, 1, 1)
a_good = {(0, 0, 0): [Fraction(1)], (1, 0, 0): [Fraction(-1)], (0, 1, 0): [Fraction(-1)],
          (1, 1, 0): [Fraction(1)], (1, 1, 1): [Fraction(-1)]}
okg, cnt, deg = LA1.grid_verify(a_good)
a_bad = dict(a_good)
a_bad[(1, 1, 1)] = [Fraction(-1), Fraction(1, 1000)]
okb, cntb, _ = LA1.grid_verify(a_bad)
R.check('网格核对：已知递推 T−T(k−1)−T(m−1)+T(k−1,m−1)−T(k−1,m−1,j−1)=0 通过；改动一个系数后报出非零',
        okg and not okb, '(网格 %s，%d 点)' % (deg, cnt))

sys.exit(R.done())
