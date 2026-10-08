# -*- coding: utf-8 -*-
"""复核 s12-b4 的补充观察（不是对笔记断言的核对，而是复核报告里「建议」部分的依据）：
X1  σ=0 时三个坐标 A_p^(0),A_p^(1),A_p^(2) 的 p 进赋值（定理 2(c) 可以加强为三个都不是 P-递推）；
X2  「每个 i 两个原子」这一中间类：W̃_i 在 K_i 中落在 span(x^a,x^b) 的 (a,b)；m=2 时真的给出 U 的表示；
X3  与 m 无关的平移 σ 下各坐标的赋值（看界 -3(p-1)/2+|σ| 的松紧）。"""
import time
from fractions import Fraction as Fr

from s12_common import (Checker, vp, primes_upto, U_core, Wt_poly, reduce_bi, mul_xpow, det3,
                        c_seq, c_at, exact_solve)

ck = Checker('s12_extra')
t0 = time.time()

# X1
pat = True
rows = []
for p in [q for q in primes_upto(101) if q > 2]:
    a = reduce_bi(Wt_poly(p), p)
    v = [vp(t, p) for t in a]
    t = -3 * (p - 1) // 2
    if p >= 5 and v != [t, t, t + 1]:
        pat = False
    if p in (3, 5, 7, 53, 101):
        rows.append(f'p={p}:{v}')
ck.check('X1-all-coords', pat, '观察：5<=p<=101 时 (v_p(A^(0)),v_p(A^(1)),v_p(A^(2)))=(t,t,t+1)，t=-3(p-1)/2，三个坐标都趋于 -∞ ⇒ 三个数列都不是 P-递推的（由引理 2.5）：'
         + '; '.join(rows))

# X2
R = 40
sols = {}
for i in range(1, 9):
    w = [Fr(t) for t in reduce_bi(Wt_poly(i), i)]
    xs = {a: list(mul_xpow((Fr(1), Fr(0), Fr(0)), i, a)) for a in range(-R, R + 1)}
    sols[i] = [(a, b) for a in range(-R, R + 1) for b in range(a + 1, R + 1) if det3([w, xs[a], xs[b]]) == 0]
ck.check('X2-two-atoms-per-fiber', len(sols[1]) > 0 and len(sols[2]) > 0 and all(len(sols[i]) == 0 for i in range(3, 9)),
         '观察：W̃_i∈span_Q(x^a,x^b)（K_i 中，|a|,|b|<=40）的 (a,b) 个数：' + ', '.join(f'i={i}:{len(sols[i])}' for i in sols)
         + f'；i=1 的例子 {sols[1][:4]}，i=2 的全部 {sols[2]}')

# m=2：用 i=1 的一对、i=2 的一对构造「每个 i 两个原子」的表示，并用 U 的数据验证
U = U_core(60, 3)
m = 2
(a1, b1), (a2, b2) = sols[1][0], sols[2][0]
cs1, cs2 = c_seq(1, 90), c_seq(2, 90)
ks = list(range(4, 61))
A = [[1, c_at(cs1, k + 3 * m - a1), c_at(cs1, k + 3 * m - b1), c_at(cs2, k + 3 * m - a2), c_at(cs2, k + 3 * m - b2)] for k in ks]
okc, rank, sol = exact_solve(A, [U[k][m] for k in ks])
ck.check('X2-m2-representation', okc and rank == 5,
         f'U_k(2)=γ0+g1 c_1(k+6-({a1}))+g2 c_1(k+6-({b1}))+g3 c_2(k+6-({a2}))+g4 c_2(k+6-({b2}))，4<=k<=60 精确成立，系数 {[str(s) for s in sol]}'
         '——「每个 i 两个原子」在 m=2 时存在（笔记 §4 的表从 1 个原子跳到 3 个原子，没有这一类）')
# m=3：纤维 3 无解 ⇒ 在这个窗口里没有两原子表示（佐证，不是证明）
ok3 = True
cs3 = c_seq(3, 120)
for (a3, b3) in [(0, 1), (0, 5), (-3, 7), (2, 9)]:
    A = [[1, c_at(cs1, k + 9 - a1), c_at(cs1, k + 9 - b1), c_at(cs2, k + 9 - a2), c_at(cs2, k + 9 - b2),
          c_at(cs3, k + 9 - a3), c_at(cs3, k + 9 - b3)] for k in range(15, 61)]
    okc, _, _ = exact_solve(A, [U[k][3] for k in range(15, 61)])
    if okc:
        ok3 = False
ck.check('X2-m3-sample', ok3, 'm=3：纤维 1、2 取上面的对，纤维 3 任取 4 对 (a,b) 时方程组都无解（与纤维 3 无解一致）')

# X3
p = 61
base = reduce_bi(Wt_poly(p), p)
tab = []
for sigma in range(-6, 7):
    av = mul_xpow(base, p, sigma)
    tab.append((sigma, [vp(t, p) for t in av]))
ck.check('X3-sigma-coords', all(min(v) <= -3 * (p - 1) // 2 + abs(s) for s, v in tab),
         'p=61 各 σ 下三个坐标的赋值：' + '; '.join(f'σ={s}:{v}' for s, v in tab))

print(f'time {time.time() - t0:.1f}s')
import sys
sys.exit(0 if ck.summary() else 1)
