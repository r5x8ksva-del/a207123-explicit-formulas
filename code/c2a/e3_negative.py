# -*- coding: utf-8 -*-
"""探索 3：「不存在形如 sum_s A(s) C(k+c-2s, m+s+d) 的单和」定理的代数事实核对 + 线性方程组反证的数值佐证。"""
import os, sys, time
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c2a_lib import *  # noqa
from core import U_fast_table
from polylib import P_poly, b_poly, pmul, padd, pshift, pscale, pdiv, pderiv, trim

F = [Fr(-1), Fr(1), Fr(0), Fr(1)]          # f = x^3 + x - 1 = -b_1


def red(p):
    return [Fr(c) for c in pdiv(p, F)[1]] if trim(p) else []


def mul(a, b):
    return red(pmul(a, b))


def egcd_inv(a):
    """a 在 Q[x]/(f) 中的逆（扩展欧几里得）。"""
    r0, r1 = [Fr(c) for c in F], red(a)
    s0, s1 = [], [Fr(1)]
    while trim(r1):
        q, r = pdiv(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, padd(s0, pscale(pmul(q, s1), -1))
    # r0 是常数
    assert len(trim(r0)) == 1
    return red(pscale(s0, Fr(1) / r0[0]))


def norm(a):
    """N_{Q(xi)/Q}(a) = det(乘 a 的矩阵)，基 1, x, x^2。"""
    cols = [red(pmul(a, pshift([1], i))) for i in range(3)]
    Mx = [[(cols[j][i] if i < len(cols[j]) else Fr(0)) for j in range(3)] for i in range(3)]
    (a1, b1, c1), (a2, b2, c2), (a3, b3, c3) = Mx
    return a1 * (b2 * c3 - b3 * c2) - b1 * (a2 * c3 - a3 * c2) + c1 * (a2 * b3 - a3 * b2)


def W_poly(m):
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
    return W


def eq(a, b):
    return trim(red(padd(a, pscale(b, -1)))) == []


xi = [Fr(0), Fr(1)]
ok_all = True
print('b_1 mod f == 0:', eq(b_poly(1), []))
print('Norm(xi)=', norm(xi), ' Norm(1+xi)=', norm([Fr(1), Fr(1)]))
print('x(1+3x^2) == 3-2x mod b_1:', eq(pmul(xi, [1, 0, 3]), [3, -2]), ';  (1-x)^2 == x^6:', eq(pmul([1, -1], [1, -1]), pshift([1], 6)))
for m in range(1, 21):
    W = W_poly(m)
    Pm = P_poly(m)
    q, r = pdiv(Pm, b_poly(1))
    assert trim(r) == []
    a1 = eq(W, [0, 1, 1])                                                   # W_m == x + x^2
    a2 = eq(q, pscale(pshift([1], 3 * m), (-1) ** (m - 1) * factorial(m - 1)))  # P_m/b_1 == (-1)^{m-1}(m-1)! x^{3m}
    # 留数恒等式：W_m(xi) u'(xi) / P_m'(xi) == (-1)^m (1+xi) xi^{-3m-2} / (m-1)!
    up = mul(mul(pmul(xi, xi), [3, -2]), egcd_inv(pmul([1, -1], [1, -1])))
    lhs = mul(mul(red(W), up), egcd_inv(red(pderiv(Pm))))
    xinv = egcd_inv(xi)
    rhs = [Fr(1), Fr(1)]
    for _ in range(3 * m + 2):
        rhs = mul(rhs, xinv)
    rhs = pscale(rhs, Fr((-1) ** m, factorial(m - 1)))
    a3 = eq(lhs, rhs)
    if not (a1 and a2 and a3):
        ok_all = False
        print('FAIL m=', m, a1, a2, a3)
print('m=1..20: W_m==x+x^2, P_m/b_1==(-1)^{m-1}(m-1)!x^{3m}, residue identity:', ok_all)

# ---- 数值佐证：解线性方程组 U_k(m) = sum_s A(s) C(k+c-2s, s+e)（k0<=k<=K），检查是否无解
def solvable(seq, c, e, k0, K):
    s_lo = max(0, -e)
    s_hi = (K + c - e) // 3
    if s_hi < s_lo:
        return False
    unk = list(range(s_lo, s_hi + 1))
    rows = []
    for k in range(k0, K + 1):
        rows.append([Fr(binom(k + c - 2 * s, s + e)) for s in unk] + [Fr(seq[k])])
    # 高斯消元判相容
    ncol = len(unk)
    piv_row = 0
    for col in range(ncol):
        pr = None
        for i in range(piv_row, len(rows)):
            if rows[i][col] != 0:
                pr = i
                break
        if pr is None:
            continue
        rows[piv_row], rows[pr] = rows[pr], rows[piv_row]
        pv = rows[piv_row][col]
        for i in range(len(rows)):
            if i != piv_row and rows[i][col] != 0:
                fac = rows[i][col] / pv
                rows[i] = [a - fac * b for a, b in zip(rows[i], rows[piv_row])]
        piv_row += 1
    for i in range(piv_row, len(rows)):
        if rows[i][-1] != 0:
            return False
    return True


t0 = time.time()
K = 54
T = U_fast_table(K, 5)
found = []
tested = 0
for m in range(1, 5):
    seq = [T[k][m] for k in range(K + 1)]
    for k0 in (0, 6, 12):
        for c in range(-6, 7):
            for e in range(-6, 8):
                tested += 1
                if solvable(seq, c, e, k0, K):
                    found.append((m, k0, c, e))
print('single-family linear systems tested=%d (m=1..4, k0 in {0,6,12}, c in [-6,6], e=m+d in [-6,7], k<=%d); solvable:' % (tested, K), found, '%.1fs' % (time.time() - t0))
# 对照组：m=0 时 U_k(0)=1 = C(k,0) 必须可解
print('control m=0 (c=0,e=0) solvable:', solvable([1] * (K + 1), 0, 0, 0, K))
# 对照组：1/P_m 的系数本身是单族（c=m, e=m）必须可解
from polylib import series_inv
for m in range(1, 5):
    ser = series_inv(P_poly(m), K + 1)
    print('control [x^k]1/P_%d (c=%d,e=%d) solvable:' % (m, m, m), solvable([int(v) for v in ser], m, m, 0, K))
