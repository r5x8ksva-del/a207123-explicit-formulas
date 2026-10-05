# -*- coding: utf-8 -*-
"""s2：c_m 的各种闭式是否等价；c_4、c_18 的精确值（多条独立路线）；Q(rho) 表示。

记号：f_m(y)=y^3-y^2-m，商环 A_m = Q[y]/(f_m)，元素用三元组 (a0,a1,a2) 表示。
c5a 闭式   X_m(y) = y (y^{3m+1}/m! - e_{m-1}(y^3)) / (3y-2)
主 Agent   Y_m(y) = [y^{3m+3}/m! + sum_{j=1}^m j y^{3m+1-3j}/(m-j)!] / (y^2+3m)
            （= rho^{3m+3}/(m!(rho^2+3m)) * (1 + sum_j j m!/(m-j)! rho^{-3j-2}) 乘开）
残数式     Z_m = (G_{m-1}(x)+m x^2)/(x(1+3m x^2)), x=1/rho, G_{m-1}=W_{m-1}/P_{m-1}
"""
import sys, os, time
from fractions import Fraction as Fr
from math import factorial
from decimal import Decimal, getcontext
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rlib import U_dp, pmul, padd, peval, pscale

getcontext().prec = 110
t0 = time.time()


def ymod(m, n):
    """y^n mod f_m 作为三元组。"""
    v = (Fr(1), Fr(0), Fr(0))
    for _ in range(n):
        a0, a1, a2 = v
        v = (m * a2, a0, a1 + a2)          # y^3 = y^2 + m
    return v


def elem_from_poly(m, d):
    """d: {exponent: coeff} -> A_m 元素"""
    out = [Fr(0)] * 3
    for e, c in d.items():
        v = ymod(m, e)
        for t in range(3):
            out[t] += c * v[t]
    return tuple(out)


def emul(m, u, v):
    # (u0+u1 y+u2 y^2)(v0+v1 y+v2 y^2) mod f_m
    prod = [Fr(0)] * 5
    for i in range(3):
        for j in range(3):
            prod[i + j] += u[i] * v[j]
    out = [Fr(0)] * 3
    for e, c in enumerate(prod):
        if c:
            w = ymod(m, e)
            for t in range(3):
                out[t] += c * w[t]
    return tuple(out)


def solve3(A, b):
    M = [list(A[i]) + [b[i]] for i in range(3)]
    for c in range(3):
        p = next(r for r in range(c, 3) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        for r in range(3):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return tuple(M[i][3] / M[i][i] for i in range(3))


def ediv(m, u, v):
    """u / v in A_m（v 可逆时）。解 x*v = u。"""
    cols = []
    for basis in ((Fr(1), Fr(0), Fr(0)), (Fr(0), Fr(1), Fr(0)), (Fr(0), Fr(0), Fr(1))):
        cols.append(emul(m, basis, v))
    A = [[cols[c][r] for c in range(3)] for r in range(3)]
    return solve3(A, u)


def X_elem(m):
    num = {3 * m + 2: Fr(1, factorial(m))}
    for i in range(m):
        num[3 * i + 1] = num.get(3 * i + 1, Fr(0)) - Fr(1, factorial(i))
    return ediv(m, elem_from_poly(m, num), elem_from_poly(m, {1: Fr(3), 0: Fr(-2)}))


def Y_elem(m):
    num = {3 * m + 3: Fr(1, factorial(m))}
    for j in range(1, m + 1):
        e = 3 * m + 1 - 3 * j
        num[e] = num.get(e, Fr(0)) + Fr(j, factorial(m - j))
    return ediv(m, elem_from_poly(m, num), elem_from_poly(m, {2: Fr(1), 0: Fr(3 * m)}))


# (a) 商环中精确等价（对 f_m 的三个根同时成立）
ok_eq = all(X_elem(m) == Y_elem(m) for m in range(1, 61))
print('(a) c5a closed form == main-agent closed form in Q[y]/(y^3-y^2-m), exact, 1<=m<=60:', ok_eq)


# (b) Q(rho) 表示与笔记中的列表比较
claimed = {
    1: (Fr(10, 31), Fr(15, 31), Fr(17, 31)),
    2: (Fr(46, 29), Fr(40, 29), Fr(79, 58)),
    3: (Fr(1147, 170), Fr(743, 170), Fr(1034, 255)),
    4: (Fr(2251, 84), Fr(2455, 168), Fr(1081, 84)),
    5: (Fr(342419, 3336), Fr(55909, 1112), Fr(233333, 5560)),
    6: (Fr(3831899, 9960), Fr(1747373, 9960), Fr(8282789, 59760)),
    7: (Fr(39498919, 27792), Fr(21386117, 34740), Fr(49785759, 108080)),
    8: (Fr(1439720167, 277200), Fr(599267623, 277200), Fr(486531209, 316800)),
}
ok_repr = all(X_elem(m) == claimed[m] for m in claimed)
print('(b) representations c_1..c_8 in Q(rho) match notes table:', ok_repr)


def rho_dec(m):
    if m == 0:
        return Decimal(1)
    y = Decimal(m) ** (Decimal(1) / 3) + Decimal('0.4')
    for _ in range(500):
        y2 = y - (y * y * y - y * y - m) / (3 * y * y - 2 * y)
        if abs(y2 - y) < Decimal(10) ** -105:
            return y2
        y = y2
    return y


def P_poly(m):
    p = [Fr(1)]
    for i in range(m + 1):
        p = pmul(p, [Fr(1), Fr(-1), Fr(0), Fr(-i)])
    return p


def W_poly(m):
    W = [Fr(1)]
    for j in range(1, m + 1):
        W = padd(W, pscale([Fr(0), Fr(0)] + P_poly(j - 1), j))
    return W


def resid_exact(m, x):
    """Z_m = (G_{m-1}(x)+m x^2)/(x(1+3m x^2))，G_{m-1}=W_{m-1}/P_{m-1}，x 为有理数（rho 为整数时）。"""
    G = peval(W_poly(m - 1), x) / peval(P_poly(m - 1), x)
    return (G + m * x * x) / (x * (1 + 3 * m * x * x))


def closed_c5a(m, r):
    e = sum(Fr(r) ** (3 * i) / factorial(i) for i in range(m))
    return Fr(r) * (Fr(r) ** (3 * m + 1) / factorial(m) - e) / (3 * r - 2)


def closed_main(m, r):
    s = 1 + sum(Fr(j * factorial(m), factorial(m - j)) * Fr(r) ** (-3 * j - 2) for j in range(1, m + 1))
    return Fr(r) ** (3 * m + 3) / (factorial(m) * (r * r + 3 * m)) * s


C18_claim = Fr(37105325714711350249401, 6830759936000)
for (m, r, claim) in ((4, 2, Fr(215, 2)), (18, 3, C18_claim), (48, 4, None), (100, 5, None)):
    a = closed_c5a(m, r)
    b = closed_main(m, r)
    c = resid_exact(m, Fr(1, r))
    print('(c) m=%d rho=%d: c5a-form == main-form == residue-form: %s ; matches claim: %s ; value=%s'
          % (m, r, a == b == c, (a == claim) if claim is not None else 'n/a',
             (str(a) if m <= 18 else '%.12e' % (a.numerator / a.denominator))))

# (d) 直接从 DP 数据（不经任何公式）数值逼近 c_4、c_18：U_k(m)/rho^k + c_{m-1} rho_{m-1}^{k+3}/rho^k
def c_dec(m):
    r = rho_dec(m)
    if m == 0:
        return Decimal(1)
    e = sum(r ** (3 * i) / factorial(i) for i in range(m))
    return r * (r ** (3 * m + 1) / factorial(m) - e) / (3 * r - 2)


for (m, r, claim, K) in ((4, 2, Fr(215, 2), 1200), (18, 3, C18_claim, 3200)):
    U = U_dp(m, K)[K]
    est0 = Decimal(U) / Decimal(r) ** K
    corr = c_dec(m - 1) * rho_dec(m - 1) ** (K + 3) / Decimal(r) ** K
    est = est0 + corr
    cl = Decimal(claim.numerator) / Decimal(claim.denominator)
    print('(d) m=%d K=%d: U_K/rho^K = %.25e ; with 2nd-pole correction = %.30e ; claim = %.30e ; rel.diff = %.3e'
          % (m, K, est0, est, cl, abs(est - cl) / cl))

# (e) c_m 数值表（m<=8）与笔记 §2.4 表对照（笔记给 30 位）
table = {1: '2.20960813177848081994505234781', 2: '7.84111922937324985940091456827',
         3: '28.9768573169912284737836260899', 5: '397.012371323434322828387413169',
         6: '1456.31682906564593591796901793', 7: '5303.63000356539763596043480665',
         8: '19179.3074772177997083232848565'}
rtab = {1: '1.46557123187676802665673122522', 2: '1.69562076955986205741636710012',
        3: '1.86370652781918909324146791527', 5: '2.11634329862421165983836641876',
        6: '2.21877658530166566312987374149', 7: '2.31085216345886473444017266116',
        8: '2.39485867386606594311860057559'}
ok_tab = True
for m in table:
    c = c_dec(m)
    r = rho_dec(m)
    if abs(c - Decimal(table[m])) > Decimal('1e-26') * c or abs(r - Decimal(rtab[m])) > Decimal('1e-28'):
        ok_tab = False
        print('   table mismatch m=%d: c=%s rho=%s' % (m, c, r))
print('(e) notes table of rho_m, c_m (m<=8, ~30 digits) reproduced:', ok_tab)

# (f) c_m > 0 与 Z_m 形式数值一致（m<=40），用 decimal 计算 G_{m-1}(x_m) 级数之外的有理函数值
ok_pos = True
for m in range(1, 41):
    r = rho_dec(m)
    x = 1 / r
    W = W_poly(m - 1)
    P = P_poly(m - 1)
    Wd = sum(Decimal(c.numerator) / Decimal(c.denominator) * x ** i for i, c in enumerate(W))
    Pd = sum(Decimal(c.numerator) / Decimal(c.denominator) * x ** i for i, c in enumerate(P))
    Z = (Wd / Pd + m * x * x) / (x * (1 + 3 * m * x * x))
    c = c_dec(m)
    if not (c > 0 and abs(Z - c) < Decimal('1e-80') * c):
        ok_pos = False
        print('   Z mismatch m=%d' % m)
print('(f) residue form (G_{m-1}(x_m)+m x_m^2)/(x_m(1+3m x_m^2)) == closed form, and c_m>0, 1<=m<=40 (decimal 110):', ok_pos)
print('elapsed %.1fs' % (time.time() - t0))
