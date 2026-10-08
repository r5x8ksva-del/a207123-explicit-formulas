# -*- coding: utf-8 -*-
"""探索（2026-10-08，B5 续）：骨架型两层和的二元母函数在纤维 2 上的留数级数。

记号：b_v = 1 - x - v x^3，K_2 = Q[x]/(b_2)，η 为 b_2 的根（1-η = 2η^3），u = x^3/(1-x)，u'(η) = (3-2η)/(4η^4)。
  E_M = x^2 sum_{j=1}^M j/(b_j...b_M)（以上升结尾），1/P_M（不以上升结尾），F^E_q = sum_M (-1)^(q-1-M) C(q,M+1) E_M。
要核对的式子（推导见 notes/14 草稿）：
  (1) sum_q u'(η) Res_η F^E_q z^q = -(W~_2(η)-1)/(8(1+z)) * y^3 e^(-y)，y = η^(-3) z/(1+z)；N^c 同样（W~_2-1 换成 1）。
  (2) 代入 z = V(1-η)/(1+ηV)、乘 1/P = η^(-(d-c+f-e)) (1-η)^(d+1) V^(e-f) (1+ηV)^(-(e+1)) 后，
      = α(η) (1+ηV)^(-e) κ(V)，α(η) = (W~_2(η)-1) η^(-(d-c+f-e)) (1-η)^(d+1)，κ(V) = -V^(3+e-f) e^(-2V/(1+V)) (1+V)^(-4)。
  (3) N^c 取 R 式的参数 (c,d,e,f) = (-1,-1,0,0) 时，代入后的每个 V 系数都是有理数（K_2 中坐标为 (a,0,0)）；N^E 的不是。
留数直接由 E_M、1/P_M 的定义在 K_2 中算（b_v(η) = (2-v)η^3，b_2'(η) = -1-6η^2），不用引理 4.1。
用法： py -3.14 code/tableB/explore/explore_b5_skeleton_residue.py [Q=14]
"""
import os
import sys
from fractions import Fraction as Fr
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from check_b4 import red, kmul, knorm  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
Q = int(sys.argv[1]) if len(sys.argv) > 1 else 14
I = 2
ZERO, ONE = [Fr(0)] * 3, [Fr(1), Fr(0), Fr(0)]
X = [Fr(0), Fr(1), Fr(0)]


def add(a, b):
    return [p + q for p, q in zip(a, b)]


def sc(c, a):
    return [Fr(c) * p for p in a]


def mul(a, b):
    return kmul(a, b, I)


def inv(a):
    # 用乘法矩阵解线性方程组
    cols = [mul(a, e) for e in (ONE, X, [Fr(0), Fr(0), Fr(1)])]
    M = [[cols[j][r] for j in range(3)] + [ONE[r]] for r in range(3)]
    for c in range(3):
        p = next(r for r in range(c, 3) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]
        M[c] = [v / pv for v in M[c]]
        for r in range(3):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [M[r][t] - f * M[c][t] for t in range(4)]
    return [M[r][3] for r in range(3)]


def xp(n):
    e = ONE
    base = X if n >= 0 else inv(X)
    for _ in range(abs(n)):
        e = mul(e, base)
    return e


eta3 = xp(3)
bv = {v: sc(2 - v, eta3) for v in range(0, Q + 3) if v != 2}       # b_v(η) = (2-v) η^3
b2p = add(sc(-1, ONE), sc(-6, xp(2)))                               # b_2'(η) = -1 - 6η^2
up = mul(add(sc(3, ONE), sc(-2, X)), inv(sc(4, xp(4))))             # u'(η) = (3-2η)/(4η^4)
Wt2m1 = red([0, 0, 0, 0, 0, 2, 0, 0, 4], I)                          # W~_2 - 1 = 2x^5 + 4x^8


def res_E(M):
    """u'(η) Res_η E_M，按定义：E_M = x^2 sum_j j/(b_j...b_M)，只有 j<=2<=M 的项含 b_2。"""
    tot = ZERO
    for j in range(1, min(2, M) + 1):
        if M < 2:
            continue
        den = b2p
        for v in range(j, M + 1):
            if v != 2:
                den = mul(den, bv[v])
        tot = add(tot, sc(j, mul(xp(2), inv(den))))
    return mul(up, tot)


def res_Pinv(M):
    """u'(η) Res_η (1/P_M)，P_M = b_0...b_M。"""
    if M < 2:
        return ZERO
    den = b2p
    for v in range(0, M + 1):
        if v != 2:
            den = mul(den, bv[v])
    return mul(up, inv(den))


def row_res(q, kind):
    tot = ZERO
    for M in range(0, q):
        r = res_E(M) if kind == 'E' else res_Pinv(M)
        tot = add(tot, sc((-1) ** (q - 1 - M) * comb(q, M + 1), r))
    return tot


# ---------- K_2 系数的形式幂级数（长度 N+1 的列表）
N = Q


def s_mul(A, B):
    C = [ZERO] * (N + 1)
    for i, a in enumerate(A):
        if a == ZERO:
            continue
        for j in range(N + 1 - i):
            if B[j] != ZERO:
                C[i + j] = add(C[i + j], mul(a, B[j]))
    return C


def s_scal(c, A):
    return [mul(c, a) for a in A]


def s_const(c):
    return [c] + [ZERO] * N


def s_exp_neg(Y):
    """exp(-Y)，Y 无常数项。"""
    assert Y[0] == ZERO
    out, term = s_const(ONE), s_const(ONE)
    for n in range(1, N + 1):
        term = s_mul(term, Y)
        out = [add(o, sc(Fr((-1) ** n, factorial(n)), t)) for o, t in zip(out, term)]
    return out


def s_compose(A, Zs):
    """A(Z(V))，Z 无常数项。"""
    assert Zs[0] == ZERO
    out, pw = s_const(ZERO), s_const(ONE)
    for k in range(N + 1):
        out = [add(o, mul(A[k], p)) for o, p in zip(out, pw)]
        pw = s_mul(pw, Zs)
    return out


def s_geom(c, n):
    """(1 + c V)^n（n 可为负），c ∈ K_2。"""
    out, pw = s_const(ZERO), s_const(ONE)
    cv = [ZERO, c] + [ZERO] * (N - 1)
    for k in range(N + 1):
        cf = Fr(1)
        for t in range(k):
            cf *= Fr(n - t, t + 1)
        out = [add(o, sc(cf, p)) for o, p in zip(out, pw)]
        pw = s_mul(pw, cv)
    return out


def is_rational(a):
    return a[1] == 0 and a[2] == 0


# (1) 留数级数
w = [ZERO] + [sc((-1) ** (n - 1), ONE) for n in range(1, N + 1)]       # z/(1+z)
inv1z = [sc((-1) ** n, ONE) for n in range(N + 1)]                      # 1/(1+z)
y = s_scal(xp(-3), w)
y3e = s_mul(s_mul(s_mul(y, y), y), s_exp_neg(y))
for kind, lead in (('E', Wt2m1), ('c', ONE)):
    pred = s_scal(sc(Fr(-1, 8), lead), s_mul(inv1z, y3e))
    act = [row_res(q, kind) for q in range(N + 1)]
    print('(1) %s：留数级数与闭式一致（q<=%d）：%s' % (kind, N, act == pred))

# (2)(3) 代入与 1/P
eta = X
zV = s_mul([ZERO, add(ONE, sc(-1, eta))] + [ZERO] * (N - 1), s_geom(eta, -1))   # V(1-η)/(1+ηV)
V = [ZERO, ONE] + [ZERO] * (N - 1)
twoV = s_mul(s_scal(sc(2, ONE), V), [sc((-1) ** n, ONE) for n in range(N + 1)])   # 2V/(1+V)
kap_core = s_mul(s_exp_neg(twoV), [sc(Fr((-1) ** n * comb(n + 3, 3)), ONE) for n in range(N + 1)])  # e^{-2V/(1+V)}(1+V)^{-4}
for kind, lead, params in (('E', Wt2m1, (0, 0, 0, 0)), ('E', Wt2m1, (-1, -1, 0, 0)), ('E', Wt2m1, (2, -1, 1, 3)),
                           ('c', ONE, (-1, -1, 0, 0)), ('c', ONE, (0, 0, 0, 0))):
    c, d, e, f = params
    S = [row_res(q, kind) for q in range(N + 1)]
    comp = s_compose(S, zV)                                                  # 关于 V
    # 1/P 的 V 无关部分：η^(-(d-c+f-e)) (1-η)^(d+1)
    one_m = add(ONE, sc(-1, eta))
    pw = ONE
    for _ in range(abs(d + 1)):
        pw = mul(pw, one_m if d + 1 > 0 else inv(one_m))
    a0 = mul(xp(-(d - c + f - e)), pw)
    lhs = s_mul(s_scal(a0, comp), s_geom(eta, -(e + 1)))                     # 还差 V^(e-f)
    alpha = mul(lead, a0)
    rhs = s_scal(sc(-1, alpha), s_mul(s_geom(eta, -e), s_mul([ZERO] * 3 + [ONE] + [ZERO] * (N - 3), kap_core)))  # 还差 V^(e-f)
    same = lhs == rhs
    rat = [is_rational(t) for t in lhs]
    print('(2) %s (c,d,e,f)=%s：代入后与 α(1+ηV)^(-e)κ 一致（V^<=%d）：%s；每个 V 系数为有理数：%s；N(α)=%s'
          % (kind, params, N, same, all(rat), knorm(alpha, I)))
