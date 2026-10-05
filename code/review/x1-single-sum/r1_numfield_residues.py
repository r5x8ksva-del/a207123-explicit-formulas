# -*- coding: utf-8 -*-
"""x1-single-sum 复核脚本 r1：独立重算「单和不可能」证明里用到的全部数域事实。

完全自写（不导入 core / polylib / c2a / c2b 的任何代码）：
  (0) 自写 DP（只用三元组条件）算 U_k(m)、E(k,m)（以上升结尾的个数），
      并验证 P_m*G_m、P_m*E_m 是多项式，且分别等于 W_m、W_m-1（W_m=1+x^2 sum_j j P_{j-1}）。
  (1) 三次域 K_i = Q[x]/(i x^3 + x - 1)：自写乘法 / 求逆 / 范数（乘法矩阵行列式）。
  (2) 对 i<=m<=MMAX：在 K_i 中直接计算留数元 theta = W_m * u' / P_m'（U）与 (W_m-1) * u' / P_m'（E），
      其中 u = x^3/(1-x)，u' = x^2(3-2x)/(1-x)^2。验证闭式
         theta_U = -W~_i(x) x^{-3m-3} / (i^2 i! (-1)^{m-i} (m-i)!)，W~_i := 1 + sum_{j=1}^i j i^(j) x^{3j+2}
         theta_E = -(W~_i(x)-1) x^{-3m-3} / (i^2 i! (-1)^{m-i} (m-i)!)
      （对比 c2a §6.3 的 theta_v 公式；c2b 的 nu_i = -i * theta）。
  (3) 定理 S：i=1 时 theta_U * x^{3m+2} / (1+x) 是有理数 (-1)^m/(m-1)!；N(1+x)=3, N(x)=1。
  (4) 统一证明（对所有 m）：U 用纤维 i=1（范数含 3^1）；E 用纤维 i=2（范数含 17^1），
      并检查 c2b 证书表中的若干精确范数值。
  (5) 浮点交叉检查：用 b_1 的三个复根直接算 G_m 的留数，验证 rho_j u'(xi_j) xi_j^{3m+2}/(1+xi_j) 三者相等。
"""
import sys
import time
import cmath
from fractions import Fraction as F
from math import factorial, comb

T0 = time.time()
OUT = []


def log(s):
    print(s)
    OUT.append(s)


FAILS = []


def check(name, ok, desc):
    log(('PASS ' if ok else 'FAIL ') + name + ' ' + desc)
    if not ok:
        FAILS.append(name)


# ---------------------------------------------------------------- 多项式（升幂系数表）
def ptrim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def pmul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return ptrim(r)


def padd(a, b):
    n = max(len(a), len(b))
    return ptrim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def pscal(a, c):
    return ptrim([c * x for x in a])


def pder(a):
    return ptrim([i * a[i] for i in range(1, len(a))])


def bpoly(v):
    return [1, -1, 0, -v]


def Ppoly(m):
    p = [1]
    for v in range(m + 1):
        p = pmul(p, bpoly(v))
    return p


def Wpoly(m):
    W = [1]
    for j in range(1, m + 1):
        W = padd(W, [0, 0] + pscal(Ppoly(j - 1), j))
    return W


# ---------------------------------------------------------------- (0) 自写 DP
def dp_counts(m, K):
    """返回 (U, E)：U[k] = 合法序列数，E[k] = 以上升结尾（h_{k-1}<h_k）的合法序列数，k=0..K。"""
    n = m + 1
    U = [1, n]
    E = [0, 0]
    if K <= 1:
        return U[:K + 1], E[:K + 1]
    cnt = {(a, b): 1 for a in range(n) for b in range(n)}
    U.append(n * n)
    E.append(sum(1 for a in range(n) for b in range(n) if a < b))
    for k in range(3, K + 1):
        new = {}
        for (a, b), val in cnt.items():
            for c in range(n):
                if b == c or (a >= b and a >= c):
                    new[(b, c)] = new.get((b, c), 0) + val
        cnt = new
        U.append(sum(cnt.values()))
        E.append(sum(v for (b, c), v in cnt.items() if b < c))
    return U, E


ok0 = True
for m in range(0, 9):
    K = 3 * m + 25
    U, E = dp_counts(m, K)
    P = Ppoly(m)
    prodU = [sum(P[i] * U[k - i] for i in range(len(P)) if 0 <= k - i <= K) for k in range(K + 1)]
    prodE = [sum(P[i] * E[k - i] for i in range(len(P)) if 0 <= k - i <= K) for k in range(K + 1)]
    W = Wpoly(m)
    # 次数 <= 3m（W_m 的次数），检查到 K（K 远大于 deg P + deg W）
    okm = ptrim(prodU) == W and ptrim(prodE) == padd(W, [-1])
    ok0 = ok0 and okm
check('r1.dp_numerators', ok0,
      'own triple-condition DP: P_m*G_m == W_m and P_m*E_m == W_m - 1 as polynomials (coefficients checked up to k=3m+25), m<=8')


# ---------------------------------------------------------------- (1) 三次域 K_i
class Cubic:
    """K_i = Q[x]/(i x^3 + x - 1)，元素为 [c0,c1,c2]。"""

    def __init__(self, i):
        self.i = F(i)

    def red(self, p):
        p = [F(c) for c in p]
        # x^3 = (1 - x)/i
        for d in range(len(p) - 1, 2, -1):
            c = p[d]
            if c:
                p[d] = F(0)
                p[d - 3] += c / self.i
                p[d - 2] -= c / self.i
        p = p[:3]
        return p + [F(0)] * (3 - len(p))

    def mul(self, a, b):
        return self.red(pmul(list(a), list(b)) or [0])

    def mat(self, a):
        cols = [a, self.mul(a, [0, 1, 0]), self.mul(a, [0, 0, 1])]
        return [[cols[c][r] for c in range(3)] for r in range(3)]

    def norm(self, a):
        M = self.mat(a)
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
                - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))

    def inv(self, a):
        # 解 M y = e0（高斯消元）
        M = self.mat(a)
        A = [row[:] + [F(1) if r == 0 else F(0)] for r, row in enumerate(M)]
        for col in range(3):
            piv = next(r for r in range(col, 3) if A[r][col] != 0)
            A[col], A[piv] = A[piv], A[col]
            pv = A[col][col]
            A[col] = [v / pv for v in A[col]]
            for r in range(3):
                if r != col and A[r][col] != 0:
                    f = A[r][col]
                    A[r] = [x - f * y for x, y in zip(A[r], A[col])]
        return [A[r][3] for r in range(3)]

    def pw(self, n):
        base = [F(0), F(1), F(0)] if n >= 0 else self.inv([F(0), F(1), F(0)])
        r = [F(1), F(0), F(0)]
        for _ in range(abs(n)):
            r = self.mul(r, base)
        return r


def is_field(i):
    # i x^3 + x - 1 有有理根 <=> 根为 1/q 且 i = q^2 (q-1)
    for q in range(1, 200):
        if q * q * (q - 1) == i:
            return False
    return True


def Wtilde(i):
    """W~_i(x) = 1 + sum_{j=1}^i j * i^(j) * x^{3j+2}（多项式）。"""
    W = [1]
    ff = 1
    for j in range(1, i + 1):
        ff *= (i - j + 1)
        term = [0] * (3 * j + 2) + [j * ff]
        W = padd(W, term)
    return W


def vp(n, p):
    n = abs(n)
    if n == 0:
        return None
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def vpQ(q, p):
    return vp(q.numerator, p) - vp(q.denominator, p)


# ---------------------------------------------------------------- (2) 留数元闭式
MMAX = 34
ok2U = ok2E = True
theta_cache = {}
for i in range(1, MMAX + 1):
    if not is_field(i):
        continue
    Ki = Cubic(i)
    up = Ki.mul(Ki.red([0, 0, 3, -2]), Ki.inv(Ki.red([1, -2, 1])))   # u' = x^2(3-2x)/(1-x)^2
    Wt = Ki.red(Wtilde(i))
    Wt1 = Ki.red(padd(Wtilde(i), [-1]))
    for m in range(i, MMAX + 1):
        P = Ppoly(m)
        Pd = Ki.red(pder(P))
        W = Wpoly(m)
        thU = Ki.mul(Ki.mul(Ki.red(W), up), Ki.inv(Pd))
        thE = Ki.mul(Ki.mul(Ki.red(padd(W, [-1])), up), Ki.inv(Pd))
        theta_cache[(i, m)] = (thU, thE)
        const = F(-1, i * i * factorial(i) * (-1) ** (m - i) * factorial(m - i))
        x3m3 = Ki.pw(-3 * m - 3)
        predU = [const * c for c in Ki.mul(Wt, x3m3)]
        predE = [const * c for c in Ki.mul(Wt1, x3m3)]
        ok2U = ok2U and thU == predU
        ok2E = ok2E and thE == predE
check('r1.theta_closed_form_U', ok2U,
      'in K_i (field), W_m u\'/P_m\' == -W~_i x^{-3m-3}/(i^2 i!(-1)^{m-i}(m-i)!) exactly, all field i<=m<=%d (c2a sec.6.3 formula; m-independent up to x^{-3m-3} and a rational)' % MMAX)
check('r1.theta_closed_form_E', ok2E,
      'in K_i (field), (W_m-1) u\'/P_m\' == -(W~_i-1) x^{-3m-3}/(i^2 i!(-1)^{m-i}(m-i)!) exactly, all field i<=m<=%d' % MMAX)

# ---------------------------------------------------------------- (3) 定理 S 的事实
K1 = Cubic(1)
ok3 = K1.norm([F(0), F(1), F(0)]) == 1 and K1.norm([F(1), F(1), F(0)]) == 3
ok3 = ok3 and K1.red(Wtilde(1)) == K1.mul([0, 1, 0], [1, 1, 0])     # W~_1 = 1+x^5 = x(1+x)
for m in range(1, MMAX + 1):
    thU, _ = theta_cache[(1, m)]
    val = K1.mul(K1.mul(thU, K1.pw(3 * m + 2)), K1.inv([F(1), F(1), F(0)]))
    ok3 = ok3 and val == [F((-1) ** m, factorial(m - 1)), F(0), F(0)]
check('r1.thmS_facts', ok3,
      'K_1: N(x)=1, N(1+x)=3, W~_1 = x(1+x); theta_U(i=1) * x^{3m+2}/(1+x) == (-1)^m/(m-1)! for m=1..%d (Theorem S step (3))' % MMAX)

# ---------------------------------------------------------------- (4) 统一证明 + c2b 证书值
okU = okE = True
rowsU = []
rowsE = []
for m in range(1, MMAX + 1):
    thU, thE = theta_cache[(1, m)]
    nU = K1.norm(thU)
    e3 = vpQ(nU, 3)
    okU = okU and (e3 % 3 != 0)
    if m <= 6:
        rowsU.append('m=%d N(theta_U,i=1)=%s v3=%d' % (m, nU, e3))
K2 = Cubic(2)
for m in range(2, MMAX + 1):
    thU, thE = theta_cache[(2, m)]
    nE = K2.norm(thE)
    e17 = vpQ(nE, 17)
    okE = okE and (e17 % 3 != 0)
    if m <= 6:
        rowsE.append('m=%d N(theta_E,i=2)=%s v17=%d' % (m, nE, e17))
for r in rowsU + rowsE:
    log('    ' + r)
check('r1.uniform_U_fiber1', okU,
      'for every m=1..%d the fiber u=1 obstruction holds: v_3(N(theta_U)) not = 0 mod 3 (prime 3 does not divide i=1); with the closed form this is m-independent => U single u-sum impossible for ALL m>=1' % MMAX)
check('r1.uniform_E_fiber2', okE,
      'for every m=2..%d the fiber u=1/2 obstruction holds: v_17(N(theta_E)) not = 0 mod 3; closed form => E single u-sum impossible for ALL m>=2' % MMAX)

# E 的另一条初等证明：纤维 1 迫使 x^{N-3m-3} * x^5 in Q => N = 3m-2；纤维 2 则要求 2+4x^3 in Q，不成立
okalt = True
# K_1 中 x^n in Q <=> n = 0（检查 |n|<=60 的坐标）
for n in range(-60, 61):
    c = K1.pw(n)
    isq = c[1] == 0 and c[2] == 0
    okalt = okalt and (isq == (n == 0))
v = K2.red([2, 0, 0, 4])          # 2 + 4 x^3
okalt = okalt and not (v[1] == 0 and v[2] == 0)
check('r1.E_alt_proof', okalt,
      'K_1: x^n in Q iff n=0 (|n|<=60; in general by |xi_1|!=|xi_2|); K_2: 2+4x^3 = 4-2x not in Q  => fibers 1,2 jointly exclude E single u-sum for every m>=2')

# c2b 证书表中的若干精确范数（c2b 的 nu_i = -i*theta，所以 N(nu) = -i^3 N(theta)）
c2b_table = {('E', 2, 2): F(17), ('U', 2, 2): F(103, 2), ('E', 3, 3): F(2363, 8), ('U', 3, 3): F(21619, 24),
             ('E', 4, 3): F(-63801, 8), ('U', 4, 3): F(-194571, 8), ('U', 1, 1): F(3),
             ('E', 5, 5): F(1320570541, 13824), ('U', 5, 5): F(20305015931, 69120),
             ('E', 6, 6): F(5271706601, 3000), ('U', 6, 6): F(97540993603, 18000)}
okc = True
for (wh, m, i), val in c2b_table.items():
    thU, thE = theta_cache[(i, m)]
    th = thU if wh == 'U' else thE
    mine = -F(i) ** 3 * Cubic(i).norm(th)
    if mine != val:
        okc = False
        log('    mismatch %s m=%d i=%d: mine %s vs c2b %s' % (wh, m, i, mine, val))
check('r1.c2b_cert_values', okc,
      'independently recomputed norms N(nu_i) (nu_i = -i*theta) equal the c2b certificate table entries for m<=6 (11 entries)')

# ---------------------------------------------------------------- (5) 浮点交叉检查（b_1 的三个复根）
def roots_cubic(i):
    # i x^3 + x - 1 = 0，Durand-Kerner
    coeffs = [1.0, 0.0, 1.0 / i, -1.0 / i]      # x^3 + 0 x^2 + x/i - 1/i
    rts = [complex(0.4, 0.9) ** k for k in range(3)]
    for _ in range(500):
        new = []
        for a in range(3):
            num = rts[a] ** 3 + coeffs[2] * rts[a] + coeffs[3]
            den = 1
            for b in range(3):
                if b != a:
                    den *= (rts[a] - rts[b])
            new.append(rts[a] - num / den)
        rts = new
    return rts


def peval(p, z):
    r = 0
    for c in reversed(p):
        r = r * z + c
    return r


okf = True
xis = roots_cubic(1)
for m in (1, 2, 5, 9):
    W = Wpoly(m)
    Pd = pder(Ppoly(m))
    vals = []
    for z in xis:
        rho = peval(W, z) / peval(Pd, z)
        upz = z * z * (3 - 2 * z) / (1 - z) ** 2
        vals.append(rho * upz * z ** (3 * m + 2) / (1 + z))
    target = (-1) ** m / factorial(m - 1)
    okf = okf and all(abs(v - target) < 1e-9 * max(1, abs(target)) for v in vals)
moduli = sorted(abs(z) for z in xis)
okf = okf and abs(moduli[0] - 0.6823278) < 1e-6 and abs(moduli[1] - moduli[0] ** -0.5) < 1e-9
check('r1.float_residues', okf,
      'floating point (tol 1e-9): at the three complex roots xi_j of b_1, rho_j u\'(xi_j) xi_j^{3m+2}/(1+xi_j) == (-1)^m/(m-1)! for m in {1,2,5,9}; |xi_1|=0.68233, |xi_2|=|xi_1|^{-1/2}')

log('# elapsed %.1fs' % (time.time() - T0))
log('SUMMARY r1 fail=%d' % len(FAILS))
sys.exit(1 if FAILS else 0)
