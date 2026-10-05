# -*- coding: utf-8 -*-
"""r-c2a 复核脚本 4：否定命题（定理 S / 命题 S' / 两族）的基本独立核对 + 对「未完成：α+β 奇数形状」的补充。
  (1) 定理 S 的代数事实：N(ξ)=1, N(1+ξ)=3（用数值根之积 + 整系数结式两种方式）；
      留数式 ρ_i u'(ξ_i) = (-1)^m (1+ξ_i) ξ_i^{-3m-2}/(m-1)!（复数浮点，明确标注容差）。
  (2) 两族：在 Z[ξ]（纤维 1：ξ^3=1-ξ，ξ^{-1}=1+ξ^2）与 Q(ξ)（纤维 2）中用整数/分数精确重算
      纤维 1 条件的解集（扩到 |a|,|b|<=500），并检验与纤维 2 无公共解；确认 m=1 的 F3 对应 (a,b)=(-1,3)。
  (3) 形状 (α,β) 的「纤维点」检验（浮点，标注容差）：v=x^{α+β}/(1-x)^β，v0=v(ξ_real)；
      若纤维 {v=v0} 中有点 η（v'(η)≠0, η∉{0,1}）使 w=(1-η)/η^3 不是正整数，则该形状对所有 m>=1 都不存在单和。
  (4) (1,2)、(2,3) 形状的线性方程组佐证（Fraction 精确消元，对照 DP 自写），含对照组。
"""
import time
import cmath
from fractions import Fraction as Fr
from math import comb, factorial
import numpy as np

T0 = time.time()
RES = []


def rep(tag, ok, msg):
    RES.append(bool(ok))
    print(('PASS ' if ok else 'FAIL ') + tag + ' ' + msg, flush=True)


def C(a, b):
    if b < 0 or a < 0 or b > a:
        return 0
    return comb(a, b)


# ---------------------------------------------------------------- (1) 定理 S 的事实
roots = np.roots([-1, 0, -1, 1])          # b_1 = 1 - x - x^3  (系数按降幂: -x^3 + 0 x^2 - x + 1)
prod_xi = np.prod(roots)
prod_1pxi = np.prod(1 + roots)
okN = abs(prod_xi - 1) < 1e-12 and abs(prod_1pxi - 3) < 1e-12
# 整数结式方式：N(1+ξ) = (-1)^3 f(-1) with f = x^3+x-1
f = lambda x: x ** 3 + x - 1
okN = okN and (-f(0) == 1) and (-f(-1) == 3)
rep('S_norms', okN, 'N(xi)=1, N(1+xi)=3 for b_1 roots (numeric product, tol 1e-12; and -f(0), -f(-1))')


def Pm_val(m, x):
    p = 1
    for v in range(m + 1):
        p *= (1 - x - v * x ** 3)
    return p


def Pm_der(m, x):
    s = 0
    for i in range(m + 1):
        t = (-1 - 3 * i * x ** 2)
        for v in range(m + 1):
            if v != i:
                t *= (1 - x - v * x ** 3)
        s += t
    return s


def Wm_val(m, x):
    w = 1
    for j in range(1, m + 1):
        w += j * x ** 2 * Pm_val(j - 1, x)
    return w


ok = True
maxrel = 0
for m in range(1, 6):
    for xi in roots:
        rho = Wm_val(m, xi) / Pm_der(m, xi)
        up = -(-1 - 3 * xi ** 2) / (1 - xi)     # u' = -b_1'(xi)/(1-xi)
        lhs = rho * up
        rhs = (-1) ** m * (1 + xi) * xi ** (-3 * m - 2) / factorial(m - 1)
        rel = abs(lhs - rhs) / abs(rhs)
        maxrel = max(maxrel, rel)
        ok = ok and rel < 1e-8
rep('S_residue_numeric', ok, 'rho_i u\'(xi_i) == (-1)^m (1+xi_i) xi_i^(-3m-2)/(m-1)! for all 3 roots, m=1..5 (complex float, max rel err %.1e < 1e-8; float error grows with m, exact check below)' % maxrel)
# 共轭不全相等（任意 M）：θ^3 = 3 不可能有理，这里只做 |M|<=60 的数值演示
ok = True
for M in range(-60, 61):
    th = [(1 + z) * z ** (-M) for z in roots]
    ok = ok and max(abs(th[0] - th[1]), abs(th[0] - th[2])) > 1e-6
rep('S_theta_conj_distinct', ok, 'theta=(1+xi)xi^(-M) has non-equal conjugates for |M|<=60 (numeric demo only)')


# ---------------------------------------------------------------- (2) 两族：精确重算
class Field:
    """Q(ξ)，ξ 为 b_v = 1 - x - v x^3 的根：ξ^3 = (1-ξ)/v。元素为分数三元组。"""
    def __init__(self, v):
        self.v = v

    def mul(self, a, b):
        r = [Fr(0)] * 5
        for i in range(3):
            if a[i]:
                for j in range(3):
                    r[i + j] += a[i] * b[j]
        # 降次：ξ^4 = ξ*ξ^3 = (ξ - ξ^2)/v ; ξ^3 = (1 - ξ)/v
        v = self.v
        c4 = r[4]
        r[1] += c4 / v
        r[2] -= c4 / v
        c3 = r[3]
        r[0] += c3 / v
        r[1] -= c3 / v
        return [r[0], r[1], r[2]]

    def inv(self, a):
        """用乘法矩阵的伴随阵求逆（精确）。"""
        e = [[Fr(1), Fr(0), Fr(0)], [Fr(0), Fr(1), Fr(0)], [Fr(0), Fr(0), Fr(1)]]
        cols = [self.mul([Fr(x) for x in a], ei) for ei in e]          # 第 j 列 = a * xi^j
        M = [[cols[j][i] for j in range(3)] for i in range(3)]
        # 解 M y = (1,0,0)
        aug = [row[:] + [Fr(1) if i == 0 else Fr(0)] for i, row in enumerate(M)]
        for col in range(3):
            p = next(i for i in range(col, 3) if aug[i][col] != 0)
            aug[col], aug[p] = aug[p], aug[col]
            pv = aug[col][col]
            aug[col] = [x / pv for x in aug[col]]
            for i in range(3):
                if i != col and aug[i][col] != 0:
                    fac = aug[i][col]
                    aug[i] = [x - fac * y for x, y in zip(aug[i], aug[col])]
        return [aug[i][3] for i in range(3)]


def det3(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def powers(Fd, A, xinv):
    xi = [Fr(0), Fr(1), Fr(0)]
    pw = {0: [Fr(1), Fr(0), Fr(0)]}
    for g in range(1, A + 1):
        pw[g] = Fd.mul(pw[g - 1], xi)
        pw[-g] = Fd.mul(pw[-g + 1], xinv)
    return pw


def poly_to_field(Fd, coeffs):
    acc = [Fr(0)] * 3
    xp = [Fr(1), Fr(0), Fr(0)]
    xi = [Fr(0), Fr(1), Fr(0)]
    for cf in coeffs:
        acc = [acc[i] + cf * xp[i] for i in range(3)]
        xp = Fd.mul(xp, xi)
    return acc


A = 500
t0 = time.time()
F1 = Field(1)
F2 = Field(2)
# ξ^{-1}：纤维 1：ξ(ξ^2+1)=1 ⇒ ξ^{-1} = 1 + ξ^2；纤维 2：ξ(2ξ^2+1)=1 ⇒ ξ^{-1} = 1 + 2ξ^2
x1inv = [Fr(1), Fr(0), Fr(1)]
x2inv = [Fr(1), Fr(0), Fr(2)]
assert F1.mul(x1inv, [0, 1, 0]) == [1, 0, 0] and F2.mul(x2inv, [0, 1, 0]) == [1, 0, 0]
P1 = powers(F1, A, x1inv)
P2 = powers(F2, A, x2inv)
# 纤维 1 全是整数坐标，转成 int 加速
P1i = {g: [int(c) for c in P1[g]] for g in P1}
assert all(all(c.denominator == 1 for c in P1[g]) for g in P1)
W1 = [int(c) for c in poly_to_field(F1, [1, 0, 0, 0, 0, 1])]          # 1 + x^5
W2 = poly_to_field(F2, [1, 0, 0, 0, 0, 2, 0, 0, 4])                   # 1 + 2x^5 + 4x^8
sol1 = [(a, b) for a in range(-A, A + 1) for b in range(a + 1, A + 1) if det3(W1, P1i[a], P1i[b]) == 0]
both = [(a, b) for (a, b) in sol1 if det3(W2, P2[a], P2[b]) == 0]
sol150 = [s for s in sol1 if abs(s[0]) <= 150 and abs(s[1]) <= 150]
rep('two_family_exact', len(sol150) == 14 and len(sol1) == 14 and both == [] and (-1, 3) in sol1,
    'fiber-1 solutions with |a|,|b|<=%d: %d (all within |.|<=11: %s); common with fiber 2: %s; (-1,3) (= F3 for m=1) present; %.1fs'
    % (A, len(sol1), sol1, both, time.time() - t0))


# 定理 S 留数式的精确核对（自写 Q(ξ) 运算，P_m'、W_m 直接按多项式定义在域中求值）
def fval(Fd, coeffs):
    return poly_to_field(Fd, coeffs)


def pmul_int(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


ok = True
for m in range(1, 16):
    P = [1]
    for v in range(m + 1):
        P = pmul_int(P, [1, -1, 0, -v])
    dP = [i * P[i] for i in range(1, len(P))]
    W = [1]
    Pj = [1]
    for j in range(1, m + 1):
        if j >= 2:
            Pj = pmul_int(Pj, [1, -1, 0, -(j - 1)])
        else:
            Pj = [1, -1]
        term = [0, 0] + [j * a for a in Pj]
        W = [(W[i] if i < len(W) else 0) + (term[i] if i < len(term) else 0) for i in range(max(len(W), len(term)))]
    rho = F1.mul(fval(F1, W), F1.inv(fval(F1, dP)))
    up = F1.mul(fval(F1, [1, 0, 3]), F1.inv(fval(F1, [1, -1])))           # u' = (1+3x^2)/(1-x) at xi
    lhs = F1.mul(rho, up)
    xpow = [Fr(1), Fr(0), Fr(0)]
    for _ in range(3 * m + 2):
        xpow = F1.mul(xpow, x1inv)
    rhs = [Fr((-1) ** m, factorial(m - 1)) * c for c in F1.mul([Fr(1), Fr(1), Fr(0)], xpow)]
    ok = ok and lhs == rhs
rep('S_residue_exact', ok, 'exact in Q(xi) (own field code): W_m(xi) u\'(xi) / P_m\'(xi) == (-1)^m (1+xi) xi^(-3m-2)/(m-1)!, m=1..15')

# ---------------------------------------------------------------- (3) 形状的纤维点检验
xi_r = [z.real for z in roots if abs(z.imag) < 1e-12][0]


def fiber_test(al, be):
    """返回 (excluded?, witness)。"""
    n = al + be
    v0 = xi_r ** n / (1 - xi_r) ** be
    # x^n - v0 (1-x)^be = 0
    poly = np.zeros(n + 1, dtype=complex)
    poly[0] = 1.0                       # 降幂：x^n
    for i in range(be + 1):
        # (1-x)^be = sum_i C(be,i) (-x)^i
        poly[n - i] -= v0 * comb(be, i) * (-1) ** i
    rts = np.roots(poly)
    crit = (al + be) / al
    for eta in rts:
        if abs(eta) < 1e-9 or abs(eta - 1) < 1e-9 or abs(eta - crit) < 1e-9:
            continue
        w = (1 - eta) / eta ** 3
        if abs(w.imag) > 1e-7 or w.real < 0.5 or abs(w.real - round(w.real)) > 1e-7:
            return True, (complex(round(eta.real, 6), round(eta.imag, 6)), complex(round(w.real, 4), round(w.imag, 4)))
    return False, None


lines = []
not_excl = []
for n in range(2, 13):
    for al in range(1, n + 1):
        be = n - al
        ex, wit = fiber_test(al, be)
        if not ex:
            not_excl.append((al, be))
        if (al, be) in ((1, 2), (2, 3), (2, 1), (6, 3), (1, 4), (3, 2), (4, 1)):
            lines.append('(%d,%d): %s %s' % (al, be, 'excluded' if ex else 'NOT excluded', wit if wit else ''))
print('  shape fiber test details: ' + '; '.join(lines))
rep('odd_shapes_fiber', not_excl == [(2, 1)], 'fiber-point test (float, tol 1e-7) excludes every shape (alpha>=1, 2<=alpha+beta<=12) except %s' % not_excl)


# ---------------------------------------------------------------- (4) 线性方程组佐证
def U_col(m, K):
    out = [1, m + 1]
    n = m + 1
    cnt = [[1] * n for _ in range(n)]
    out.append(n * n)
    for _ in range(3, K + 1):
        new = [[0] * n for _ in range(n)]
        for b in range(n):
            suf = [0] * (n + 1)
            for a in range(n - 1, -1, -1):
                suf[a] = suf[a + 1] + cnt[a][b]
            for c in range(n):
                new[b][c] = suf[0] if b == c else suf[max(b, c)]
        cnt = new
        out.append(sum(map(sum, cnt)))
    return out


def solvable(seq, al, be, c, d, k0, K):
    # 未知量 A(s)，s 使 C(k+c-al*s, be*s+d) 在某个 k0<=k<=K 上可能非零
    cand = []
    for s in range(-60, 60):
        if be * s + d < 0:
            continue
        if any(C(k + c - al * s, be * s + d) for k in range(k0, K + 1)):
            cand.append(s)
    rows = [[Fr(C(k + c - al * s, be * s + d)) for s in cand] + [Fr(seq[k])] for k in range(k0, K + 1)]
    pr = 0
    for col in range(len(cand)):
        p = next((i for i in range(pr, len(rows)) if rows[i][col] != 0), None)
        if p is None:
            continue
        rows[pr], rows[p] = rows[p], rows[pr]
        pv = rows[pr][col]
        for i in range(len(rows)):
            if i != pr and rows[i][col] != 0:
                fac = rows[i][col] / pv
                rows[i] = [x - fac * y for x, y in zip(rows[i], rows[pr])]
        pr += 1
    return all(rows[i][-1] == 0 for i in range(pr, len(rows)))


K = 45
cols = {m: U_col(m, K) for m in range(0, 4)}
t0 = time.time()
for (al, be) in ((1, 2), (2, 3)):
    found = [(m, k0, c, d) for m in (1, 2, 3) for k0 in (0, 6) for c in range(-4, 5) for d in range(-4, 7)
             if solvable(cols[m], al, be, c, d, k0, K)]
    ctrl = solvable(cols[0], al, be, 0, 0, 0, K)        # U_k(0)=1 = C(k,0)：s=0 一项
    rep('linsys_shape_%d_%d' % (al, be), found == [] and ctrl,
        'U_k(m) = sum_s A(s) C(k+c-%d s, %d s+d), k0<=k<=45, m=1..3, k0 in {0,6}, c in [-4,4], d in [-4,6]: no solvable system (%d tried); control m=0 solvable (%.1fs)'
        % (al, be, 3 * 2 * 9 * 11, time.time() - t0))

print('# elapsed %.1fs' % (time.time() - T0))
print('SUMMARY r4 pass=%d fail=%d' % (sum(RES), len(RES) - sum(RES)))
