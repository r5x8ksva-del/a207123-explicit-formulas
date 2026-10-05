# -*- coding: utf-8 -*-
"""x1-single-sum 复核脚本 r4：命题 S' 未覆盖的形状（c2a-shapes-odd）能否用同一纤维论证补上。

形状 U_k(m) = sum_s A(s) C(k+c-alpha s, beta s+d)，v = x^{alpha+beta}/(1-x)^beta（alpha>=1 时 A in C(v)，与 S' 第一步相同）。
设 xi 为 b_1 的实根，v0 = v(xi)。G_m 在 xi 有单极点 => A 在 v0 有极点 => 纤维 {v=v0} 中每个 v'!=0、不在 {0,1} 的点都必须是 P_m 的根。
  (a) (1,2)：若纤维中的 eta 是 b_w 的根（w>=1），可推出 (w-1+xi)^3 = w(1-xi)；在基 1,xi,xi^2 上展开，xi^2 系数 = 3(w-1) => w=1, eta=xi。
      于是纤维中其余两点都不是极点 => 矛盾。这里对一般 w 做多项式展开核对。
  (b) 数值佐证（浮点，容差 1e-7）：对 (1,2),(2,3),(1,4),(3,2),(0,2),(0,3)，求纤维的全部点，确认除 xi 外存在不是 b_w (0<=w<=60) 根的点。
  (c) 线性方程组佐证（精确）：m=1,2，c in [-8,8]，d in [-4,8]，k<=45，形状 (1,2),(2,3) 全部无解。
"""
import sys
import time
from fractions import Fraction as F
from math import comb
import numpy as np

T0 = time.time()
FAILS = []


def log(s):
    print(s, flush=True)


def check(name, ok, desc):
    log(('PASS ' if ok else 'FAIL ') + name + ' ' + desc)
    if not ok:
        FAILS.append(name)


# ---------------- (a) (1,2) 的代数恒等式：系数是 w 的多项式
# 在 Q(xi)[w] 中展开 (w - 1 + xi)^3 - w (1 - xi)，xi^3 = 1 - xi
def mulx(p):
    # p: [c0,c1,c2]（每个 c 是 w 的多项式，列表），乘 xi
    c0, c1, c2 = p
    # xi^3 = 1 - xi
    return [c2, padd(c0, [-t for t in c2]), c1]


def padd(a, b):
    n = max(len(a), len(b))
    r = [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
    while len(r) > 1 and r[-1] == 0:
        r.pop()
    return r


def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def emul(p, q):
    # p, q 都是 [c0,c1,c2]，c 为 w 的多项式
    res = [[0], [0], [0]]
    xp = [q[0], q[1], q[2]]
    for r in range(3):
        # p[r] * xi^r * q
        term = [pmul(p[r], xp[t]) for t in range(3)]
        cur = term
        for _ in range(r):
            cur = mulx(cur)
        res = [padd(res[t], cur[t]) for t in range(3)]
    return res


base = [[-1, 1], [1], [0]]          # (w - 1) + xi
cube = emul(emul(base, base), base)
rhs = [[0, 1], [0, -1], [0]]         # w - w xi
diff = [padd(cube[t], [-c for c in rhs[t]]) for t in range(3)]
log('(1,2): coefficients of (w-1+xi)^3 - w(1-xi) in basis 1,xi,xi^2 as polynomials in w (ascending): %s' % diff)
# 期望：xi^2 系数 = 3(w-1)，且 w=1 时三个系数全为 0
okA = diff[2] == [-3, 3] and all(sum(c * 1 ** e for e, c in enumerate(diff[t])) == 0 for t in range(3))
check('r4.shape12_algebra', okA,
      '(1,2): a root eta of b_w in the fiber of v(xi) forces (w-1+xi)^3 = w(1-xi); the xi^2-coefficient is 3(w-1) => w=1, eta=xi; '
      'so the other two fiber points are never poles of G_m (any m)')

# ---------------- (b) 数值：纤维点是否为 P_m 的根
xi = [r for r in np.roots([1, 0, 1, -1]) if abs(r.imag) < 1e-12][0].real   # x^3 + x - 1


def fiber_points(alpha, beta):
    D = alpha + beta
    if alpha >= 1:
        v0 = xi ** D / (1 - xi) ** beta
        # x^D - v0 (1-x)^beta = 0
        poly = np.zeros(D + 1)
        poly[0] = 1.0                       # x^D（降幂）
        for j in range(beta + 1):
            # (1-x)^beta = sum_j C(beta,j)(-x)^j，x^j 在降幂下标 D-j
            poly[D - j] -= v0 * comb(beta, j) * (-1) ** j
        return list(np.roots(poly))
    # alpha = 0：v = w^beta，w = x/(1-x)
    w0 = xi / (1 - xi)
    pts = []
    for t in range(beta):
        z = w0 * np.exp(2j * np.pi * t / beta)
        pts.append(z / (1 + z))
    return pts


all_b_roots = []
for w in range(0, 61):
    if w == 0:
        all_b_roots.append(1.0 + 0j)
    else:
        all_b_roots.extend(np.roots([-w, 0, -1, 1]))
okB = True
for (al, be) in ((1, 2), (2, 3), (1, 4), (3, 2), (0, 2), (0, 3)):
    pts = fiber_points(al, be)
    others = [p for p in pts if abs(p - xi) > 1e-7]
    nonpole = [p for p in others if min(abs(p - r) for r in all_b_roots) > 1e-7 and abs(p) > 1e-7 and abs(p - 1) > 1e-7]
    log('  shape (%d,%d): fiber points %s; non-pole points other than xi: %d' % (
        al, be, ', '.join('%.5f%+.5fi' % (p.real, p.imag) for p in pts), len(nonpole)))
    okB = okB and len(nonpole) >= 1
check('r4.fiber_numeric', okB,
      'float (tol 1e-7): for shapes (1,2),(2,3),(1,4),(3,2),(0,2),(0,3) the fiber of v(xi) contains a point that is not a root of any b_w (0<=w<=60), '
      'so (given A in C(v)) none of these shapes represents U_k(m) for 1<=m<=60')


# ---------------- (c) 线性方程组佐证
def C(n, r):
    if r < 0 or n < 0 or r > n:
        return 0
    return comb(n, r)


def U_dp(m, K):
    n = m + 1
    U = [1, n] + [0] * (K - 1)
    cnt = {(a, b): 1 for a in range(n) for b in range(n)}
    U[2] = n * n
    for k in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in range(n):
                if b == c or (a >= b and a >= c):
                    new[(b, c)] = new.get((b, c), 0) + v
        cnt = new
        U[k] = sum(cnt.values())
    return U


def solvable(V, c, g, d, e, k0=0):
    K = len(V) - 1
    cols = []
    for s in range(-20, 200):
        r = d + e * s
        if r < 0:
            continue
        if max(0, r + g * s - c) <= K:
            cols.append(s)
        elif s > 0:
            break
    rows = [[F(C(k + c - g * s, d + e * s)) for s in cols] + [F(V[k])] for k in range(k0, K + 1)]
    n = len(cols)
    r = 0
    for col in range(n):
        piv = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][col]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return all(rows[i][-1] == 0 for i in range(r, len(rows)))


KL = 45
found = []
nsys = 0
for m in (1, 2):
    V = U_dp(m, KL)
    for (g, e) in ((1, 2), (2, 3)):
        for c in range(-8, 9):
            for d in range(-4, 9):
                for k0 in (0, 8):
                    nsys += 1
                    if solvable(V, c, g, d, e, k0):
                        found.append((m, g, e, c, d, k0))
# 对照：1/P_m（完整部分）对 (2,1) 形状可解
def A_dp(m, K):
    n = m + 1
    A = [1, n] + [0] * (K - 1)
    cnt = {(a, b): 1 for a in range(n) for b in range(n)}
    A[2] = sum(1 for a in range(n) for b in range(n) if a >= b)
    for k in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in range(n):
                if b == c or (a >= b and a >= c):
                    new[(b, c)] = new.get((b, c), 0) + v
        cnt = new
        A[k] = sum(v for (b, c), v in cnt.items() if b >= c)
    return A


ctrl = all(solvable(A_dp(m, KL), m, 2, m, 1) for m in (1, 2))
check('r4.linsys_odd', found == [] and ctrl,
      'exact: U_k(m) = sum_s A(s) C(k+c-gs, es+d) inconsistent on k0<=k<=45 for m=1,2, (g,e) in {(1,2),(2,3)}, c in [-8,8], d in [-4,8], k0 in {0,8} (%d systems, s from -20); control A_m(k) with (2,1) solvable' % nsys)

log('# elapsed %.1fs' % (time.time() - T0))
log('SUMMARY r4 fail=%d' % len(FAILS))
sys.exit(1 if FAILS else 0)
