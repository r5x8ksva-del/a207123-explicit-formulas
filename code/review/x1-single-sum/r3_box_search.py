# -*- coding: utf-8 -*-
"""x1-single-sum 复核脚本 r3：c2b §6.2–6.5 的盒内搜索与 E(k,m,s) 单项判据——独立重做。

完全自写（不导入 core / polylib / c2b 代码）：
  (0) 自写 DP（只用三元组条件）得 U_k(m)、A_m(k)（不以上升结尾）、E(k,m)（以上升结尾）、E(k,m,s)（按上升数）。
      N、N^c、N^E 用容斥；q<=4 时再用「记录已用值集合」的直接 DP 对照。
  (1) c2b-S1 参数盒：族 (alpha,beta,gamma,delta,eps,zeta) 共 11760，gamma+eps>=2 的 8232 族；
      V(k) = sum_{s>=0} A(m,s) C(k+alpha m+beta-gamma s, delta m+eps s+zeta)，k=0..30，m(q)=1..12。
      求解器：先模大素数消元；若 [A|V] 在模 p 下列满秩+1（=> 有理数上必不相容，严格），否则改用 Fraction 精确消元。
  (2) c2b-S2/S3：E(k,2,2) 闭式；E(k,m,s)（m<=8,s<=6）在 k>=3s-1 上的次数，以及「单项 A*C(k+c,d)」的完全判据
      （由次高项系数唯一确定 c，再整体比对，不依赖整数根搜索区间）。
  (3) c2b-canon：规范三项 u 分解 G_m (1-x)^{m+1} = F0(u) + x F1(u) + x^2 F2(u) 的系数与 DP 对照，m=2 时 f_{0,s} = -2^s 的说法。
"""
import sys
import time
from fractions import Fraction as F
from math import comb

T0 = time.time()
FAILS = []


def log(s):
    print(s, flush=True)


def check(name, ok, desc):
    log(('PASS ' if ok else 'FAIL ') + name + ' ' + desc)
    if not ok:
        FAILS.append(name)


def C(n, r):
    if r < 0 or n < 0 or r > n:
        return 0
    return comb(n, r)


KMAX = 30
MMAX = 12


# ---------------------------------------------------------------- (0) 自写 DP
def dp_tables(m, K):
    n = m + 1
    U = [1] + [0] * K
    A = [1] + [0] * K
    E = [0] * (K + 1)
    if K >= 1:
        U[1] = A[1] = n
    if K >= 2:
        cnt = {(a, b): 1 for a in range(n) for b in range(n)}
        for k in range(2, K + 1):
            if k > 2:
                new = {}
                for (a, b), v in cnt.items():
                    for c in range(n):
                        if b == c or (a >= b and a >= c):
                            new[(b, c)] = new.get((b, c), 0) + v
                cnt = new
            U[k] = sum(cnt.values())
            E[k] = sum(v for (b, c), v in cnt.items() if b < c)
            A[k] = U[k] - E[k]
    return U, A, E


TU, TA, TE = {}, {}, {}
for m in range(0, MMAX + 1):
    TU[m], TA[m], TE[m] = dp_tables(m, KMAX)


def ie(tab, q, k, base_at_minus1):
    tot = 0
    for i in range(q + 1):
        val = base_at_minus1(k) if i == 0 else tab[i - 1][k]
        tot += (-1) ** (q - i) * comb(q, i) * val
    return tot


TN = {q: [ie(TU, q, k, lambda kk: 1 if kk == 0 else 0) for k in range(KMAX + 1)] for q in range(1, MMAX + 1)}
TNc = {q: [ie(TA, q, k, lambda kk: 1 if kk == 0 else 0) for k in range(KMAX + 1)] for q in range(1, MMAX + 1)}
TNE = {q: [ie(TE, q, k, lambda kk: 0) for k in range(KMAX + 1)] for q in range(1, MMAX + 1)}


def direct_surj(q, K):
    """直接 DP：值域恰为 {0..q-1} 的合法词，按是否以上升结尾拆分。"""
    full = (1 << q) - 1
    Nc = [0] * (K + 1)
    NE = [0] * (K + 1)
    if q == 0:
        Nc[0] = 1
        return Nc, NE
    for a in range(q):
        if (1 << a) == full:
            Nc[1] += 1
    cnt = {}
    for a in range(q):
        for b in range(q):
            key = (a, b, (1 << a) | (1 << b))
            cnt[key] = cnt.get(key, 0) + 1
    for k in range(2, K + 1):
        if k > 2:
            new = {}
            for (a, b, mk), v in cnt.items():
                for c in range(q):
                    if b == c or (a >= b and a >= c):
                        key = (b, c, mk | (1 << c))
                        new[key] = new.get(key, 0) + v
            cnt = new
        for (a, b, mk), v in cnt.items():
            if mk == full:
                if a < b:
                    NE[k] += v
                else:
                    Nc[k] += v
    return Nc, NE


ok0 = True
for q in range(1, 5):
    Nc, NE = direct_surj(q, KMAX)
    ok0 = ok0 and Nc == TNc[q] and NE == TNE[q] and [x + y for x, y in zip(Nc, NE)] == TN[q]
# 题面校验数据（第 2 节）抽查
ok0 = ok0 and [TU[m][3] for m in range(7)] == [1, 6, 17, 36, 65, 106, 161] and [TU[m][10] for m in range(7)] == [1, 100, 1222, 7629, 32971, 112349, 323647]
check('r3.tables', ok0, 'own DP tables (k<=30, m<=12) match prompt data; N, N^c, N^E by inclusion-exclusion == direct used-value-set DP for q<=4')

# ---------------------------------------------------------------- 求解器
P1 = (1 << 61) - 1


def build(V, c, g, d, e):
    K = len(V) - 1
    cols = []
    for s in range(0, 200):
        r = d + e * s
        if r < 0:
            if e > 0:
                continue
            break
        # 是否在 k<=K 内有非零项：需要 k + c - g s >= r
        kmin = max(0, r + g * s - c)
        if kmin <= K:
            cols.append(s)
        elif g + e > 0:
            break
    rows = [[C(k + c - g * s, d + e * s) for s in cols] for k in range(K + 1)]
    return cols, rows


def rank_modp(M, ncols):
    M = [[v % P1 for v in row] for row in M]
    r = 0
    for col in range(ncols):
        piv = None
        for i in range(r, len(M)):
            if M[i][col]:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][col], -1, P1)
        M[r] = [v * inv % P1 for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][col]:
                f = M[i][col]
                M[i] = [(x - f * y) % P1 for x, y in zip(M[i], M[r])]
        r += 1
    return r


def consistent_exact(rows, V):
    M = [[F(v) for v in row] + [F(V[k])] for k, row in enumerate(rows)]
    n = len(rows[0]) if rows else 0
    r = 0
    for col in range(n):
        piv = next((i for i in range(r, len(M)) if M[i][col] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][col]
        M[r] = [v / pv for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][col] != 0:
                f = M[i][col]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        r += 1
    return all(M[i][-1] == 0 for i in range(r, len(M)))


STATS = {'modp_rigorous': 0, 'exact': 0}


def consistent(V, c, g, d, e):
    cols, rows = build(V, c, g, d, e)
    n = len(cols)
    if n == 0:
        return all(v == 0 for v in V)
    aug = [row + [V[k]] for k, row in enumerate(rows)]
    if n + 1 <= len(rows):
        ra = rank_modp(aug, n + 1)
        if ra == n + 1:
            STATS['modp_rigorous'] += 1
            return False          # [A|V] 列满秩（模 p => 有理数上也满秩）=> V 不在列空间中
    STATS['exact'] += 1
    return consistent_exact(rows, V)


# ---------------------------------------------------------------- (1) 参数盒
FAM = [(a, b, g, dl, e, z) for a in range(-1, 3) for b in range(-3, 4) for g in range(0, 4)
       for dl in range(0, 3) for e in range(-1, 4) for z in range(-3, 4)]
INF = [f for f in FAM if f[2] + f[4] >= 2]
log('families: %d total, %d with gamma+eps>=2' % (len(FAM), len(INF)))
targets = (('A', TA), ('E', TE), ('U', TU), ('N', TN), ('Nc', TNc), ('NE', TNE))
res = {}
t = time.time()
for name, tab in targets:
    cache = {}
    surv = []
    minm = {}
    for (a, b, g, dl, e, z) in INF:
        dead = None
        for m in range(1, MMAX + 1):
            key = (m, a * m + b, g, dl * m + z, e)
            if key not in cache:
                cache[key] = consistent(tab[m], a * m + b, g, dl * m + z, e)
            if not cache[key]:
                dead = m
                break
        if dead is None:
            surv.append((a, b, g, dl, e, z))
        else:
            minm[dead] = minm.get(dead, 0) + 1
    res[name] = (surv, minm, len(cache))
    log('  target %-2s: survivors %s; refuted at m(q)= %s; distinct systems %d' % (name, surv, dict(sorted(minm.items())), len(cache)))
log('  solver stats %s, box time %.1fs' % (STATS, time.time() - t))
okbox = (sorted(res['A'][0]) == [(1, 0, 2, 1, 1, 0), (1, 2, 2, 1, 1, -1)]
         and all(res[nm][0] == [] for nm in ('E', 'U', 'N', 'Nc', 'NE')))
okmin = (res['U'][1] == {1: len(INF)} and set(res['E'][1]) <= {1, 2} and max(res['N'][1]) <= 2
         and max(res['Nc'][1]) <= 2 and max(res['NE'][1]) <= 3)
check('r3.box', okbox,
      'independent re-run of the c2b box (8232 families, k<=30, m or q = 1..12): no family solvable for E, U, N, N^c, N^E; '
      'for A only (1,0,2,1,1,0) and its index shift (1,2,2,1,1,-1) survive')
check('r3.box_minm', okmin,
      'minimal refuting m: U always m=1; E m<=2 (E: %s); N,N^c q<=2; N^E q<=3 (matches c2b explore8 log)' % res['E'][1])

# ---------------------------------------------------------------- (2) E(k,m,s)
def dp_Es(m, K):
    """E[k][s]：以上升结尾、恰 s 个上升的合法序列数。"""
    n = m + 1
    out = [[0] * (K + 2) for _ in range(K + 1)]
    if K < 2:
        return out
    cnt = {}
    for a in range(n):
        for b in range(n):
            key = (a, b, 1 if a < b else 0)
            cnt[key] = cnt.get(key, 0) + 1
    for k in range(2, K + 1):
        if k > 2:
            new = {}
            for (a, b, s), v in cnt.items():
                for c in range(n):
                    if b == c or (a >= b and a >= c):
                        key = (b, c, s + (1 if b < c else 0))
                        new[key] = new.get(key, 0) + v
            cnt = new
        for (a, b, s), v in cnt.items():
            if a < b:
                out[k][s] += v
    return out


def interp_poly(xs, ys):
    """返回升幂系数（Fraction）。"""
    n = len(xs)
    coef = [F(y) for y in ys]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / (xs[i] - xs[i - j])
    poly = [F(0)]
    for i in range(n - 1, -1, -1):
        # poly = poly*(x - xs[i]) + coef[i]
        newp = [F(0)] * (len(poly) + 1)
        for d, cf in enumerate(poly):
            newp[d + 1] += cf
            newp[d] -= cf * xs[i]
        newp[0] += coef[i]
        poly = newp
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def pev(p, x):
    r = F(0)
    for cf in reversed(p):
        r = r * x + cf
    return r


def single_term(poly):
    """poly 是否等于 A*C(k+c, d) 的多项式（d = deg）：返回 (bool, c)。"""
    d = len(poly) - 1
    if d == 0:
        return True, None
    ratio = poly[d - 1] / poly[d]           # = d*c - d(d-1)/2
    cc = (ratio + F(d * (d - 1), 2)) / d
    if cc.denominator != 1:
        return False, None
    cc = int(cc)
    A = poly[d]
    for k in range(-d - 3, 3):
        prod = F(1)
        for tt in range(d):
            prod *= (k + cc - tt)
        if pev(poly, k) != A * prod:
            return False, None
    return True, cc


KE = 60
okS = True
single = []
deg_ok = True
for m in range(1, 9):
    Es = dp_Es(m, KE)
    if m == 2:
        okS = okS and all(Es[k][2] == ((k - 4) * (3 * k - 1) // 2 if k >= 4 else 0) for k in range(KE + 1))
    for s in range(1, 7):
        dg = m + s - 2
        k0 = 3 * s - 1
        xs = list(range(k0, k0 + dg + 1))
        if xs[-1] + 20 > KE:
            deg_ok = False
            continue
        poly = interp_poly(xs, [Es[k][s] for k in xs])
        deg_ok = deg_ok and len(poly) - 1 == dg and all(pev(poly, k) == Es[k][s] for k in range(k0, min(KE, k0 + dg + 25) + 1))
        # k = 3s-2 处多项式与真值不同（说明阈值 3s-1 不能再降，非必需）
        st, cc = single_term(poly)
        if st:
            single.append((m, s))
        if s == 1:
            okS = okS and all(Es[k][1] == C(k + m - 1, k) for k in range(2, KE + 1))
        if m == 1:
            okS = okS and all(Es[k][s] == C(k - 2 * s, s - 1) for k in range(0, KE + 1) if k >= 3 * s - 1)
expect = sorted([(1, s) for s in range(1, 7)] + [(m, 1) for m in range(2, 9)])
check('r3.Es_closed', okS, 'own refined DP: E(k,2,2)=(k-4)(3k-1)/2 (k>=4, else 0), E(k,m,1)=C(k+m-1,k) (k>=2), E(k,1,s)=C(k-2s,s-1) (k>=3s-1), k<=%d, m<=8' % KE)
check('r3.Es_poly', deg_ok, 'for k>=3s-1, E(k,m,s) agrees with a degree-(m+s-2) polynomial (fit on m+s-1 points, verified on 25 more), m<=8, s<=6')
check('r3.Es_single', sorted(single) == expect,
      'complete single-term test (c forced by the subleading coefficient; no root-range assumption): E(k,m,s) is eventually A*C(k+c,deg) iff s=1 or m=1 (m<=8, s<=6); singles found: %d' % len(single))

# ---------------------------------------------------------------- (3) 规范三项 u 分解
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def Wpoly2(m):
    W = [1]
    for j in range(1, m + 1):
        P = [1]
        for v in range(j):
            P = pmul(P, [1, -1, 0, -v])
        term = [0, 0] + [j * c for c in P]
        W = [(W[i] if i < len(W) else 0) + (term[i] if i < len(term) else 0) for i in range(max(len(W), len(term)))]
    return W


def coords_u(poly, S):
    """多项式 poly(x) 在基 1,x,x^2 上的坐标，每个坐标是 u 的多项式（列表，长 S）。x^3 = u - u x。"""
    # 表示 x^n 的坐标：迭代
    co = [[0] * S for _ in range(3)]
    cur = [[1] + [0] * (S - 1), [0] * S, [0] * S]   # x^0
    for n, cf in enumerate(poly):
        if cf:
            for r in range(3):
                for t in range(S):
                    co[r][t] += cf * cur[r][t]
        # cur *= x: (c0 + c1 x + c2 x^2) x = c0 x + c1 x^2 + c2 (u - u x)
        c0, c1, c2 = cur
        sh = [0] + c2[:-1]           # u*c2
        cur = [sh, [a - b for a, b in zip(c0, sh)], c1]
    return co


okcan = True
fcoef = {}
for m in range(1, 7):
    S = 25
    W = Wpoly2(m)
    co = coords_u(W, S)
    # 1/D(u), D = prod_{v=0}^m (1 - v u)
    invD = [F(1)] + [F(0)] * (S - 1)
    for v in range(1, m + 1):
        # 乘 1/(1-vu)
        acc = [F(0)] * S
        run = F(0)
        for t in range(S):
            run = run * v + invD[t]
            acc[t] = run
        invD = acc
    f = [[sum(F(co[r][i]) * invD[t - i] for i in range(t + 1)) for t in range(S)] for r in range(3)]
    fcoef[m] = f
    # 由 f_{r,s} 重建 U_k(m)
    for k in range(0, KMAX + 1):
        val = sum(f[r][s] * C(k + m - r - 2 * s, m + s) for r in range(3) for s in range(S))
        okcan = okcan and val == TU[m][k]
okm2 = all(fcoef[2][0][s] == -(2 ** s) for s in range(1, 20))
neg5 = any(fcoef[5][2][s] < 0 for s in range(20))
check('r3.canon', okcan and okm2 and neg5,
      'canonical 3-term u-decomposition U_k(m) = sum_s sum_r f_{r,s} C(k+m-r-2s, m+s) reproduces the DP (m<=6, k<=30); m=2: f_{0,s} = -2^s (1<=s<20); m=5: some f_{2,s} < 0')

log('# elapsed %.1fs' % (time.time() - T0))
log('SUMMARY r3 fail=%d' % len(FAILS))
sys.exit(1 if FAILS else 0)
