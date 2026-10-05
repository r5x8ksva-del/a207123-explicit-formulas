# -*- coding: utf-8 -*-
"""r-c2b 复核脚本 6：c2b-misc、c2b-canon、c2b-S2、c2b-S3。

- misc：两个恒等式作为「有理函数恒等式」精确核对（通分后比较多项式，而不是只比较到 x^24 的级数），m<=10；
- canon：G_m(1-x)^{m+1} = F_0(u)+xF_1(u)+x^2F_2(u) 的系数用三角消元独立求出，核对 m=2 时 f_{0,s}=-2^s 及符号观察；
- S2：E(k,2,2) 闭式（对照自写 DP）；
- S3：E(k,m,s) 在 k>=3s-1 时的多项式性，以及「是 A*C(k+c,d) 当且仅当 s=1 或 m=1」——用系数直接解出 c 并精确比较（不靠在 [-300,300] 内数整数根），
  扩大到 m<=10, s<=8；另核对 E(k,1,s)=C(k-2s,s-1) 对全部 k 成立。
"""
import sys, os, time
from fractions import Fraction
from math import comb, factorial

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass

T0 = time.time()
RES = []


def rep(name, ok, msg=''):
    RES.append((name, ok))
    print(('OK   ' if ok else 'BAD  ') + name + ('  ' + msg if msg else ''), flush=True)


def good(a, b, c):
    return b == c or (a >= b and a >= c)


def C(n, r):
    if n < 0 or r < 0 or r > n:
        return 0
    return comb(n, r)


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def pscale(a, c):
    return trim([c * x for x in a])


def pmul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return trim(r)


def ppow(a, n):
    r = [1]
    for _ in range(n):
        r = pmul(r, a)
    return r


def b(v):
    return trim([1, -1, 0, -v])


# ---------------- misc：有理函数恒等式精确核对 ----------------
okT = okP = True
for m in range(1, 11):
    D = [1]
    for v in range(0, m + 1):
        D = pmul(D, b(v))                  # 公分母 P_m = prod_{v=0}^m b_v
    def Qnum(j):
        """Q_j = prod_{v=j}^m b_v^{-1} = P_{j-1}/P_m：返回分子 P_{j-1}（相对公分母 D）。"""
        p = [1]
        for v in range(0, j):
            p = pmul(p, b(v))
        return p
    # 恒等式 1：x sum_{j=1}^m Q_j + x^3 sum_j j Q_j = Q_1 - 1
    lhs = []
    for j in range(1, m + 1):
        lhs = padd(lhs, pmul([0, 1], Qnum(j)))
        lhs = padd(lhs, pscale(pmul([0, 0, 0, 1], Qnum(j)), j))
    rhs = padd(Qnum(1), pscale(D, -1))
    if lhs != rhs:
        okT = False
    # 恒等式 2：sum_{i=0}^m Q_i = sum_{v=1}^m (-1)^{m-v}/((m-v)! b_v) sum_{r=0}^v v^{m-v+r}(1-x)^{-(m-v+r)}/r!
    # 通分：乘以 D*(1-x)^m（右边最大 (1-x) 幂为 m）
    Lnum = []
    for i in range(0, m + 1):
        Lnum = padd(Lnum, Qnum(i))
    Lnum = pmul(Lnum, ppow([1, -1], m))       # (sum Q_i) * D * (1-x)^m
    Rnum = []
    for v in range(1, m + 1):
        Dv = [Fraction(1)]
        for w in range(0, m + 1):
            if w != v:
                Dv = pmul(Dv, b(w))                 # D / b_v
        inner = []
        for r in range(0, v + 1):
            n = m - v + r
            inner = padd(inner, pscale(ppow([1, -1], m - n), Fraction(v ** n, factorial(r))))   # (1-x)^{m-n}
        term = pmul(Dv, inner)
        Rnum = padd(Rnum, pscale(term, Fraction((-1) ** (m - v), factorial(m - v))))
    if trim([Fraction(x) for x in Lnum]) != trim([Fraction(x) for x in Rnum]):
        okP = False
rep('misc_telescope_exact', okT, 'x sum Q_j + x^3 sum j Q_j = Q_1 - 1：通分后的多项式恒等式 (m<=10)')
rep('misc_partial_fraction_exact', okP, 'sum_{i=0}^m Q_i 的部分分式（截断指数和）：通分后的多项式恒等式 (m<=10)')


# ---------------- 自写 DP（细化） ----------------
def refined(K, m):
    SM = K + 2
    comp = [[0] * SM for _ in range(K + 1)]
    ascd = [[0] * SM for _ in range(K + 1)]
    comp[0][0] = 1
    comp[1][0] = m + 1
    st = {}
    for a in range(m + 1):
        for bb in range(m + 1):
            vec = [0] * SM
            vec[1 if a < bb else 0] = 1
            st[(a, bb)] = vec
    def tally(k):
        for (a, bb), vec in st.items():
            tgt = ascd[k] if a < bb else comp[k]
            for s, v in enumerate(vec):
                if v:
                    tgt[s] += v
    tally(2)
    for k in range(3, K + 1):
        nst = {}
        for (a, bb), vec in st.items():
            for c in range(m + 1):
                if not good(a, bb, c):
                    continue
                tv = nst.setdefault((bb, c), [0] * SM)
                if bb < c:
                    for s in range(SM - 1):
                        if vec[s]:
                            tv[s + 1] += vec[s]
                else:
                    for s in range(SM):
                        if vec[s]:
                            tv[s] += vec[s]
        st = nst
        tally(k)
    return comp, ascd


KD = 60
DP = {m: refined(KD, m) for m in range(0, 11)}
print('[dp] %.1fs' % (time.time() - T0), flush=True)

# ---------------- S2 ----------------
ok = all(DP[2][1][k][2] == ((k - 4) * (3 * k - 1) // 2 if k >= 4 else 0) for k in range(KD + 1))
ok = ok and all(((k - 4) * (3 * k - 1)) % 2 == 0 for k in range(4, KD + 1))
rep('S2_E22', ok, 'E(k,2,2)=(k-4)(3k-1)/2 (k>=4) 否则 0，对照自写 DP (k<=60)；根 4 与 1/3 不是相邻整数 => 连「k 充分大成立」的单项都不存在')


# ---------------- S3 ----------------
def interp_coeffs(xs, ys):
    """Lagrange 插值得到升幂系数（Fraction）。"""
    n = len(xs)
    coef = [Fraction(0)] * n
    for i in range(n):
        basis = [Fraction(1)]
        den = Fraction(1)
        for j in range(n):
            if j != i:
                basis = pmul(basis, [Fraction(-xs[j]), Fraction(1)])
                den *= (xs[i] - xs[j])
        for t, v in enumerate(basis):
            coef[t] += Fraction(ys[i]) * v / den
    return trim(coef)


def peval(p, x):
    r = Fraction(0)
    for c in reversed(p):
        r = r * x + c
    return r


singles = []
ok_poly = True
for m in range(1, 11):
    for s in range(1, 9):
        deg = m + s - 2
        k0 = 3 * s - 1
        xs = list(range(k0, k0 + deg + 1))
        if xs[-1] > KD - 5:
            continue
        ys = [DP[m][1][k][s] for k in xs]
        P = interp_coeffs(xs, ys)
        # 多项式性：对 k0..60 全部成立，且次数恰为 deg
        if any(peval(P, k) != DP[m][1][k][s] for k in range(k0, KD + 1)) or len(P) - 1 != deg:
            ok_poly = False
            continue
        # 是否 = A*C(k+c,deg)：由 k^{deg-1} 与 k^deg 系数解出 c，再精确比较
        if deg == 0:
            singles.append((m, s))
            continue
        lead = P[deg]
        sub = P[deg - 1]
        # A*C(k+c,d) = (A/d!) prod_{t=0}^{d-1}(k+c-t)；k^{d-1} 系数 = (A/d!)*sum_t (c-t) = lead*(d*c - d(d-1)/2)
        cval = (sub / lead + Fraction(deg * (deg - 1), 2)) / deg
        if cval.denominator != 1:
            continue
        cval = int(cval)
        A = lead * factorial(deg)
        if all(peval(P, k) == A * Fraction(comb(k + cval, deg) if k + cval >= 0 else 0) or (k + cval < 0) for k in range(k0, k0 + deg + 3)):
            # 还要核对多项式本身（不是组合约定）恒等
            polyC = [Fraction(1)]
            for t in range(deg):
                polyC = pmul(polyC, [Fraction(cval - t), Fraction(1)])
            polyC = [x * A / factorial(deg) for x in polyC]
            if trim(polyC) == P:
                singles.append((m, s))
expect = sorted([(1, s) for s in range(1, 9)] + [(m, 1) for m in range(2, 11)])
singles = sorted(set(singles))
rep('S3_eventual_poly', ok_poly, 'k>=3s-1 时 E(k,m,s) 是 k 的 m+s-2 次多项式（插值后对 k<=60 全部吻合）(m<=10, s<=8, 受 k<=55 插值点限制)')
rep('S3_single_iff', singles == [x for x in expect if x in singles] and set(singles) == set(e for e in expect if (3 * e[1] - 1 + e[0] + e[1] - 2) <= KD - 5),
    '最终单项 <=> s=1 或 m=1（系数法求 c，精确比较）：得到 %s' % singles)
ok = all(DP[1][1][k][s] == C(k - 2 * s, s - 1) for k in range(KD + 1) for s in range(1, 25))
ok = ok and all(DP[m][1][k][1] == C(k + m - 1, k) for m in range(1, 11) for k in range(2, KD + 1))
rep('S3_closed_forms', ok, 'E(k,1,s)=C(k-2s,s-1) 对全部 0<=k<=60、1<=s<=24 成立；E(k,m,1)=C(k+m-1,k) (k>=2, m<=10)')


# ---------------- canon ----------------
def canon(m, NS):
    """G_m(1-x)^{m+1} 的 x 级数，再三角消元求 f_{r,s}。"""
    comp, ascd = DP[m]
    U = [sum(comp[k]) + sum(ascd[k]) for k in range(KD + 1)]
    N = 3 * NS + 3
    V = [sum((-1) ** t * comb(m + 1, t) * U[n - t] for t in range(0, min(n, m + 1) + 1)) for n in range(N)]
    f = {}
    rem = list(V)
    for n in range(N):
        r, s = n % 3, n // 3
        f[(r, s)] = rem[n]
        # 减去 f_{r,s} x^{r+3s}(1-x)^{-s}
        for nn in range(n, N):
            t = nn - n
            coef = 1 if (s == 0 and t == 0) else (0 if s == 0 else comb(t + s - 1, t))
            rem[nn] -= f[(r, s)] * coef
    return f, U


ok = True
f2, U2 = canon(2, 16)
ok = ok and all(f2[(0, s)] == -2 ** s for s in range(1, 17)) and f2[(0, 0)] == 1
# 用规范分解回代 U_k(m)
for m in range(0, 9):
    f, U = canon(m, 18)
    for k in range(0, 50):
        val = sum(f[(r, s)] * C(k + m - r - 2 * s, m + s) for r in range(3) for s in range(0, 19))
        if val != U[k]:
            ok = False
neg5 = [s for s in range(0, 10) if canon(5, 10)[0][(2, s)] < 0]
rep('canon', ok and bool(neg5), 'm=2：f_{0,s}=-2^s (1<=s<=16)；规范三项分解回代 == DP (m<=8, k<=49)；m=5 时 f_{2,s} 为负的 s：%s' % neg5)
print('    m=2 f0:', [f2[(0, s)] for s in range(8)], ' f1:', [f2[(1, s)] for s in range(8)], ' f2:', [f2[(2, s)] for s in range(8)])

print('[time] %.1fs' % (time.time() - T0))
nb = sum(1 for _, o in RES if not o)
print('SUMMARY r6 ok=%d bad=%d' % (len(RES) - nb, nb))
