# -*- coding: utf-8 -*-
"""s6：h_k 结构（T13–T21、T14–T16、V4、V5、C1、U1），全部用复核者自己的代码。

U 表：引理 1 递推（s1 已与自写 DP 对照）。N：容斥。h_k：h_{k,i}=sum_j (-1)^{i-j} C(k+1,i-j) U_k(j)。
实根性：自写整数 Sturm 序列（|lc|^{delta+1} 伪除，保持符号），与作者的 Fraction 版 Sturm 代码无关。
"""
import sys, os, time
from fractions import Fraction as Fr
from math import factorial, comb, gcd
from itertools import product
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rlib import U_rec_table, ok3, peval, pmul, padd, pscale, pderiv, trim

t0 = time.time()
K = int(sys.argv[1]) if len(sys.argv) > 1 else 130
KRR = int(sys.argv[2]) if len(sys.argv) > 2 else 100
T = U_rec_table(K, K + 2)


def Uval(k, m):
    if m == -1:
        return 1 if k == 0 else 0
    return T[k][m]


N = {(k, q): sum((-1) ** (q - i) * comb(q, i) * Uval(k, i - 1) for i in range(q + 1))
     for k in range(K + 1) for q in range(k + 1)}


def gb(x, q):
    num = 1
    for i in range(q):
        num *= (x - i)
    return num // factorial(q)


def Upoly(k, m):
    if k == -1:
        return 1
    if k < -1:
        return 0
    return sum(N[(k, q)] * gb(m + 1, q) for q in range(k + 1))


H = {}
okdeg_le = True
for k in range(K + 1):
    h = [sum((-1) ** (i - j) * comb(k + 1, i - j) * T[k][j] for j in range(i + 1)) for i in range(k + 2)]
    if any(h[i] != 0 for i in range(k, k + 2)) and k >= 1:
        okdeg_le = False
    H[k] = trim(h)
print('deg h_k <= k-1 (coefficients i=k,k+1 vanish), 1<=k<=%d:' % K, okdeg_le)

# 1. h_k = sum_q N(k,q) t^{q-1}(1-t)^{k-q}，k<=80
ok_hN = True
for k in range(1, 81):
    s = []
    for q in range(1, k + 1):
        term = [0] * (q - 1) + [N[(k, q)]]
        for _ in range(k - q):
            term = pmul(term, [1, -1])
        s = padd(s, term)
    if trim(s) != H[k]:
        ok_hN = False
print('T13 h_k = sum_q N(k,q) t^(q-1)(1-t)^(k-q), k<=80:', ok_hN)

# 2. (C6) 递推 + 初值 h_0=1,h_1=1,h_2=1+t；以及若错取 h_2=1 的后果
ok_rec = H[0] == [1] and H[1] == [1] and H[2] == [1, 1]
for k in range(3, K + 1):
    nxt = padd(H[k - 1], pmul([0, 1, -1], padd(pmul([1, -1], pderiv(H[k - 3])), pscale(H[k - 3], k - 2))))
    if nxt != H[k]:
        ok_rec = False
wrong_h3 = padd([1], pmul([0, 1, -1], padd(pmul([1, -1], pderiv([1])), pscale([1], 1))))  # 若 h_2=1：h_3=h_2+...
print('T13 (C6) recurrence with h_0=1,h_1=1,h_2=1+t, 3<=k<=%d:' % K, ok_rec, '; with wrong h_2=1, h_3 would be', wrong_h3)

# 3. h_k(0)=1, h_k(1)=2
print('T13 h_k(0)=1 (k<=%d), h_k(1)=2 (2<=k<=%d):' % (K, K),
      all(peval(H[k], 0) == 1 for k in range(K + 1)) and all(peval(H[k], 1) == 2 for k in range(2, K + 1)))


# 4. 次数、首项、第二首项
def stir1(nmax):
    c = [[0] * (nmax + 2) for _ in range(nmax + 2)]
    c[0][0] = 1
    for n in range(1, nmax + 1):
        for kk in range(1, n + 1):
            c[n][kk] = (n - 1) * c[n - 1][kk] + c[n - 1][kk - 1]
    return c


C1 = stir1(K + 10)


def lead(k):
    a, r = divmod(k, 3)
    return [(-1) ** a * factorial(a), (-1) ** a * C1[a + 2][2], (-1) ** a * factorial(a + 1)][r]


def second(k):
    a, r = divmod(k, 3)
    if r == 0:
        return (-1) ** (a + 1) * 2 * a * factorial(a)
    if r == 1:
        return (-1) ** a * (C1[a + 3][2] + C1[a + 3][3] - factorial(a + 2) - (3 * a + 2) * C1[a + 2][2])
    return (-1) ** a * (C1[a + 3][2] + C1[a + 3][3] - 3 * (a + 1) * factorial(a + 1))


ok_deg = all(len(H[k]) - 1 == (2 * k) // 3 for k in range(1, K + 1))
ok_lead = all(H[k][-1] == lead(k) for k in range(1, K + 1))
ok_sec = all(H[k][-2] == second(k) for k in range(2, K + 1))
print('T15 deg h_k = floor(2k/3) (1<=k<=%d):' % K, ok_deg, '; lead:', ok_lead, '; second (2<=k<=%d):' % K, ok_sec)

# 5. 负整数零点：全部列出 1<=j<=400 中 U_k(-j)=0 的 j
extra = {}
ok_zero = True
for k in range(1, K + 1):
    s = (k + 2) // 3
    zs = [j for j in range(1, 401) if Upoly(k, -j) == 0]
    if zs[:s] != list(range(1, s + 1)):
        ok_zero = False
    if zs != list(range(1, s + 1)):
        extra[k] = [j for j in zs if j > s]
print('T15 zeros of U_k at -1..-400: first segment = 1..floor((k+2)/3) for all k<=%d:' % K, ok_zero,
      '; k with additional zeros beyond the first segment:', extra if extra else 'none')

# 6. G_{-j} 递推与最高六个系数
G = {1: [1]}
for j in range(1, 46):
    G[j + 1] = padd(pmul([1, -1, 0, j], G[j]), [0, 0, j])
ok_G = all(Upoly(k, -j) == (G[j][k] if k < len(G[j]) else 0) for j in range(1, 47) for k in range(K + 1))
ok_top = True
for j in range(2, 47):
    g = G[j]
    if len(g) - 1 != 3 * j - 3:
        ok_top = False
    exp = {3 * j - 3: factorial(j - 1), 3 * j - 4: factorial(j - 1), 3 * j - 5: -C1[j][2], 3 * j - 6: factorial(j - 1),
           3 * j - 7: C1[j][2] + C1[j][3], 3 * j - 8: factorial(j - 1) - C1[j][2] - C1[j][3]}
    for e, v in exp.items():
        if e >= 0 and g[e] != v:
            ok_top = False
print('T14 G_{-j} recurrence == polynomial values U_k(-j) (j<=46,k<=%d):' % K, ok_G, '; deg 3j-3 & top six coeffs (2<=j<=46):', ok_top)

# 7. 互反引理
ok_recip = all((-1) ** k * sum(H[k][i] * comb(i + j - 1, k) for i in range(len(H[k])) if i > k - j) == Upoly(k, -j)
               for k in range(K + 1) for j in range(1, 51))
print('Lemma 4.2 reciprocity, k<=%d, j<=50:' % K, ok_recip)


# 8. Möbius：自顶向下的对偶递推 mu(x,1^)，k<=13；严格链计数 == N(k,q)，k<=10
def allowed(k):
    return [r for r in product((0, 1), repeat=k)
            if all(r[i:i + 3] not in ((0, 0, 1), (0, 1, 0)) for i in range(k - 2))]


mob = []
ok_mu = True
for k in range(1, 14):
    rows = allowed(k)
    rows.sort(key=lambda r: -sum(r))
    leq = lambda a, b: all(x <= y for x, y in zip(a, b))
    top = tuple([1] * k)
    mu = {}
    for r in rows:   # 从大到小
        if r == top:
            mu[r] = 1
        else:
            mu[r] = -sum(mu[z] for z in mu if z != r and leq(r, z))
    v = mu[tuple([0] * k)]
    mob.append(v)
    if v != Upoly(k, -2):
        ok_mu = False
print('T16 Moebius mu(0^,1^) by top-down recursion == U_k(-2), k<=13:', ok_mu, mob)

ok_chain = True
for k in range(1, 11):
    rows = allowed(k)
    rows.sort(key=sum)
    idx = {r: i for i, r in enumerate(rows)}
    lt = lambda a, b: a != b and all(x <= y for x, y in zip(a, b))
    # f[r][q] = 0^ 到 r 的长 q 严格链数
    f = {rows[0]: {0: 1}}
    for r in rows[1:]:
        d = {}
        for z in rows:
            if z in f and lt(z, r):
                for q, c in f[z].items():
                    d[q + 1] = d.get(q + 1, 0) + c
        f[r] = d
    cnt = f[tuple([1] * k)]
    if any(cnt.get(q, 0) != N[(k, q)] for q in range(0, k + 1)) or any(q > k for q in cnt):
        ok_chain = False
print('T16 #strict chains 0^<...<1^ of length q == N(k,q), k<=10:', ok_chain)

# 9. [t^1] h_k 的 g.f.
den = pmul(pmul([1, -1], [1, -1]), [1, -1, 0, -1])
ser = [0] * (K + 1)
num = [0, 0, 1, -1, 1]
for n in range(K + 1):
    s = num[n] if n < len(num) else 0
    for i in range(1, min(n, len(den) - 1) + 1):
        s -= den[i] * ser[n - i]
    ser[n] = s
ok_t1 = all(ser[k] == (H[k][1] if len(H[k]) > 1 else 0) for k in range(K + 1)) and \
    all(H[k][1] == T[k][1] - k - 1 > 0 for k in range(2, K + 1))
print('T17 [t^1]h_k = R_k-k-1 = [x^k] x^2(1-x+x^2)/((1-x)^2(1-x-x^3)) > 0, k<=%d:' % K, ok_t1)


# 10. t=1 处导数
def der_at1(p, d):
    for _ in range(d):
        p = pderiv(p)
    return peval(p, 1) if p else 0


ok_der = all(der_at1(H[k], d) == factorial(d) * sum((-1) ** e * comb(k - 1 - e, d - e) * N[(k, k - e)]
                                                   for e in range(d + 1) if k - 1 - e >= 0 and k - e >= 0)
             for k in range(1, K + 1) for d in range(0, 5))
q1 = [2, 3, -1]
q2 = [Fr(c, 2) for c in (140, -102, 59, -14, 1)]
q3 = [Fr(c, 4) for c in (-13800, 20060, -10054, 2743, -421, 33, -1)]
ok_derx = all(der_at1(H[k], 1) == peval(q1, k) for k in range(4, K + 1)) and \
    all(der_at1(H[k], 2) == peval(q2, k) for k in range(6, K + 1)) and \
    all(der_at1(H[k], 3) == peval(q3, k) for k in range(8, K + 1))
thr = [min(k for k in range(1, K + 1) if all(der_at1(H[kk], d) == peval(qq, kk) for kk in range(k, K + 1)))
       for d, qq in ((1, q1), (2, q2), (3, q3))]
print('T19 general derivative formula (d<=4,k<=%d):' % K, ok_der, '; explicit d=1,2,3:', ok_derx, '; exact thresholds:', thr)

# 11. PDE 的 z^k 系数
ok_pde = True
for k in range(K + 1):
    lhs = padd(H[k], pscale(H[k - 1], -1)) if k >= 1 else list(H[0])
    if k >= 3:
        n = k - 3
        inner = padd(pmul([1, -1], pderiv(H[n])), pscale(H[n], n + 1))
        lhs = padd(lhs, pscale(pmul([0, 1, -1], inner), -1))
    rhs = [1] if k == 0 else ([0, 1] if k == 2 else [])
    if trim(lhs) != trim(rhs):
        ok_pde = False
print('T20 PDE coefficients z^k, k<=%d:' % K, ok_pde)


# 12. 实根性：自写整数 Sturm
def prim(p):
    p = trim(p)
    g = 0
    for c in p:
        g = gcd(g, c)
    return [c // g for c in p] if g > 1 else p


def ideriv(p):
    return trim([i * p[i] for i in range(1, len(p))])


def prem_pos(A, B):
    """|lc(B)|^{delta+1} * A mod B（整数），是 rem(A,B) 的正倍数。"""
    A = list(A)
    db = len(B) - 1
    delta = len(A) - 1 - db
    lb = B[-1]
    A = [c * abs(lb) ** (delta + 1) for c in A]
    while len(A) - 1 >= db and A:
        c = A[-1]
        assert c % lb == 0
        q = c // lb
        sh = len(A) - 1 - db
        for i, b in enumerate(B):
            A[sh + i] -= q * b
        A = trim(A)
    return A


def sturm_seq(p):
    p = prim(p)
    seq = [p, prim(ideriv(p))]
    while len(seq[-1]) > 1:
        r = prem_pos(seq[-2], seq[-1])
        if not r:
            break
        seq.append(prim([-c for c in r]))
    return seq


def var(vals):
    v = [x for x in vals if x != 0]
    return sum(1 for a, b in zip(v, v[1:]) if (a > 0) != (b > 0))


def V_inf(seq, sign):
    return var([s[-1] * (sign ** (len(s) - 1)) for s in seq])


def V_at(seq, x):
    return var([peval(s, x) for s in seq])


rr = {}
ok_rr = True
ok01 = True
okdesc = True
t_rr = time.time()
for k in range(2, KRR + 1):
    seq = sturm_seq(H[k])
    d = len(H[k]) - 1
    nreal = V_inf(seq, -1) - V_inf(seq, 1)
    sqfree = len(seq[-1]) == 1
    n01 = V_at(seq, 0) - V_at(seq, 1)      # (0,1]；h(0)=1≠0
    ngt1 = V_at(seq, 1) - V_inf(seq, 1)
    if not (nreal == d and sqfree):
        ok_rr = False
        rr[k] = (nreal, d, sqfree)
    if n01 != 0:
        ok01 = False
    if var(H[k]) != ngt1:
        okdesc = False
print('V5/C1 own integer Sturm: h_k real-rooted with simple roots for 2<=k<=%d:' % KRR, ok_rr, rr if rr else '',
      '; no roots in [0,1]:', ok01, '; #sign changes == #roots>1:', okdesc, '(%.1fs)' % (time.time() - t_rr))
oklc = all(N[(k, q)] ** 2 >= N[(k, q - 1)] * N[(k, q + 1)] for k in range(3, K + 1) for q in range(2, k))
print('V5 N(k,.) log-concave, k<=%d:' % K, oklc)

# 13. z=-1 在 n_k 中的重数
okm = True
for k in range(1, K + 1):
    p = [N[(k, q)] for q in range(1, k + 1)]
    mlt = 0
    while len(p) > 1 and peval(p, -1) == 0:
        # 除以 (z+1)
        out = []
        acc = 0
        for c in reversed(p):
            acc = c - acc
            out.append(acc)
        out.pop()
        p = list(reversed(out))
        mlt += 1
    if mlt != -(-k // 3) - 1:
        okm = False
print('T16 multiplicity of z=-1 in n_k equals ceil(k/3)-1, k<=%d:' % K, okm)

# 14. V4：固定位置系数转正门槛，扩大到 k<=K
print('V4 thresholds: first k0 such that [t^i]h_k > 0 for all k0<=k<=%d (i=1..14):' % K)
res = []
for i in range(1, 15):
    k0 = None
    for kk in range(K, 0, -1):
        if len(H[kk]) > i and H[kk][i] > 0:
            k0 = kk
        else:
            break
    res.append((i, k0))
print('  ', res)
claimed = {1: 2, 2: 8, 3: 16, 4: 24, 5: 33, 6: 41, 7: 50, 8: 59}
print('   claimed thresholds (i=1..8) still valid up to k=%d:' % K, all(dict(res)[i] == claimed[i] for i in claimed))

# 15. h_k(-1) 前 21 项
hm1 = [peval(H[k], -1) for k in range(21)]
claimed_hm1 = [1, 1, 0, -2, -6, -10, -10, 10, 82, 238, 438, 266, -1518, -7506, -19818, -30038, 12050, 264238,
               1028534, 2428682, 2537938]
print('U1 h_k(-1), k<=20 matches notes:', hm1 == claimed_hm1)
print('elapsed %.1fs' % (time.time() - t0))
