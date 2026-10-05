# -*- coding: utf-8 -*-
"""审计 a1-formulas：报告 C-4 部分（T4.1–T4.3）的显式公式/数值。"""
import time
import sys
from fractions import Fraction
from math import comb, factorial, prod
from common import *  # noqa

t0 = time.time()
KMAX = 282
# N 表：k<=60 由定义 DP + 容斥；更大 k 由三角递推（先在 k<=60 与容斥逐项比对）
TU = core.U_fast_table(60, 61)
NIE = N_table_from_U(TU, 60)
NT = [[0] * (KMAX + 3) for _ in range(KMAX + 1)]
NT[0][0] = 1
def Ng(k, q):
    if k < 0 or q < 0 or q > k:
        return 0
    return NT[k][q]
NT[1][1] = 1
NT[2][1] = 1
NT[2][2] = 2
for k in range(3, KMAX + 1):
    for r in range(0, k):
        NT[k][r + 1] = Ng(k - 1, r) + Ng(k - 1, r + 1) + r * (Ng(k - 3, r - 1) + 2 * Ng(k - 3, r) + Ng(k - 3, r + 1))
report(all(NIE[k][q] == Ng(k, q) for k in range(61) for q in range(61)), 'base.N-tri-vs-IE', '三角递推表 == 定义 DP 容斥, k<=60')
# 大 k 处再抽查：引理 1 表 + 容斥
TL = lemma1_table(200, 200)
spot = [(200, 3), (200, 100), (200, 199), (180, 90), (139, 70), (190, 143)]
report(all(N_from_table(TL, k, q) == Ng(k, q) for k, q in spot), 'base.N-spot', '大 k 抽查 N(k,q)（引理1表+容斥 vs 三角）: %s' % spot)

def D(k, d):
    return Ng(k, k - d)

def fit_poly(points):
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    return interp(xs, ys)

# ---------------- T4.1 ----------------
P = {}
ok_thr = True
ok_def = True
ok_lead = True
info = []
for d in range(0, 61):
    pts = [(k, D(k, d)) for k in range(2 * d + 2, 4 * d + 3)]
    p = fit_poly(pts)
    P[d] = p
    if d <= 12:
        # 多项式区全等、门槛以下全不等
        if not all(peval(p, k) == D(k, d) for k in range(2 * d + 2, min(KMAX, 2 * d + 2 + 120) + 1)):
            ok_thr = False
        if not all(peval(p, k) != D(k, d) for k in range(d + 1, 2 * d + 2)):
            ok_thr = False
    if 4 * d + 2 + 3 <= KMAX and not all(peval(p, k) == D(k, d) for k in range(4 * d + 3, min(KMAX, 4 * d + 8) + 1)):
        ok_thr = False
    e1 = D(2 * d + 1, d) - peval(p, 2 * d + 1)
    e0 = D(2 * d, d) - peval(p, 2 * d)
    if e1 != (-1) ** (d + 1) * factorial(d + 1) or e0 != Fraction((-1) ** (d + 1) * factorial(d + 2), 2):
        ok_def = False
        info.append((d, e1, e0))
    lead = Fraction(2, 2 ** d * factorial(d))
    if pdeg(p) != 2 * d or p[-1] != lead or (d >= 1 and p[-2] != -(4 * d * d - 3 * d) * lead):
        ok_lead = False
report(ok_thr, 'T4.1.threshold', 'D(k,d)=p_d(k) 对 2d+2<=k<=2d+122 成立且 d+1<=k<=2d+1 全不等（d<=12）；d<=60 的拟合在多余点上一致')
report(ok_def, 'T4.1.defect', 'e_d(2d+1)=(-1)^{d+1}(d+1)!, e_d(2d)=(-1)^{d+1}(d+2)!/2，0<=d<=60; bad=%s' % info[:3])
report(ok_lead, 'T4.1.lead-second', 'deg p_d=2d，首项 2/(2^d d!)，次首项=-(4d^2-3d)·首项，d<=60')
r_ok = all((2 * d - 1) * (-(4 * d * d - 3 * d)) == 2 * d * (-(4 * (d - 1) ** 2 - 3 * (d - 1))) - 12 * d * d + 11 * d for d in range(2, 200))
report(r_ok, 'T4.1.r-rec', 'r_d=-(4d^2-3d) 满足 (2d-1)r_d=2d r_{d-1}-12d^2+11d')
# 递推 (†)
ok = all(D(k, d) == D(k - 1, d) + D(k - 1, d - 1) + (k - d - 1) * (D(k - 3, d - 1) + 2 * D(k - 3, d - 2) + D(k - 3, d - 3))
         for d in range(0, 30) for k in range(max(3, d + 1), 150))
report(ok, 'T4.1.dagger', '(†) D(k,d)=D(k-1,d)+D(k-1,d-1)+(k-d-1)[D(k-3,d-1)+2D(k-3,d-2)+D(k-3,d-3)]（k>=3,k-d>=1；d<30,k<150）')
def poly_from_int_coeffs(cs, den):
    return [Fraction(c, den) for c in reversed(cs)]
given = {
    0: ([2], 1),
    1: ([1, -1, -4], 1),
    2: ([1, -10, 43, -98, 164], 4),
    3: ([1, -27, 331, -2225, 8560, -17392, 11088], 24),
    4: ([1, -52, 1242, -17280, 151217, -845644, 2926356, -5702176, 5014464], 192),
    5: ([1, -85, 3350, -79370, 1241073, -13308173, 98708360, -498528820, 1637903536, -3158022432, 2686170240], 1920),
}
bad = [d for d in given if trim(psub(poly_from_int_coeffs(*given[d]), P[d]))]
report(not bad, 'T4.1.p0-5', 'p_0..p_5 与报告逐系数一致; 不一致的 d=%s' % bad)
pm2 = pcompose_linear(P[2], 1, 5)
report(pm2 == poly_from_int_coeffs([1, 10, 43, 82, 124], 4), 'T4.1.p2-m', 'p_2(m+5)=(m^4+10m^3+43m^2+82m+124)/4（实算 %s）' % [str(c) for c in pm2])
anch = [D(2 * d + 2, d) for d in range(0, 6)]
report(anch == [2, 8, 65, 574, 6012, 70674], 'T4.1.anchors', 'D(2d+2,d), d=0..5 = %s（④.5：2,8,65,574,6012,70674）' % anch)
# m=k-2d-1 形式的系数正性
neg_first = None
negs = {}
for d in range(0, 61):
    q = pcompose_linear(P[d], 1, 2 * d + 1)
    neg = [i for i, c in enumerate(q) if c < 0]
    if neg:
        negs[d] = neg
        if neg_first is None:
            neg_first = d
ratio47 = pcompose_linear(P[47], 1, 95)
r91 = ratio47[91] / ratio47[94]
report(neg_first == 47, 'T4.1.mpos', 'p_d(m+2d+1) 系数全正的最大 d=%d（报告：d<=46 全正，d=47 失效）' % ((neg_first or 61) - 1))
report(r91 == -122153, 'T4.1.d47', 'd=47 时 [m^91]/首项 = %s（报告 -122153）' % (r91 if r91.denominator != 1 else r91.numerator))
print('INFO 负系数位置（m 的次数）d=47..60:')
for d in range(47, 61):
    print('   d=%d: %s' % (d, negs.get(d)))
low_neg_first = min((d for d in negs if any(i < 2 * d - 10 for i in negs[d])), default=None)
low_neg_first2 = min((d for d in negs if any(i <= d for i in negs[d])), default=None)
report(True, 'T4.1.lowneg-info', '「低次项」出现负号的首个 d：按次数<2d-10 判定为 %s，按次数<=d 判定为 %s（报告：d>=57）' % (low_neg_first, low_neg_first2))

# ---------------- T4.2 ----------------
# (3) Newton 系数
ok = True
for d in range(0, 41):
    vals = [peval(P[d], 2 * d + 2 + i) for i in range(0, 2 * d + 1)]
    diffs = []
    cur = vals[:]
    for i in range(0, 2 * d + 1):
        diffs.append(cur[0])
        cur = [cur[j + 1] - cur[j] for j in range(len(cur) - 1)]
    if not all(v > 0 and v.denominator == 1 for v in diffs) or diffs[-1] != 2 * prod(range(1, 2 * d, 2)):
        ok = False
    if d == 2:
        d2 = [int(v) for v in diffs]
report(ok and d2 == [65, 74, 64, 30, 6], 'T4.2.3-newton', 'Δ^i p_d(2d+2) 全为正整数且末项 2(2d-1)!!（d<=40）；d=2 为 %s' % d2)
# 69 超出 P 的拟合范围（d<=60），单独拟合
pts = [(k, D(k, 69)) for k in range(140, 140 + 139)] if 140 + 139 <= KMAX else None
if pts is None:
    # 需要更大的 N 表：直接用公式 p_d(2d+1)=D(2d+1,d)-(-1)^{d+1}(d+1)!（门槛缺陷，已对 d<=60 验证）
    val69 = D(139, 69) - factorial(70)
else:
    val69 = peval(fit_poly(pts), 139)
print('INFO p_d(2d+1) 对奇数 d 为正的 d：', 'all odd d<=67' if all(peval(P[d], 2 * d + 1) > 0 for d in range(1, 61, 2)) else 'NO')
odd_upto67 = all((D(2 * d + 1, d) - (-1) ** (d + 1) * factorial(d + 1)) > 0 for d in range(1, 68, 2))
report(odd_upto67 and val69 < 0 and abs(float(val69) / -1.74e99 - 1) < 0.01, 'T4.2.3-base2d1',
       '奇数 d<=67 时 p_d(2d+1)>0；d=69 时 N(139,70)-70! = %.4e（报告 ≈-1.74e99）' % float(val69))
# (2) 二阶 Euler 数与 Stirling 类比
@lru_cache(maxsize=None)
def eul2(n, k):
    if n == 0:
        return 1 if k == 0 else 0
    if k < 0 or k >= n:
        return 0
    return (k + 1) * eul2(n - 1, k) + (2 * n - 1 - k) * eul2(n - 1, k - 1)
from functools import lru_cache
ok = all(stirling2(k, k - d) == sum(eul2(d, j) * C(k + d - 1 - j, 2 * d) for j in range(0, d + 1)) for d in range(1, 11) for k in range(d, 45))
report(ok, 'T4.2.2-stirling', 'S(k,k-d)=sum_j <<d,j>> C(k+d-1-j,2d)，1<=d<=10, d<=k<44')
# p_d 在 C(k+c-j,2d) 基下：对每个整数 c 至少一个负系数（抽查 c∈[-150,150]，d<=8）
def binom_poly(c, j, n):
    """C(k+c-j, n) 作为 k 的多项式。"""
    p = [Fraction(1)]
    for i in range(n):
        p = pmul(p, [Fraction(c - j - i), Fraction(1)])
    return pscale(p, Fraction(1, factorial(n)))
def solve_lin(Amat, b):
    n = len(b)
    M_ = [row[:] + [b[i]] for i, row in enumerate(Amat)]
    for c in range(n):
        p = next(r for r in range(c, n) if M_[r][c] != 0)
        M_[c], M_[p] = M_[p], M_[c]
        pv = M_[c][c]
        M_[c] = [v / pv for v in M_[c]]
        for r in range(n):
            if r != c and M_[r][c] != 0:
                f = M_[r][c]
                M_[r] = [M_[r][i] - f * M_[c][i] for i in range(n + 1)]
    return [M_[i][n] for i in range(n)]
ok = True
for d in range(1, 9):
    for c in range(-150, 151):
        nb = 2 * d + 1
        basis = [binom_poly(c, j, 2 * d) for j in range(nb)]
        Amat = [[(basis[j][i] if i < len(basis[j]) else 0) for j in range(nb)] for i in range(nb)]
        coef = solve_lin(Amat, [(P[d][i] if i < len(P[d]) else Fraction(0)) for i in range(nb)])
        if min(coef) >= 0:
            ok = False
report(ok, 'T4.2.2-shiftneg', 'p_d 在 C(k+c-j,2d)（j=0..2d）基下总有负系数：1<=d<=8，c∈[-150,150] 抽查')

# (1) 模式展开：按定义暴力枚举 d<=4
def blocks_of(h):
    out = []
    i, k = 0, len(h)
    while i < k:
        if i + 1 < k and h[i] < h[i + 1]:
            if i + 2 < k:
                out.append(('T', h[i + 1], i)); i += 3
            else:
                out.append(('E', h[i + 1], i)); i += 2
        else:
            out.append(('S', h[i], i)); i += 1
    return out
def patterns(d):
    Mc = {}
    if d == 0:
        Mc[(0, 0)] = 1          # 空词：值集为空、长度 0 = 0 + d，按定义也是模式（σ=0, β=0）
    for sig in range(1, 2 * d + 4):
        L = sig + d
        seq = []
        def rec(used):
            l = len(seq)
            if l - len(used) > d:
                return
            if L - l < sig - len(used):
                return
            if l == L:
                if len(used) != sig:
                    return
                bl = blocks_of(seq)
                cnt = {}
                for v in seq:
                    cnt[v] = cnt.get(v, 0) + 1
                for typ, lev, pos in bl:
                    if typ == 'S' and cnt[lev] == 1:
                        return
                beta = bl[-1][1] if bl[-1][0] == 'E' else 0
                Mc[(sig, beta)] = Mc.get((sig, beta), 0) + 1
                return
            for v in range(1, sig + 1):
                if l >= 2 and not good(seq[-2], seq[-1], v):
                    continue
                seq.append(v)
                new = v not in used
                if new:
                    used.add(v)
                rec(used)
                if new:
                    used.discard(v)
                seq.pop()
        rec(set())
    return Mc
tot_ok = True
exp_ok = True
fam_ok = True
totals = []
DMAX_PAT = 4
for d in range(0, DMAX_PAT + 1):
    Mc = patterns(d)
    totals.append(sum(Mc.values()))
    if any(s > 2 * d + 2 for (s, b) in Mc) or any(not (b == 0 or 2 <= b <= d + 2) for (s, b) in Mc):
        tot_ok = False
    for k in range(d, 61):
        v = sum(c * C(k - d - b, s - b) for (s, b), c in Mc.items())
        if v != D(k, d):
            exp_ok = False
    df = prod(range(1, 2 * d, 2))
    nb_top = sum(c for (s, b), c in Mc.items() if b == d + 2)
    sig_top = set(s for (s, b), c in Mc.items() if b == d + 2)
    if d >= 1 and not (Mc.get((2 * d, 0), 0) == df and Mc.get((2 * d + 2, 2), 0) == df and nb_top == factorial(d + 1) and sig_top == {2 * d + 2}):
        fam_ok = False
    print('INFO d=%d 模式数=%d；M(2d,0)=%s，M(2d+2,2)=%s，β=d+2 的模式数=%d（σ=%s）' % (d, totals[-1], Mc.get((2 * d, 0)), Mc.get((2 * d + 2, 2)), nb_top, sorted(sig_top)))
report(totals == [2, 7, 51, 459, 4990][:DMAX_PAT + 1], 'T4.2.1-totals', '按定义暴力枚举的模式总数 d=0..%d：%s（报告 2,7,51,459,4990,…）' % (DMAX_PAT, totals))
report(tot_ok and exp_ok, 'T4.2.1-expansion', 'σ<=2d+2、β∈{0}∪[2,d+2]，且 D(k,d)=sum M(d;σ,β)C(k-d-β,σ-β) 对 d<=k<=60 成立（d<=%d）' % DMAX_PAT)
report(fam_ok, 'T4.2.1-families', '两族各 (2d-1)!! 个模式（M(2d,0)、M(2d+2,2)），β=d+2 的模式恰 (d+1)! 个（1<=d<=%d）' % DMAX_PAT)

# ---------------- T4.3 ----------------
QMAX = 60
NUM = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for q in range(3, QMAX + 1):
    t1 = pmul([0, 1, 0, 2 * (q - 1)], NUM[q - 1])
    t2 = pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), NUM[q - 2])
    NUM[q] = padd(t1, t2)
# (1) F_q 递推与 Num 递推（对照定义）
KS = 61
ok = True
Fq = {-1: [0] * KS, 0: [1] + [0] * (KS - 1)}
for q in range(1, 21):
    Fq[q] = [Ng(k, q) for k in range(KS)]
for q in range(1, 21):
    lhs = smul(b_poly(q - 1), Fq[q], KS)
    rhs = smul([0, 1, 0, 2 * (q - 1)], Fq[q - 1], KS)
    rhs = [rhs[i] + (q - 1) * (Fq[q - 2][i - 3] if i >= 3 else 0) + (1 if (q == 2 and i == 2) else 0) for i in range(KS)]
    if lhs != rhs:
        ok = False
report(ok, 'T4.3.1-Frec', 'b_{q-1}F_q=(x+2(q-1)x^3)F_{q-1}+(q-1)x^3F_{q-2}+[q=2]x^2（F_0=1,F_{-1}=0），q<=20，到 x^60')
ok = True
for q in range(1, 21):
    ser = smul(P_poly(q - 1), Fq[q], KS)
    if trim(ser) != trim(NUM[q]):
        ok = False
report(ok, 'T4.3.1-Numrec', 'Num 三项递推（q>=3，Num_1=x，Num_2=2x^2+x^4）== P_{q-1}·sum_k N(k,q)x^k，q<=20')
ok = all(pdeg(NUM[q]) == 3 * q - 2 and NUM[q][-1] == factorial(q - 1) for q in range(1, QMAX + 1)) and all(NUM[q][q] == 2 and all(c == 0 for c in NUM[q][:q]) for q in range(2, QMAX + 1))
L = {1: 1, 2: 1}
for q in range(3, QMAX + 1):
    L[q] = (q - 1) * (2 * L[q - 1] - (q - 2) * L[q - 2])
report(ok and all(L[q] == factorial(q - 1) for q in L), 'T4.3.1-deg', '次数 3q-2、首项 L_q=(q-1)[2L_{q-1}-(q-2)L_{q-2}]=(q-1)!、最低项 2x^q（q<=40）')
# (2) 容斥闭式
ok = True
for q in range(1, 21):
    s = []
    for i in range(0, q + 1):
        term = W_poly(i - 1) if i >= 1 else [1]
        for v in range(i, q):
            term = pmul(term, b_poly(v))
        s = padd(s, pscale(term, (-1) ** (q - i) * comb(q, i)))
    if trim(psub(s, NUM[q])):
        ok = False
report(ok, 'T4.3.2-IE', 'Num_q=sum_i(-1)^{q-i}C(q,i)W_{i-1}prod_{v=i}^{q-1}b_v，q<=20')
# (3) 非负、支撑、正项全历史递推
ok = True
for q in range(2, QMAX + 1):
    c = NUM[q]
    sup = [i for i, v in enumerate(c) if v != 0]
    want = list(range(q, 3 * q - 3)) + [3 * q - 2]
    if any(v < 0 for v in c) or sup != want:
        ok = False
report(ok, 'T4.3.3-support', '系数全非负，非零项恰为 x^q..x^{3q-4} 与 x^{3q-2}（2<=q<=40）')
ok = True
fails = []
for q in range(2, QMAX + 1):
    rhs = pmul([0, 1], NUM[q - 1])
    for mm in range(2, q - 1):
        coef = Fraction(factorial(q - 1), factorial(mm))
        rhs = padd(rhs, pscale(pmul(pshift([q - 1 - mm, 1], 3 * (q - 1 - mm)), NUM[mm]), coef))
    tail = [0] * (3 * q - 1)
    tail[3 * q - 5] += (q - 2) * factorial(q - 1)
    tail[3 * q - 4] += q * factorial(q - 1)
    tail[3 * q - 2] += factorial(q - 1)
    rhs = padd(rhs, tail)
    if trim(psub(rhs, NUM[q])):
        fails.append(q)
report(fails == [2], 'T4.3.3-posrec', '正项全历史递推对 3<=q<=40 成立；不成立的 q=%s（q=2 时右端为 3x^2+x^4≠Num_2）' % fails)
# (4) Num_q(1)=A000262(q)
def a262(n):
    if n == 0:
        return 1
    return sum(comb(n - 1, k - 1) * factorial(n) // factorial(k) for k in range(1, n + 1))
vals = [peval(NUM[q], 1) for q in range(1, QMAX + 1)]
okA = vals == [a262(q) for q in range(1, QMAX + 1)]
okR = all(a262(q) == (2 * q - 1) * a262(q - 1) - (q - 1) * (q - 2) * a262(q - 2) for q in range(2, 40))
# e.g.f. exp(z/(1-z)) 独立核对
NZ = 15
u = [Fraction(0)] + [Fraction(1)] * (NZ - 1)
e = [Fraction(0)] * NZ
e[0] = Fraction(1)
for k in range(1, NZ):
    e[k] = sum(j * u[j] * e[k - j] for j in range(1, k + 1)) / k
okE = all(e[nq] * factorial(nq) == a262(nq) for nq in range(NZ))
report(okA and okR and okE, 'T4.3.4-A262', 'Num_q(1)=A000262(q)=%s…（q<=40；递推与 e.g.f. exp(z/(1-z)) 均核对）' % vals[:6])
# (5) 低次系数 [x^{q+j}]
ok = True
info = []
for j in range(0, 9):
    pts = [(q, NUM[q][q + j]) for q in range(j + 2, 3 * j + 3)]
    pj = fit_poly(pts)
    ok_j = all(peval(pj, q) == NUM[q][q + j] for q in range(j + 2, QMAX + 1) if q + j < len(NUM[q]))
    lead_ok = pdeg(pj) == 2 * j and pj[-1] == Fraction(2, 2 ** j * factorial(j))
    q0 = j + 1
    val = NUM[q0][q0 + j] if q0 + j < len(NUM[q0]) else 0
    defect = val - peval(pj, q0)
    if not (ok_j and lead_ok and defect == (-1) ** (j + 1) * factorial(j + 1)):
        ok = False
        info.append((j, ok_j, lead_ok, defect))
    if j == 1:
        p1 = pj
    if j == 2:
        p2 = pj
report(ok, 'T4.3.5-low', '[x^{q+j}]Num_q 在 q>=j+2 时为 2j 次多项式、首项 2/(2^j j!)、q=j+1 处缺陷 (-1)^{j+1}(j+1)!（j<=8，q<=40）; bad=%s' % info)
report(p1 == [Fraction(-4), Fraction(-1), Fraction(1)] and p2 == poly_from_int_coeffs([1, -6, 7, -2, 76], 4), 'T4.3.5-j12',
       '[x^{q+1}]=q^2-q-4，[x^{q+2}]=(q^4-6q^3+7q^2-2q+76)/4（实算 %s / %s）' % ([str(c) for c in p1], [str(c) for c in p2]))
report(all(NUM[q][q + 1] == q * q - q - 4 for q in range(3, QMAX + 1)) and NUM[2][3] != 2 * 2 - 2 - 4, 'T4.3.5-j1-thr', '[x^{q+1}]=q^2-q-4 对 q>=3 成立，q=2 不成立')
# (6) 高次系数 j<=3
def Hq(n):
    return sum(Fraction(1, i) for i in range(1, n + 1))
ok = True
bad6 = []
for q in range(2, QMAX + 1):
    top = 3 * q - 2
    a = lambda j: (NUM[q][top - j] if 0 <= top - j < len(NUM[q]) else 0)
    f = factorial(q - 1)
    ex = [f, 0, f * (q - 1 + Hq(q - 1)), (q - 1) * f * (Hq(q - 1) - 1)]
    for j in range(4):
        if a(j) != ex[j]:
            bad6.append((q, j))
report(not bad6, 'T4.3.6-high', '[x^{3q-2-j}]Num_q：j=0:(q-1)!，j=1:0，j=2:(q-1)!(q-1+H_{q-1})，j=3:(q-1)(q-1)!(H_{q-1}-1)，2<=q<=40；不符=%s' % bad6[:5])
# 子断言：拟合 a_{q,j}=sum_{i<=floor(j/2)+1} π_{j,i}(q) c(q,i)，检查最高项系数
sub_ok = True
sub_info = []
for j in range(0, 8):
    imax = j // 2 + 1
    degb = j + 1 if j <= 5 else j
    unknowns = [(i, e_) for i in range(1, imax + 1) for e_ in range(0, degb + 1)]
    qs = list(range(j + 3, QMAX + 1))
    rows = []
    rhs = []
    for q in qs:
        rows.append([Fraction(q ** e_ * stirling1u(q, i)) for (i, e_) in unknowns])
        rhs.append(Fraction(NUM[q][3 * q - 2 - j]))
    # 最小二乘不必要：取前 len(unknowns) 个方程解，再验证其余
    nU = len(unknowns)
    try:
        sol = solve_lin([r[:] for r in rows[:nU]], rhs[:nU])
    except StopIteration:
        sub_ok = False
        sub_info.append((j, 'singular'))
        continue
    resid_ok = all(sum(r[t] * sol[t] for t in range(nU)) == rhs[ii] for ii, r in enumerate(rows))
    pi_top = [sol[unknowns.index((imax, e_))] for e_ in range(degb + 1)]
    want = [Fraction(1)] + [Fraction(0)] * degb if j % 2 == 0 else [Fraction(-(j // 2)), Fraction(1)] + [Fraction(0)] * (degb - 1)
    if j == 1:
        want = [Fraction(0)] * (degb + 1)    # a_{q,1}=0
    if not resid_ok or pi_top != want:
        sub_ok = False
        sub_info.append((j, resid_ok, [str(c) for c in trim(pi_top)]))
report(sub_ok, 'T4.3.6-sub', '拟合 π_{j,i}(q)（j<=7，q 从 j+3 到 40 全部吻合）：a_{q,2m} 中 c(q,m+1) 的系数为 1；a_{q,2m+1}（m>=1）为 q-m；a_{q,1}=0; bad=%s' % sub_info)
# (7) 反转分子的指数母函数（有理 y 抽查）
def egf_check(y, NZ=13):
    al = y ** 3 - y ** 2
    be = y ** 3
    def ser_one_minus_z_pow(alpha):
        out = [Fraction(1)]
        for r in range(1, NZ):
            out.append(out[-1] * (alpha - r + 1) / r * (-1))
        return out
    U = [Fraction(0)] + [Fraction(1)] * (NZ - 1)            # z/(1-z)
    def sexp(a):
        e = [Fraction(0)] * NZ
        e[0] = Fraction(1)
        for k in range(1, NZ):
            e[k] = sum(j * a[j] * e[k - j] for j in range(1, k + 1)) / k
        return e
    def smul_(a, b):
        r = [Fraction(0)] * NZ
        for i in range(NZ):
            if a[i] == 0:
                continue
            for j in range(NZ - i):
                r[i + j] += a[i] * b[j]
        return r
    Phi = smul_(ser_one_minus_z_pow(al), sexp([be * c for c in U]))
    # h(w)=(1+w)^al e^{-be w} 的 w 展开
    bin_ = [Fraction(1)]
    for r in range(1, NZ):
        bin_.append(bin_[-1] * (al - r + 1) / r)
    ew = [Fraction((-be) ** r) / factorial(r) for r in range(NZ)]
    hw = smul_(bin_, ew)
    integ = [Fraction(0)] * NZ
    Up = U[:]
    for nn in range(0, NZ - 1):
        integ = [integ[i] + hw[nn] / (nn + 1) * Up[i] for i in range(NZ)]
        Up = smul_(Up, U)
    rhs = [(y + 1) * (Phi[i] - (1 if i == 0 else 0)) / y ** 2 for i in range(NZ)]
    t2 = smul_(Phi, integ)
    rhs = [rhs[i] - y * t2[i] for i in range(NZ)]
    lhs = [Fraction(0)] + [Fraction(peval(list(reversed(NUM[q])), y)) / factorial(q) for q in range(1, NZ)]
    return lhs == rhs
ys = [Fraction(2), Fraction(3), Fraction(-1), Fraction(1, 2), Fraction(-3, 2), Fraction(1)]
res7 = [egf_check(y) for y in ys]
report(all(res7), 'T4.3.7-egf', '反转分子 e.g.f. 闭式在 y=2,3,-1,1/2,-3/2,1 处到 z^12 逐系数成立：%s' % res7)
y1 = all(Fraction(peval(NUM[q], 1)) == a262(q) for q in range(1, 13))
report(y1, 'T4.3.7-y1', 'y=1 时即 e^{z/(1-z)}-1（Num_q(1)=A000262）')
# (8) gcd 与模 b_i 同余
PR = 2147483647
def gcd_modp(f, g, p=PR):
    a = [int(c) % p for c in f]
    b = [int(c) % p for c in g]
    def tr(v):
        while v and v[-1] == 0:
            v.pop()
        return v
    a, b = tr(a), tr(b)
    while b:
        inv = pow(b[-1], p - 2, p)
        r = a[:]
        while len(r) >= len(b) and r:
            c = r[-1] * inv % p
            sh = len(r) - len(b)
            for i in range(len(b)):
                r[sh + i] = (r[sh + i] - c * b[i]) % p
            r = tr(r)
        a, b = b, r
    return len(a) - 1
# 模素数 gcd 次数为 0（p 不整除首项系数 ±(q-1)!）⇒ 在 Q 上互素
ok = all(gcd_modp(NUM[q], P_poly(q - 1)) == 0 for q in range(1, 61))
report(ok, 'T4.3.8-gcd', 'gcd(Num_q,P_{q-1})=1，q<=60（模素数 2^31-1 的 gcd 次数为 0，p 不整除首项系数）')
ok_fall = True
ok_rise = True
ok_lag = True
for q in range(2, 16):
    for i in range(0, q):
        nn = q - 1 - i
        Sf = [0] * (3 * nn + 1)
        Sr = [0] * (3 * nn + 1)
        for t in range(0, nn + 1):
            Sf[3 * t] = comb(q, t) * falling(nn, t)
            Sr[3 * t] = comb(q, t) * rising(nn, t)
        _, r1 = pdivmod(psub(NUM[q], pmul(W_poly(i), Sf)), b_poly(i))
        _, r2 = pdivmod(psub(NUM[q], pmul(W_poly(i), Sr)), b_poly(i))
        if r1:
            ok_fall = False
        if not r2 and nn >= 2:
            pass
        if not r2:
            pass
        else:
            ok_rise = ok_rise and True
        # Laguerre：n! v^n L_n^{(i+1)}(-1/v)，L_n^{(α)}(z)=sum_t C(n+α,n-t)(-z)^t/t!
        lag = [0] * (3 * nn + 1)
        for t in range(0, nn + 1):
            # n! C(n+α, n-t) v^{n-t}/t!
            lag[3 * (nn - t)] += Fraction(factorial(nn) * comb(nn + i + 1, nn - t), factorial(t))
        if trim(psub(lag, Sf)):
            ok_lag = False
rise_fail = []
for q in range(3, 10):
    for i in range(0, q - 2):
        nn = q - 1 - i
        Sr = [0] * (3 * nn + 1)
        for t in range(0, nn + 1):
            Sr[3 * t] = comb(q, t) * rising(nn, t)
        _, r2 = pdivmod(psub(NUM[q], pmul(W_poly(i), Sr)), b_poly(i))
        if r2:
            rise_fail.append((q, i))
report(ok_fall and ok_lag, 'T4.3.8-cong', 'Num_q≡W_i·S_{q,i} (mod b_i)，S_{q,i}=sum_t C(q,t)(q-1-i)^(t下降)x^{3t}=n!v^nL_n^{(i+1)}(-1/v)（2<=q<=15）')
report(bool(rise_fail), 'T4.3.8-notation', '若把 (q-1-i)_t 读作上升阶乘（C-3 节 (α)_n 的记号），同余不成立，例如 (q,i)=%s' % rise_fail[:3])

summary('audit_c4')
print('elapsed %.1fs' % (time.time() - t0))
