# -*- coding: utf-8 -*-
"""t2：逐条数值核对 s6-t436 证明中的引理（证明本身是书面的，这里只防止代数笔误）。
 L1  (1-z)^2 ∂_z A = (1-z+y^2 z) + (y^2(1-z)+y^3 z) A，A=Σ_{q>=1} R_q z^q/q!，R_q 直接取自 Num_q 的反转；
 L2  A_0=L，A_1=0，A_2=L^2/2+u-L；j>=3：θA_j = u A_{j-2} + u^2 A_{j-3}（写成整数序列恒等式）；
 L3  D G_{a,i} = U^aΛ^i，G_{a,i} 无常数项、权重 <= i+1，G_{2,i} ≡ UΛ^i - Λ^{i+1}/(i+1) (mod W_i)；
 L4  ev(P_j) = A_j（把 U->u、Λ->L 代入，作为 z 的幂级数逐项比较）；
 L5  P_j ∈ W_{⌊j/2⌋+1}；
 L6  U^aΛ^i - [t·C(t-1,a-1)/(i+1)](D) Λ^{i+1} ∈ N_i，并且分解 Σ p_k(D)Λ^k 精确还原 U^aΛ^i；
 L7  P_{2m} ≡ Λ^{m+1}/(m+1)! (mod W_m)；
 L8  P_{2m+1} ≡ -(m/(m+1)!) Λ^{m+1} + [m>=1] UΛ^m/m! (mod W_m)。
"""
import sys
sys.dont_write_bytecode = True
import time
from fractions import Fraction
from math import factorial
import s6lib as L

t0 = time.time()
ok_all = True


def report(name, ok, extra=''):
    global ok_all
    ok_all = ok_all and ok
    print('[%s] %s %s' % ('OK ' if ok else 'BAD', name, extra))


QN = 80
N = L.num_polys(QN)

# ---------------- L1：e.g.f. 的一阶 ODE（R_q 取自 Num_q 的反转，不经过 (R)）
def ypoly_add(*ps):
    n = max(len(p) for p in ps)
    return [sum((p[k] if k < len(p) else 0) for p in ps) for k in range(n)]

def yshift(p, e):
    return [0] * e + list(p)

def ysc(p, s):
    return [s * x for x in p]

alpha = [[Fraction(0)]]
for q in range(1, QN + 1):
    alpha.append([Fraction(x, factorial(q)) for x in reversed(N[q])])   # R_q/q!
ok = True
for n in range(0, QN):
    lhs = ypoly_add(ysc(alpha[n + 1], n + 1), ysc(alpha[n], -2 * n),
                    ysc(alpha[n - 1], n - 1) if n >= 1 else [0])
    rhs = ypoly_add([Fraction(1 if n == 0 else (-1 if n == 1 else 0))],
                    [0, 0, Fraction(1 if n == 1 else 0)],
                    yshift(alpha[n], 2),
                    ysc(yshift(alpha[n - 1], 2), -1) if n >= 1 else [0],
                    yshift(alpha[n - 1], 3) if n >= 1 else [0])
    m = max(len(lhs), len(rhs))
    lhs += [0] * (m - len(lhs)); rhs += [0] * (m - len(rhs))
    if lhs != rhs:
        ok = False
        print('   L1 fails at z^%d' % n)
        break
report('L1：(1-z)^2 A\' = (1-z+y^2 z) + (y^2(1-z)+y^3 z) A', ok, '(到 z^%d，全部 y 次数)' % (QN - 1))

# ---------------- L2：分量递推（整数序列形式）
QR, J = 300, 41
R = L.R_trunc(QR, J)
def a(q, j):
    if q == 0 or j < 0:
        return 0
    return R[q][j]
fact = [factorial(n) for n in range(QR + 1)]
# 基例：A_0 = L <=> a_{q,0}=(q-1)!；A_1=0；A_2 = L^2/2 + u - L <=> a_{q,2} = c(q,2) + q! - (q-1)!
c = L.stirling1_rec(QR, 3)
ok = all(a(q, 0) == c[q][1] for q in range(1, QR + 1)) and all(a(q, 1) == 0 for q in range(1, QR + 1)) \
     and all(a(q, 2) == c[q][2] + fact[q] - c[q][1] for q in range(1, QR + 1))
report('L2 基例 A_0=L，A_1=0，A_2=L^2/2+u-L', ok, '(q<=%d)' % QR)
# θA_j = u A_{j-2} + u^2 A_{j-3}： q a_{q,j} = Σ_{r<q} (q!/r!) a_{r,j-2} + Σ_{r<=q-2} (q-1-r)(q!/r!) a_{r,j-3}
ok = True
bad = None
for j in range(3, J):
    for q in range(1, QR + 1):
        s = 0
        for r in range(1, q):
            s += (fact[q] // fact[r]) * (a(r, j - 2) + (q - 1 - r) * a(r, j - 3))
        if q * a(q, j) != s:
            ok = False; bad = (j, q); break
    if not ok:
        break
report('L2 递推 θA_j = u A_{j-2} + u^2 A_{j-3}', ok, '(3<=j<=%d, q<=%d) %s' % (J - 1, QR, bad or ''))

# ---------------- L3：D^{-1}
ok = True
for aa in range(1, 21):
    for i in range(0, 21):
        g = L.G(aa, i)
        if L.bp_D(g) != {(aa, i): Fraction(1)}:
            ok = False; print('   D G fails', aa, i)
        if (0, 0) in g or L.bp_weight(g) > i + 1:
            ok = False; print('   G const/weight fails', aa, i)
    if not ok:
        break
report('L3 D G_{a,i}=U^aΛ^i，无常数项，权重<=i+1', ok, '(a<=20, i<=20)')
ok = True
for i in range(0, 21):
    diff = L.bp_add(L.G(2, i), {(1, i): Fraction(1), (0, i + 1): Fraction(-1, i + 1)}, -1)
    if L.bp_weight(diff) > i:
        ok = False; print('   G_2 top fails', i)
report('L3(iv) G_{2,i} ≡ UΛ^i - Λ^{i+1}/(i+1) mod W_i', ok, '(i<=20)')

# ---------------- L5：权重；L4：ev(P_j)=A_j
JP = 40
P = L.P_family(JP)
ok = all(L.bp_weight(P[j]) <= j // 2 + 1 and (0, 0) not in P[j] for j in range(JP + 1))
report('L5 P_j ∈ W_{⌊j/2⌋+1} 且无常数项', ok, '(j<=%d)' % JP)
ok = all(L.bp_weight(P[j]) == j // 2 + 1 for j in range(JP + 1) if j != 1)
report('   权重恰好等于 ⌊j/2⌋+1（j≠1）', ok, '(j<=%d)' % JP)
print('   P_3 =', sorted(P[3].items()))
print('   P_4 =', sorted(P[4].items()))

Z = 60
useries = L.u_series(Z)
Lseries = L.L_series(Z)
upow = [[Fraction(1)] + [Fraction(0)] * Z]
for _ in range(15):
    upow.append(L.ser_mul(upow[-1], useries, Z))
Lpow = [[Fraction(1)] + [Fraction(0)] * Z]
for _ in range(25):
    Lpow.append(L.ser_mul(Lpow[-1], Lseries, Z))
mon_cache = {}
def mon_series(aa, i):
    if (aa, i) not in mon_cache:
        mon_cache[(aa, i)] = L.ser_mul(upow[aa], Lpow[i], Z)
    return mon_cache[(aa, i)]
ok = True
JE = 20
for j in range(JE + 1):
    ser = [Fraction(0)] * (Z + 1)
    for (aa, i), v in P[j].items():
        ms = mon_series(aa, i)
        for n in range(Z + 1):
            ser[n] += v * ms[n]
    for qq in range(0, Z + 1):
        target = Fraction(L.a_from_num(N, qq, j), factorial(qq)) if qq >= 1 else 0
        if ser[qq] != target:
            ok = False; print('   ev(P_j) != A_j at j=%d, z^%d' % (j, qq)); break
    if not ok:
        break
report('L4 ev(P_j) = A_j（逐项比较 z 的系数，A_j 取自 Num_q）', ok, '(j<=%d, 到 z^%d)' % (JE, Z))

# ---------------- L6：单项式的分解
ok = True
for aa in range(1, 13):
    for i in range(0, 12):
        mono = {(aa, i): Fraction(1)}
        p, steps, const = L.decompose(mono, i + 1)
        expect = L.tp_scale(L.tp_mul([Fraction(0), Fraction(1)], L.binom_tminus1(aa)), Fraction(1, i + 1))
        if L.tp_trim(p[i + 1]) != L.tp_trim(expect) or const != 0:
            ok = False; print('   L6 top fails', aa, i)
        recon = {}
        for k in range(i + 2):
            if p[k]:
                recon = L.bp_add(recon, L.apply_tpoly_D(p[k], k))
        if recon != mono:
            ok = False; print('   L6 recon fails', aa, i)
    if not ok:
        break
report('L6 U^aΛ^i 的分解：顶层系数 t·C(t-1,a-1)/(i+1)，精确还原', ok, '(a<=12, i<=11)')

# ---------------- L7, L8
ok7 = True
for m in range(0, JP // 2 + 1):
    diff = L.bp_add(P[2 * m], {(0, m + 1): Fraction(1, factorial(m + 1))}, -1)
    if L.bp_weight(diff) > m:
        ok7 = False; print('   L7 fails m=', m)
report('L7 P_{2m} ≡ Λ^{m+1}/(m+1)! mod W_m', ok7, '(m<=%d)' % (JP // 2))
ok8 = True
for m in range(0, (JP - 1) // 2 + 1):
    tgt = {(0, m + 1): Fraction(-m, factorial(m + 1))}
    if m >= 1:
        tgt[(1, m)] = Fraction(1, factorial(m))
    tgt = {k: v for k, v in tgt.items() if v != 0}
    diff = L.bp_add(P[2 * m + 1], tgt, -1)
    if L.bp_weight(diff) > m:
        ok8 = False; print('   L8 fails m=', m)
report('L8 P_{2m+1} ≡ -(m/(m+1)!)Λ^{m+1} + [m>=1]UΛ^m/m! mod W_m', ok8, '(m<=%d)' % ((JP - 1) // 2))

print('ALL_OK' if ok_all else 'SOME_BAD', '  time %.1fs' % (time.time() - t0))
