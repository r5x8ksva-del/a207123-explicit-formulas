# -*- coding: utf-8 -*-
"""r6：复核者对 C4-28（高次系数一般结构）的一般证明所做的计算核对。

证明要点（详见复核报告）：
  记 u := z/(1-z)，L := -ln(1-z)。由 C4-29 的闭式，Phi = exp(y^2 L + y^3 (u - L))，
  I = ∫_0^u exp(-y^2 ln(1+w) + y^3 (ln(1+w) - w)) dw，于是每个 A_j(z) := [y^j] A 属于 Q[u, L]。
  θ := z d/dz 满足 θ(u^a L^b) = a(u^a+u^{a+1})L^b + b u^{a+1} L^{b-1}；θ^d L^i 的首项（先比 u 次数再比 L 次数）
  是 i(d-1)! u^d L^{i-1}（d>=1），故 {θ^d L^i} 与单项式 {u^a L^b} 三角对应，Q[u,L] = span{θ^d L^i}，
  而 θ^d (L^i/i!) 正是序列 q^d c(q,i) 的指数母函数。指标 ι(u^a L^b) := b + [a>=1] 控制所需的最大 i。
本脚本：(1) 按上述推导把 A_j 精确展开为 Q[u,L] 的元素（含形式积分），并与真实 a_{q,j} 逐项比较；
        (2) 检查指标界 ι <= floor(j/2)+1；(3) 用三角算法把 A_j 化成 sum π_{j,i}(q) c(q,i)，与表 6 及
            r4 的拟合结果比较；(4) 核对 c(q, floor(j/2)+1) 的系数（偶 j 为 1，奇 j=2m+1 为 q-m，m>=1；j=1 为 0）。
"""
import sys
import time
from fractions import Fraction
from math import factorial, comb
from collections import defaultdict
from rlib import *

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
t0 = time.time()
Lg = Log('r6_structure')
JM = 14
QM = 60
Num = num_by_recurrence(QM)


def coef(q, e):
    p = Num[q]
    return p[e] if 0 <= e < len(p) else 0


# ---------- 二元多项式（dict: (deg1, deg2) -> Fraction）
def dadd(A, B, c=Fraction(1)):
    R = dict(A)
    for k, v in B.items():
        R[k] = R.get(k, 0) + c * v
        if R[k] == 0:
            del R[k]
    return R


def dmul(A, B):
    R = defaultdict(Fraction)
    for (a1, b1), v1 in A.items():
        for (a2, b2), v2 in B.items():
            R[(a1 + a2, b1 + b2)] += v1 * v2
    return {k: v for k, v in R.items() if v}


def dpow(A, n):
    R = {(0, 0): Fraction(1)}
    for _ in range(n):
        R = dmul(R, A)
    return R


ONE = {(0, 0): Fraction(1)}
U = {(1, 0): Fraction(1)}
LL = {(0, 1): Fraction(1)}
UmL = {(1, 0): Fraction(1), (0, 1): Fraction(-1)}


def Phi_n(n):
    """[y^n] exp(y^2 L + y^3 (u-L))，Q[u,L] 中。"""
    R = {}
    for b in range(0, n // 3 + 1):
        if (n - 3 * b) % 2:
            continue
        a = (n - 3 * b) // 2
        R = dadd(R, dmul(dpow(LL, a), dpow(UmL, b)), Fraction(1, factorial(a) * factorial(b)))
    return R


# 被积函数在 (v, ell) 变量下：v = 1+w，ell = ln(1+w)
mELL = {(0, 1): Fraction(-1)}
ELLmW = {(0, 1): Fraction(1), (1, 0): Fraction(-1), (0, 0): Fraction(1)}   # ell - w = ell - v + 1


def P_m(m):
    R = {}
    for b in range(0, m // 3 + 1):
        if (m - 3 * b) % 2:
            continue
        a = (m - 3 * b) // 2
        R = dadd(R, dmul(dpow(mELL, a), dpow(ELLmW, b)), Fraction(1, factorial(a) * factorial(b)))
    return R


_K = {}


def K(s, r):
    """∫_0^w (1+t)^s ell(t)^r dt，再代 w=u（即 1+w -> 1+u，ell -> L），返回 Q[u,L] 元素。
    (1+w)^s ell^r = [d/dw((1+w)^{s+1} ell^r) - r (1+w)^s ell^{r-1}]/(s+1)。"""
    if (s, r) in _K:
        return _K[(s, r)]
    onepu = dpow({(0, 0): Fraction(1), (1, 0): Fraction(1)}, s + 1)
    R = dmul(onepu, dpow(LL, r))
    if r == 0:
        R = dadd(R, ONE, Fraction(-1))
    R = {k: v / (s + 1) for k, v in R.items()}
    if r >= 1:
        R = dadd(R, K(s, r - 1), Fraction(-r, s + 1))
    _K[(s, r)] = R
    return R


def I_m(m):
    R = {}
    for (s, r), c in P_m(m).items():
        R = dadd(R, K(s, r), c)
    return R


PH = {n: Phi_n(n) for n in range(0, JM + 3)}
IM = {m: I_m(m) for m in range(0, JM + 1)}


def A_j(j):
    R = dadd(PH[j + 2], PH[j + 1])
    for n in range(0, j):
        R = dadd(R, dmul(PH[n], IM[j - 1 - n]), Fraction(-1))
    return R


# ---------- 把 Q[u,L] 元素展开为 z 的幂级数
Z = QM
useries = [Fraction(0)] + [Fraction(1)] * Z
Lseries = [Fraction(0)] + [Fraction(1, k) for k in range(1, Z + 1)]


def smul(a, b):
    r = [Fraction(0)] * (Z + 1)
    for i, x in enumerate(a):
        if x:
            for k in range(Z + 1 - i):
                if b[k]:
                    r[i + k] += x * b[k]
    return r


_pw = {}


def mono_series(a, b):
    if (a, b) in _pw:
        return _pw[(a, b)]
    if a == 0 and b == 0:
        s = [Fraction(1)] + [Fraction(0)] * Z
    elif a > 0:
        s = smul(mono_series(a - 1, b), useries)
    else:
        s = smul(mono_series(0, b - 1), Lseries)
    _pw[(a, b)] = s
    return s


def to_series(F):
    s = [Fraction(0)] * (Z + 1)
    for (a, b), c in F.items():
        ms = mono_series(a, b)
        for k in range(Z + 1):
            if ms[k]:
                s[k] += c * ms[k]
    return s


# ---------- θ 与三角化
def theta(F):
    R = defaultdict(Fraction)
    for (a, b), c in F.items():
        if a:
            R[(a, b)] += a * c
            R[(a + 1, b)] += a * c
        if b:
            R[(a + 1, b - 1)] += b * c
    return {k: v for k, v in R.items() if v}


_TH = {}


def thetaL(d, i):
    if (d, i) not in _TH:
        F = dpow(LL, i)
        for _ in range(d):
            F = theta(F)
        _TH[(d, i)] = F
    return _TH[(d, i)]


def stirling_rep(F):
    """F = sum κ_{d,i} θ^d L^i；返回 dict i -> π_i(q) 升幂系数，使 q![z^q]F = sum_i π_i(q) c(q,i)。"""
    F = dict(F)
    kap = defaultdict(Fraction)
    guard = 0
    while F:
        guard += 1
        if guard > 10000:
            raise RuntimeError('no termination')
        (a, b) = max(F.keys())          # 字典序：先 u 次数，再 L 次数
        c = F[(a, b)]
        if a == 0:
            d, i, lead = 0, b, Fraction(1)
        else:
            d, i, lead = a, b + 1, Fraction(i_ := b + 1) * factorial(a - 1)
        T = thetaL(d, i)
        assert max(T.keys()) == (a, b) and T[(a, b)] == lead, (a, b, d, i)
        kap[(d, i)] += c / lead
        F = dadd(F, T, -c / lead)
    pis = defaultdict(lambda: [])
    for (d, i), k in kap.items():
        poly = [Fraction(0)] * (d + 1)
        poly[d] = k * factorial(i)
        pis[i] = add(pis[i], poly)
    return {i: tr(p) for i, p in pis.items() if tr(p)}


C1 = stirling1(QM + 2)

ok_series, ok_index, ok_rep, ok_top = True, True, True, True
REPS = {}
for j in range(0, JM + 1):
    F = A_j(j)
    s = to_series(F)
    if s[0] != 0:
        ok_series = False
    for q in range(1, Z + 1):
        if s[q] * factorial(q) != coef(q, 3 * q - 2 - j):
            ok_series = False
            Lg.out('  A_%d series mismatch at q=%d' % (j, q))
            break
    idx = max(b + (1 if a >= 1 else 0) for (a, b) in F) if F else 0
    if idx > j // 2 + 1:
        ok_index = False
    rep = stirling_rep(F)
    REPS[j] = rep
    for q in range(1, Z + 1):
        val = sum(ev(p, Fraction(q)) * C1[q][i] for i, p in rep.items())
        if val != coef(q, 3 * q - 2 - j):
            ok_rep = False
            Lg.out('  stirling rep mismatch j=%d q=%d' % (j, q))
            break
    if max(rep.keys(), default=0) > j // 2 + 1:
        ok_index = False
    m = j // 2
    top = rep.get(m + 1, [])
    if j == 1:
        want = []
    elif j % 2 == 0:
        want = [Fraction(1)]
    else:
        want = [Fraction(-m), Fraction(1)]
    if tr(top) != want:
        ok_top = False
        Lg.out('  top coefficient j=%d: %s' % (j, top))
Lg.check('r6-Aj-series', ok_series, 'j<=%d：由闭式的 y 展开（Phi_n、P_m、形式积分 K(s,r)）得到的 A_j ∈ Q[u,L] 展开成 z 级数后 q![z^q]A_j == [x^{3q-2-j}]Num_q（q<=%d）' % (JM, Z))
Lg.check('r6-index', ok_index, 'j<=%d：A_j 的单项式指标 b+[a>=1] <= floor(j/2)+1，且 Stirling 表示只用到 c(q,i)，i<=floor(j/2)+1' % JM)
Lg.check('r6-rep', ok_rep, 'j<=%d：三角化得到的 sum_i π_{j,i}(q)c(q,i) 对 q<=%d 等于真实系数' % (JM, Z))
Lg.check('r6-top', ok_top, 'j<=%d：c(q,floor(j/2)+1) 的系数：偶 j 为 1；奇 j=2m+1 (m>=1) 为 q-m；j=1 为 0' % JM)

# 与表 6（j<=8）逐多项式比较
HF6 = {
    0: {1: [1]}, 1: {}, 2: {1: [-1, 1], 2: [1]}, 3: {1: [1, -1], 2: [-1, 1]}, 4: {1: [-1, 1], 2: [-1], 3: [1]},
    5: {1: [1, Fraction(-3, 2), Fraction(1, 2)], 2: [2, -1], 3: [-2, 1]},
    6: {1: [Fraction(-3, 2), Fraction(11, 4), Fraction(-5, 4)], 2: [-2, Fraction(1, 2), Fraction(1, 2)], 3: [0, -1], 4: [1]},
    7: {1: [Fraction(3, 2), Fraction(-9, 4), Fraction(3, 4)], 2: [2, -1], 3: [3, -1], 4: [-3, 1]},
    8: {1: [Fraction(-9, 4), Fraction(55, 24), Fraction(-1, 8), Fraction(1, 12)], 2: [Fraction(-5, 2), 2, -1],
        3: [-4, Fraction(3, 2), Fraction(1, 2)], 4: [2, -2], 5: [1]},
}
ok = True
for j, F in HF6.items():
    a = {i: tr([Fraction(c) for c in p]) for i, p in F.items()}
    if a != REPS[j]:
        ok = False
        Lg.out('  table6 vs derived j=%d: %s vs %s' % (j, a, REPS[j]))
Lg.check('r6-table6', ok, '由闭式 + 三角化独立推出的 π_{j,i} 与 c4.md 表 6（j<=8）逐多项式完全一致')
for j in range(9, JM + 1):
    Lg.out('# j=%d：%s' % (j, {i: [str(c) for c in p] for i, p in sorted(REPS[j].items())}))

# 单项式 u^a L^b 的序列确为 sum_{i<=b+[a>=1]} π_i(q)c(q,i)、deg π<=a（三角对应的直接核对）
ok = True
for a in range(0, 6):
    for b in range(0, 6):
        F = {(a, b): Fraction(1)}
        rep = stirling_rep(F)
        if max(rep.keys(), default=0) > b + (1 if a >= 1 else 0) or any(len(p) - 1 > a for p in rep.values()):
            ok = False
        s = to_series(F)
        for q in range(1, 40):
            if s[q] * factorial(q) != sum(ev(p, Fraction(q)) * C1[q][i] for i, p in rep.items()):
                ok = False
Lg.check('r6-monomials', ok, 'a,b<=5：u^a L^b 的系数序列 == sum_{i<=b+[a>=1]} π_i(q)c(q,i)，deg π_i<=a（q<40 逐项）')
Lg.close(t0)
