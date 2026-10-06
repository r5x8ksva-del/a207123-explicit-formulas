# -*- coding: utf-8 -*-
"""s6-t436 复核 T4.3(6) 用的公共函数。只用 Python 标准库（fractions、math）。

内容：
  * Num_q 的三项递推（x 方向，整数系数）与反转多项式 R_q；
  * R_q 的反转递推 (R)（y 方向，可截断到 y^J）；
  * 第一类无符号 Stirling 数：按定义 L^i/i! 的 e.g.f. 展开，以及递推 c(q+1,i)=q c(q,i)+c(q,i-1)；
  * t 的一元有理多项式（系数为 Fraction 的列表，下标 = 次数）；
  * Q[U,Λ] 的双变量多项式（dict {(a,i): Fraction} 表示 U^a Λ^i），导子 D（DU=U+U^2，DΛ=U）、
    D 的逆 G_{a,i}=D^{-1}(U^aΛ^i)、权重、分解 P=Σ_i p_i(D) Λ^i；
  * 模素数的高斯消元、CRT 与有理重构（只用于“搜索”系数，最后一律用精确有理数复验）。
被各脚本 import；各脚本开头设置 sys.dont_write_bytecode=True，不在仓库里留下 __pycache__。
"""
import sys
sys.dont_write_bytecode = True
try:
    sys.stdout.reconfigure(encoding='utf-8')   # 日志统一用 UTF-8（与仓库里其他复核日志一致）
except Exception:
    pass
from fractions import Fraction
from math import factorial, isqrt

# ---------------------------------------------------------------- Num_q 与 R_q

def num_polys(Q):
    """按报告的递推构造 Num_1..Num_Q（整数系数列表，下标 = x 的次数，长度 3q-1）。
    Num_1 = x，Num_2 = 2x^2 + x^4，q>=3：
    Num_q = (x + 2(q-1)x^3) Num_{q-1} + (q-1) x^3 (1 - x - (q-2)x^3) Num_{q-2}。"""
    N = [None] * (Q + 1)
    N[1] = [0, 1]
    if Q >= 2:
        N[2] = [0, 0, 2, 0, 1]
    for q in range(3, Q + 1):
        A, B = N[q - 1], N[q - 2]
        res = [0] * (3 * q - 1)            # 次数 <= 3q-2
        for k, c in enumerate(A):
            if c:
                res[k + 1] += c
                res[k + 3] += 2 * (q - 1) * c
        for k, c in enumerate(B):
            if c:
                cc = (q - 1) * c
                res[k + 3] += cc
                res[k + 4] -= cc
                res[k + 6] -= (q - 2) * cc
        N[q] = res
    return N


def a_from_num(N, q, j):
    """a_{q,j} := [x^{3q-2-j}] Num_q（3q-2-j<0 时为 0）。"""
    d = 3 * q - 2 - j
    if d < 0:
        return 0
    return N[q][d]


def R_trunc(Q, J):
    """反转递推 (R)：R_1=1，R_2=1+2y^2，q>=3：
    R_q = (y^2 + 2(q-1)) R_{q-1} + (q-1)(y^3 - y^2 - (q-2)) R_{q-2}，只保留 y^0..y^{J-1}。"""
    assert J >= 3
    R = [None] * (Q + 1)
    R[1] = [1] + [0] * (J - 1)
    if Q >= 2:
        R[2] = [1, 0, 2] + [0] * (J - 3)
    for q in range(3, Q + 1):
        A, B = R[q - 1], R[q - 2]
        res = [0] * J
        for j in range(J):
            v = 2 * (q - 1) * A[j] - (q - 1) * (q - 2) * B[j]
            if j >= 2:
                v += A[j - 2] - (q - 1) * B[j - 2]
            if j >= 3:
                v += (q - 1) * B[j - 3]
            res[j] = v
        R[q] = res
    return R

# ---------------------------------------------------------------- 一元形式幂级数（截断）

def ser_mul(F, G, n):
    """截断到 z^n 的 Cauchy 积（系数为数）。"""
    H = [0] * (n + 1)
    for a, fa in enumerate(F[: n + 1]):
        if fa:
            for b in range(0, n + 1 - a):
                gb = G[b] if b < len(G) else 0
                if gb:
                    H[a + b] += fa * gb
    return H


def L_series(n):
    """L = -ln(1-z) := Σ_{m>=1} z^m/m（形式对数的定义）。"""
    return [Fraction(0)] + [Fraction(1, m) for m in range(1, n + 1)]


def u_series(n):
    """u = z/(1-z) = Σ_{m>=1} z^m。"""
    return [Fraction(0)] + [Fraction(1)] * n

# ---------------------------------------------------------------- Stirling 数

def stirling1_rec(Q, I):
    """c(q,i)，0<=q<=Q，0<=i<=I，按 c(0,0)=1、c(q+1,i)=q c(q,i)+c(q,i-1)。"""
    c = [[0] * (I + 1) for _ in range(Q + 1)]
    c[0][0] = 1
    for q in range(Q):
        c[q + 1][0] = q * c[q][0]
        for i in range(1, I + 1):
            c[q + 1][i] = q * c[q][i] + c[q][i - 1]
    return c


def stirling1_egf(Q, I):
    """按定义：Σ_q c(q,i) z^q/q! = L^i/i!，直接展开幂级数取系数。"""
    L = L_series(Q)
    c = [[0] * (I + 1) for _ in range(Q + 1)]
    P = [Fraction(1)] + [Fraction(0)] * Q
    for i in range(I + 1):
        for q in range(Q + 1):
            v = Fraction(P[q]) * factorial(q) / factorial(i)
            assert v.denominator == 1
            c[q][i] = v.numerator
        P = ser_mul(P, L, Q)
    return c

# ---------------------------------------------------------------- t 的一元多项式（Fraction 系数）

def tp_trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def tp_add(p, q):
    n = max(len(p), len(q))
    return tp_trim([(p[k] if k < len(p) else 0) + (q[k] if k < len(q) else 0) for k in range(n)])


def tp_scale(p, s):
    return tp_trim([s * x for x in p])


def tp_mul(p, q):
    if not p or not q:
        return []
    r = [Fraction(0)] * (len(p) + len(q) - 1)
    for a, x in enumerate(p):
        if x:
            for b, y in enumerate(q):
                if y:
                    r[a + b] += x * y
    return tp_trim(r)


def tp_eval(p, x):
    v = 0
    for c in reversed(p):
        v = v * x + c
    return v


def tp_str(p, var='q'):
    p = tp_trim(p)
    if not p:
        return '0'
    terms = []
    for d in range(len(p) - 1, -1, -1):
        c = p[d]
        if c == 0:
            continue
        cs = str(c)
        if d == 0:
            terms.append(cs)
        else:
            mon = var if d == 1 else '%s^%d' % (var, d)
            if c == 1:
                terms.append(mon)
            elif c == -1:
                terms.append('-' + mon)
            else:
                terms.append('(%s)*%s' % (cs, mon))
    s = ' + '.join(terms)
    return s.replace('+ -', '- ')


def binom_tminus1(a):
    """C(t-1, a-1) 作为 t 的多项式（a>=1）：Π_{r=1}^{a-1}(t-r)/(a-1)!。"""
    p = [Fraction(1)]
    for r in range(1, a):
        p = tp_mul(p, [Fraction(-r), Fraction(1)])
    return tp_scale(p, Fraction(1, factorial(a - 1)))

# ---------------------------------------------------------------- Q[U,Λ]：dict {(a,i): Fraction}

def bp_add(P, Q_, s=1):
    R = dict(P)
    for k, v in Q_.items():
        R[k] = R.get(k, 0) + s * v
        if R[k] == 0:
            del R[k]
    return R


def bp_scale(P, s):
    if s == 0:
        return {}
    return {k: s * v for k, v in P.items()}


def bp_mulU(P, e):
    return {(a + e, i): v for (a, i), v in P.items()}


def bp_D(P):
    """导子 D：D(U^a Λ^i) = a U^a Λ^i + a U^{a+1} Λ^i + i U^{a+1} Λ^{i-1}。"""
    R = {}
    for (a, i), v in P.items():
        if a:
            R[(a, i)] = R.get((a, i), 0) + a * v
            R[(a + 1, i)] = R.get((a + 1, i), 0) + a * v
        if i:
            R[(a + 1, i - 1)] = R.get((a + 1, i - 1), 0) + i * v
    return {k: v for k, v in R.items() if v != 0}


_G = {}


def G(a, i):
    """G_{a,i} = D^{-1}(U^a Λ^i)（a>=1）：G_{1,i}=Λ^{i+1}/(i+1)，
    G_{a+1,i} = (U^aΛ^i - a G_{a,i} - i G_{a+1,i-1})/a。"""
    key = (a, i)
    if key in _G:
        return _G[key]
    assert a >= 1 and i >= 0
    if a == 1:
        res = {(0, i + 1): Fraction(1, i + 1)}
    else:
        b = a - 1
        res = {(b, i): Fraction(1)}
        res = bp_add(res, G(b, i), -b)
        if i >= 1:
            res = bp_add(res, G(a, i - 1), -i)
        res = bp_scale(res, Fraction(1, b))
    _G[key] = res
    return res


def bp_Dinv(P):
    """D^{-1}：U·Q[U,Λ] -> 无常数项的多项式。要求每个单项式都含 U。"""
    R = {}
    for (a, i), v in P.items():
        assert a >= 1, 'D^{-1} 只对 U 的倍式定义'
        R = bp_add(R, G(a, i), v)
    return R


def wt(a, i):
    """权重：wt(Λ^i)=i，wt(U^aΛ^i)=i+1（a>=1）。"""
    return i + (1 if a >= 1 else 0)


def bp_weight(P):
    return max((wt(a, i) for (a, i) in P), default=-1)


def P_family(Jmax):
    """P_0=Λ，P_1=0，P_2=Λ^2/2+U-Λ，j>=3：P_j = D^{-1}(U P_{j-2} + U^2 P_{j-3})。"""
    P = [None] * (Jmax + 1)
    P[0] = {(0, 1): Fraction(1)}
    if Jmax >= 1:
        P[1] = {}
    if Jmax >= 2:
        P[2] = {(0, 2): Fraction(1, 2), (1, 0): Fraction(1), (0, 1): Fraction(-1)}
    for j in range(3, Jmax + 1):
        S = bp_add(bp_mulU(P[j - 2], 1), bp_mulU(P[j - 3], 2))
        P[j] = bp_Dinv(S)
    return P


def DpowLam(k, dmax):
    """[D^0 Λ^k, D^1 Λ^k, ..., D^dmax Λ^k]。"""
    out = [{(0, k): Fraction(1)}]
    for _ in range(dmax):
        out.append(bp_D(out[-1]))
    return out


def apply_tpoly_D(s, k):
    """s(D) Λ^k。"""
    pw = DpowLam(k, max(len(s) - 1, 0))
    R = {}
    for d, c in enumerate(s):
        if c:
            R = bp_add(R, pw[d], c)
    return R


def top_symbol(P, k):
    """对 P ∈ W_k（k>=1）给出 s(t) = [Λ^k]P + Σ_{a>=1} [U^aΛ^{k-1}]P · t·C(t-1,a-1)/k，
    使 P - s(D)Λ^k ∈ W_{k-1}（引理 6）。"""
    s = []
    c0 = P.get((0, k), 0)
    if c0:
        s = tp_add(s, [Fraction(c0)])
    for (a, i), v in P.items():
        if a >= 1 and i == k - 1:
            g = tp_mul([Fraction(0), Fraction(1)], binom_tminus1(a))
            s = tp_add(s, tp_scale(g, Fraction(v) / k))
    return s


def decompose(P, K):
    """把 P ∈ W_K 写成 Σ_{i=0}^K p_i(D) Λ^i；返回 (p 列表, 每一步残差的权重, 最后的常数)。
    每一步都核对残差权重确实下降（引理 6 的数值核对）。"""
    assert bp_weight(P) <= K
    p = [[] for _ in range(K + 1)]
    cur = dict(P)
    steps = []
    for k in range(K, 0, -1):
        s = top_symbol(cur, k)
        p[k] = s
        cur = bp_add(cur, apply_tpoly_D(s, k), -1)
        w = bp_weight(cur)
        steps.append(w)
        assert w <= k - 1, ('残差权重没有下降', k, w)
    const = cur.get((0, 0), 0)
    assert all(key == (0, 0) for key in cur), cur
    if const:
        p[0] = [Fraction(const)]
    return p, steps, const

# ---------------------------------------------------------------- 模素数线性代数、CRT、有理重构

def is_probable_prime(n):
    if n < 2:
        return False
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for p in small:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:          # 对 n < 3.3e24 是确定性的
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def primes_below(start, count):
    out = []
    n = start
    while len(out) < count:
        n -= 1
        if is_probable_prime(n):
            out.append(n)
    return out


def solve_mod(M, b, p):
    """Gauss-Jordan 模 p。返回 ('ok', 解) / ('rankdef', 列号) / ('inconsistent', None)。"""
    m, n = len(M), len(M[0])
    A = [[x % p for x in row] + [bi % p] for row, bi in zip(M, b)]
    r = 0
    for c in range(n):
        pr = None
        for i in range(r, m):
            if A[i][c]:
                pr = i
                break
        if pr is None:
            return ('rankdef', c)
        A[r], A[pr] = A[pr], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [(x * inv) % p for x in A[r]]
        rowr = A[r]
        for i in range(m):
            if i != r:
                f = A[i][c]
                if f:
                    A[i] = [(x - f * y) % p for x, y in zip(A[i], rowr)]
        r += 1
    for i in range(r, m):
        if A[i][n] % p:
            return ('inconsistent', None)
    return ('ok', [A[i][n] for i in range(n)])


def crt_pair(r1, m1, r2, m2):
    t = ((r2 - r1) * pow(m1, -1, m2)) % m2
    return (r1 + m1 * t) % (m1 * m2), m1 * m2


def ratrec(x, M):
    """有理重构：找 a/b，a ≡ b x (mod M)，|a|,|b| <= sqrt(M/2)。失败返回 None。"""
    Nb = isqrt(M // 2)
    r0, r1 = M, x % M
    s0, s1 = 0, 1
    while r1 > Nb:
        qq = r0 // r1
        r0, r1 = r1, r0 - qq * r1
        s0, s1 = s1, s0 - qq * s1
    if s1 == 0 or abs(s1) > Nb:
        return None
    return Fraction(r1, s1)
