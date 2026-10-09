# -*- coding: utf-8 -*-
"""复核者 s17-b9b 的公共函数（只用标准库；不 import 项目里的任何代码）。

真值：U_k(m) = 长 k、取值于 {0..m}、每个相邻三元组 (a,b,c) 满足「b=c 或 a>=max(b,c)」的序列个数
（notes/原始任务说明.md 第 1 节 (b)）。
  brute_U        逐个枚举（只用于很小的 k、m）
  U_rows         U 的三项递推 U_k(m)=U_k(m-1)+U_{k-1}(m)+m U_{k-3}(m)，按 k 逐行滚动（m<=M）；
                 边界约定 U_0=U_{-1}=1、U_{-2}=0、U_k(-1)=0（k>=1），先与 brute_U 对照再用
  h_from_U       h_{k,i}=Σ_r (-1)^r C(k+1,r) U_k(i-r)（i<=M），一次卷积
  N_rows         N 三角递推 N(k,q)=N(k-1,q-1)+N(k-1,q)+(q-1)(N(k-3,q-2)+2N(k-3,q-1)+N(k-3,q))（q<=Q），按 k 滚动
  h_from_N       h_{k,i}=Σ_q N(k,q)(-1)^{i+1-q}C(k-q,i+1-q)，即 h_k(t)=Σ_q N(k,q)t^{q-1}(1-t)^{k-q}
  t17_rows       我自己写的 T1.7 递推（截断到 i<=I）：h_k=h_{k-1}+t(1-t)[(1-t)h'_{k-3}+(k-2)h_{k-3}]
  t17_full       同一递推，不截断（完整多项式）
  rho_bracket    y^3-y^2=j 的实根 ρ_j 的整数二分（宽度 2^-B），c_dec、rho_dec 为高精度十进制值
"""
import math
from decimal import Decimal as D, getcontext, localcontext
from fractions import Fraction as Fr
from itertools import product


# ------------------------------------------------------------------ 真值
def good(a, b, c):
    return b == c or (a >= b and a >= c)


def brute_U(k, m):
    if k <= 2:
        return (m + 1) ** k
    cnt = 0
    for s in product(range(m + 1), repeat=k):
        if all(good(s[i], s[i + 1], s[i + 2]) for i in range(k - 2)):
            cnt += 1
    return cnt


def pair_dp_U(K, m):
    """[U_0(m),...,U_K(m)]：以最后两个值为状态，逐个检查三元组条件（朴素，O(m^3)/步）。"""
    out = [1, m + 1, (m + 1) ** 2]
    cnt = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    for _ in range(3, K + 1):
        new = {}
        for (a, b), v in cnt.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
        cnt = new
        out.append(sum(cnt.values()))
    return out[:K + 1]


# ------------------------------------------------------------------ U 的三项递推（按 k 滚动）
def U_rows(K, M, mutate=None):
    """依次产生 (k, [U_k(0..M)])，k=0..K。mutate 只用于反向检查（把 m*U_{k-3} 换成 mutate(m)*U_{k-3}）。"""
    mult = (lambda m: m) if mutate is None else mutate
    one = [1] * (M + 1)
    zero = [0] * (M + 1)
    prev = {-3: zero, -2: zero, -1: one, 0: one}   # U_{-3} 不会用到（k>=1 时 k-3>=-2）
    yield 0, one[:]
    for k in range(1, K + 1):
        r1 = prev[k - 1]
        r3 = prev[k - 3]
        row = [0] * (M + 1)
        left = 0                                    # U_k(-1)=0
        for m in range(M + 1):
            left = left + r1[m] + mult(m) * r3[m]
            row[m] = left
        prev[k] = row
        prev.pop(k - 4, None)
        yield k, row


def binom_row_next(B):
    """B=[C(n,0..R)] -> [C(n+1,0..R)]。"""
    R = len(B) - 1
    return [B[0]] + [B[r] + B[r - 1] for r in range(1, R + 1)]


def h_from_U(Urow, Bsigned, imax):
    """h_{k,i}=Σ_{r<=i} (-1)^r C(k+1,r) U_k(i-r)，Bsigned[r]=(-1)^r C(k+1,r)。返回 i=0..imax。"""
    out = []
    for i in range(imax + 1):
        s = 0
        for r in range(i + 1):
            b = Bsigned[r]
            if b:
                s += b * Urow[i - r]
        out.append(s)
    return out


# ------------------------------------------------------------------ N 三角
def N_rows(K, Q):
    """依次产生 (k, [N(k,0..Q)])，k=0..K。N(0,0)=1，N(1,1)=1，N(2,1)=1，N(2,2)=2。"""
    base = {0: [1] + [0] * Q, 1: [0, 1] + [0] * (Q - 1), 2: [0, 1, 2] + [0] * (Q - 2)}
    prev = {}
    for k in range(0, K + 1):
        if k <= 2:
            row = base[k][:Q + 1]
        else:
            p1, p3 = prev[k - 1], prev[k - 3]
            row = [0] * (Q + 1)
            for q in range(1, Q + 1):
                t = (p3[q - 2] if q >= 2 else 0) + 2 * p3[q - 1] + p3[q]
                row[q] = p1[q - 1] + p1[q] + (q - 1) * t
        prev[k] = row
        prev.pop(k - 4, None)
        yield k, row


def h_from_N(k, Nrow, i):
    """h_{k,i}=Σ_{q=1}^{min(i+1,k)} N(k,q)(-1)^{i+1-q} C(k-q,i+1-q)（k>=1）。"""
    s = 0
    for q in range(1, min(i + 1, k) + 1):
        p = i + 1 - q
        c = math.comb(k - q, p)
        if c:
            s += (-c if p & 1 else c) * Nrow[q]
    return s


def h_from_N_all(k, Nrow, imax):
    """同上，i=0..imax 全部（逐个调用 math.comb，不做增量）。"""
    return [h_from_N(k, Nrow, i) for i in range(imax + 1)]


# ------------------------------------------------------------------ T1.7（自写）
def t17_rows(K, I, kshift=-2):
    """依次产生 (k, [h_{k,0..I}])；截断对 i<=I 精确（第 i 个系数只用到 h_{k-3} 的第 <=i 个系数）。
    kshift 只用于反向检查（把 (k-2) 换成 (k+kshift)）。"""
    rows = {}
    for k in range(0, K + 1):
        if k <= 1:
            row = [1] + [0] * I
        elif k == 2:
            row = [1, 1] + [0] * (I - 1)
        else:
            g = rows[k - 3]
            hp = rows[k - 1]
            # A_m = (m+1) g_{m+1} + (k-2-m) g_m，m=0..I-1；h_k[n] = hp[n] + A_{n-1} - A_{n-2}
            A = [(m + 1) * g[m + 1] + (k + kshift - m) * g[m] for m in range(I)]
            row = [hp[0]] + [hp[1] + A[0]] + [hp[n] + A[n - 1] - A[n - 2] for n in range(2, I + 1)]
        rows[k] = row
        rows.pop(k - 4, None)
        yield k, row


def t17_full(K):
    """依次产生 (k, h_k 的完整系数表)。"""
    rows = {}
    for k in range(0, K + 1):
        if k <= 1:
            h = [1]
        elif k == 2:
            h = [1, 1]
        else:
            g = rows[k - 3]
            hp = rows[k - 1]
            d = len(g) - 1
            A = [(m + 1) * (g[m + 1] if m + 1 <= d else 0) + (k - 2 - m) * g[m] for m in range(d + 1)]
            n_out = max(len(hp), d + 3)
            h = [0] * n_out
            for n in range(n_out):
                v = hp[n] if n < len(hp) else 0
                if 1 <= n <= d + 1:
                    v += A[n - 1]
                if 2 <= n <= d + 2:
                    v -= A[n - 2]
                h[n] = v
            while len(h) > 1 and h[-1] == 0:
                h.pop()
        rows[k] = h
        rows.pop(k - 4, None)
        yield k, h


# ------------------------------------------------------------------ ρ_j、c_j
def rho_bracket(j, B=256):
    """整数 n 使 ρ_j ∈ (n/2^B, (n+1)/2^B]（j>=1）；j=0 返回 (2^B, 2^B)，即 ρ_0=1。"""
    S = 1 << B
    if j == 0:
        return S, S
    lo, hi = S, max(2, j) * S          # f(lo)<j<=f(hi)，f(y)=y^3-y^2
    S3 = S ** 3
    target = j * S3
    def f_scaled(n):                   # S^3 f(n/S)
        return n * n * n - n * n * S
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if f_scaled(mid) < target:
            lo = mid
        else:
            hi = mid
    return lo, hi


def rho_fr(j, B=256):
    lo, hi = rho_bracket(j, B)
    return Fr(lo, 1 << B), Fr(hi, 1 << B)


def rho_dec(j, prec=100):
    B = int(prec * 3.33) + 16
    lo, hi = rho_bracket(j, B)
    with localcontext() as ctx:
        ctx.prec = prec + 10
        return D(hi) / D(1 << B)


def c_dec(j, prec=100):
    """c_j=ĝ_j(ρ_j)/(ρ_j^2+3j)，ĝ_j(y)=y^{3j+3}/j!+Σ_{l<j}(j-l)y^{3l+1}/l!；j=0 时为 1。"""
    if j == 0:
        return D(1)
    with localcontext() as ctx:
        ctx.prec = prec + 10
        r = rho_dec(j, prec + 10)
        u = r ** 3
        s = u ** (j + 1) / D(math.factorial(j))
        for l in range(j):
            s += (j - l) * r * u ** l / D(math.factorial(l))
        return s / (r * r + 3 * j)


def M_of(rho):
    return (rho / (rho - 1)) * math.sqrt((3 * rho - 2) / (3 * rho + 1))


def K_bound(i, X0='0.26', prec=50):
    """K_i:=D_i(ln A_i+ln ln A_i)，A_i=D_i/X0，D_i=ρ_i^2+3i 的严格上界（十进制）。
    ρ_i 取整数二分的上端（宽度 2^-200），D 的上界再加 1e-40；K(D) 在 A>e 时关于 D 递增；
    Decimal 的 ln 正确舍入，最后加 1e-30 的余量盖住 prec=50 的舍入误差。返回 (K_upper, D_upper)。"""
    lo, hi = rho_bracket(i, 200)
    with localcontext() as ctx:
        ctx.prec = prec
        rho_hi = D(hi) / D(1 << 200)
        Dd = rho_hi * rho_hi + 3 * i + D('1e-40')
        A = Dd / D(X0)
        assert A > D(3)
        K = Dd * (A.ln() + A.ln().ln()) + D('1e-30')
        return K, Dd


def lnbig(x):
    """正整数的自然对数（大整数安全）。"""
    b = x.bit_length()
    if b < 1000:
        return math.log(x)
    s = b - 900
    return math.log(x >> s) + s * math.log(2)


def parse_tau_table(path):
    """从 notes/18 §2 的代码块读出 τ_1..τ_300（只读文本，不执行任何代码）。"""
    txt = open(path, encoding='utf-8').read()
    start = txt.index('## 2. 推论 2')
    block = txt[start:txt.index('```', txt.index('```', start) + 3)]
    vals = []
    for line in block.splitlines():
        if line.startswith('i=') and ':' in line:
            vals += [int(x) for x in line.split(':', 1)[1].split(',')]
    return vals
