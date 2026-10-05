# -*- coding: utf-8 -*-
"""check_c4.py —— 子方向 C-4：近对角线 D(k,d)=N(k,k-d) 与 (C7) 分子 Num_q 的正式核对模块。

契约：从任意目录用 `py -3.14 <路径>` 运行；sys.path 插入 code 目录导入 core / polylib（只读使用）；
每条结论打印一行 `PASS <id> <描述>` 或 `FAIL <id> <描述>`；最后一行 `SUMMARY c4 pass=<n> fail=<n>`；
全部通过时退出码 0。全程只用精确整数 / Fraction（无浮点）。

「原始定义」的落脚点：core.U_fast_table（高度向量 DP，第 1 节 (b) 的直接实现）+ core.N_from_U（容斥），
core.N_brute（按定义 DFS 枚举合法词），core.U_multichain（多重链定义），core.U_list（提示词参考实现）。
"""
import sys
import os
import time
from fractions import Fraction
from math import comb, factorial
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(HERE)
sys.path.insert(0, CODE)
from core import (U_fast_table, U_list, U_multichain, N_from_U, N_brute,  # noqa: E402
                  stirling2_table, PROMPT_TABLE)
from polylib import (trim, padd, psub, pscale, pmul, pshift, peval, pdiv,  # noqa: E402
                     pgcd, series_mul, interpolate, P_poly, b_poly)

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
T0 = time.time()
RESULTS = []


def report(cid, ok, desc):
    print(('PASS' if ok else 'FAIL') + ' ' + cid + ' ' + desc, flush=True)
    RESULTS.append(bool(ok))


# =====================================================================
# 公共工具
# =====================================================================
def kshift(p, s):
    """p(k+s) 的系数（升幂，Fraction）。"""
    res = []
    for a in reversed(p):
        res = padd(pmul(res, [Fraction(s), Fraction(1)]), [Fraction(a)])
    return trim(res)


def pv(p, x):
    return peval([Fraction(a) for a in p], Fraction(x))


def binom_poly(c, n):
    """C(k+c, n) 作为 k 的多项式。"""
    p = [Fraction(1)]
    for i in range(n):
        p = pmul(p, [Fraction(c - i), Fraction(1)])
    return pscale(p, Fraction(1, factorial(n)))


def Cplus(n, r):
    """组合意义的二项式：n 元集合的 r 元子集数（n<0 时为 0）。"""
    if n < 0 or r < 0 or r > n:
        return 0
    return comb(n, r)


def newton(p, base, deg):
    vals = [pv(p, base + i) for i in range(deg + 1)]
    out = []
    for _ in range(deg + 1):
        out.append(vals[0])
        vals = [vals[j + 1] - vals[j] for j in range(len(vals) - 1)]
    return out


def euler2(n):
    """二阶 Euler 数 <<a,k>>，0<=a<=n。"""
    E = [[0] * (n + 2) for _ in range(n + 1)]
    E[0][0] = 1
    for a in range(1, n + 1):
        for k in range(0, a):
            E[a][k] = (k + 1) * E[a - 1][k] + ((2 * a - 1 - k) * E[a - 1][k - 1] if k >= 1 else 0)
    return E


def stirling1_table(nmax):
    c = [[0] * (nmax + 2) for _ in range(nmax + 1)]
    c[0][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            c[n][k] = (n - 1) * c[n - 1][k] + c[n - 1][k - 1]
    return c


# =====================================================================
# 0. 数据：N 三角（定义 DP + 容斥）与（已证明的）三角递推
# =====================================================================
K = 60
TU = U_fast_table(K, K - 1)                       # U_k(m)，k<=60, m<=59
ND = [[0] * (K + 6) for _ in range(K + 1)]
for k in range(K + 1):
    for q in range(0, k + 1):
        ND[k][q] = N_from_U(TU, k, q)


def N_table_rec(KK):
    N = [[0] * (KK + 6) for _ in range(KK + 1)]
    N[0][0] = 1
    N[1][1] = 1
    N[2][1], N[2][2] = 1, 2

    def g(k, q):
        if k < 0 or q < 0 or q > k + 3:
            return 0
        return N[k][q]
    for k in range(3, KK + 1):
        for q in range(1, k + 1):
            r = q - 1
            N[k][q] = g(k - 1, q - 1) + g(k - 1, q) + r * (g(k - 3, q - 2) + 2 * g(k - 3, q - 1) + g(k - 3, q))
    return N


NR = N_table_rec(K)


def D(N, k, d):
    q = k - d
    if k < 0 or q < 0 or q > k:
        return 0
    return N[k][q]


# ---- 0a. DP 本身锚定到原始定义（多重链 / 参考实现 / 提示词校验表）
_UL = {m: U_list(m, 20) for m in range(0, 11)}
ok = all(TU[k][m] == _UL[m][k] for m in range(0, 11) for k in range(0, 21))
ok = ok and all(TU[k][m] == U_multichain(k, m) for k in range(1, 7) for m in range(0, 6))
ok = ok and all(TU[k][m] == PROMPT_TABLE[k][m] for k in range(1, 11) for m in range(0, 7))
report('c4-U-anchor', ok, 'U_fast_table == U_list(参考实现, k<=20,m<=10) == U_multichain(多重链, k<=6,m<=5) == 提示词校验表(k<=10,m<=6)')

# ---- 0b. N 三角递推（c4.md §1 已证明）与定义 DP 容斥一致
ok = all(NR[k][q] == ND[k][q] for k in range(K + 1) for q in range(0, k + 1))
report('c4-N-rec-dp', ok, 'N 三角递推(k>=3)+初值 == 高度DP+容斥 的 N(k,q)，全部 0<=q<=k<=60')

# ---- 0c. N 与按定义 DFS 枚举一致
ok = True
for k in range(1, 9):
    br = N_brute(k)
    if any(br.get(q, 0) != ND[k][q] for q in range(0, k + 1)):
        ok = False
report('c4-N-dfs', ok, 'N(k,q) == 按定义 DFS 枚举合法满射词（core.N_brute），k<=8')

# =====================================================================
# 1. 近对角线 D(k,d) = N(k,k-d)
# =====================================================================
# ---- 1a. D 递推
ok = True
for k in range(3, K + 1):
    for d in range(0, k):
        rhs = D(ND, k - 1, d) + D(ND, k - 1, d - 1) + (k - d - 1) * (
            D(ND, k - 3, d - 1) + 2 * D(ND, k - 3, d - 2) + D(ND, k - 3, d - 3))
        if rhs != D(ND, k, d):
            ok = False
report('c4-D-rec', ok, 'D(k,d)=D(k-1,d)+D(k-1,d-1)+(k-d-1)[D(k-3,d-1)+2D(k-3,d-2)+D(k-3,d-3)]，3<=k<=60, 0<=d<=k-1（对 DP 表）')

# ---- 1b. d=0,1
ok = all(D(ND, k, 0) == 2 for k in range(2, K + 1)) and D(ND, 1, 0) == 1 and D(ND, 0, 0) == 1
report('c4-D0', ok, 'D(k,0)=N(k,k)=2 (2<=k<=60)；例外 D(1,0)=1, D(0,0)=1（对 DP 表）')
ok = all(D(ND, k, 1) == k * k - k - 4 for k in range(4, K + 1)) and D(ND, 3, 1) == 4 and D(ND, 2, 1) == 1
report('c4-D1', ok, 'D(k,1)=N(k,k-1)=k^2-k-4 (4<=k<=60)；例外 D(2,1)=1(多项式值-2), D(3,1)=4(多项式值2)')

# ---- 1c. 构造性归纳：p_d(k) = D(2d+2,d) + sum_{j=2d+3}^k R_d(j)，并核对多项式恒等式
DMAX = 12
PD = {-3: [], -2: [], -1: []}
ok_id, ok_deg, ok_lead = True, True, True
for d in range(0, DMAX + 1):
    Rd = padd(kshift(PD[d - 1], -1),
              pmul([Fraction(-(d + 1)), Fraction(1)],
                   padd(padd(kshift(PD[d - 1], -3), pscale(kshift(PD[d - 2], -3), 2)), kshift(PD[d - 3], -3))))
    base = 2 * d + 2
    xs = [base]
    ys = [Fraction(D(NR, base, d))]
    for t in range(1, 2 * d + 3):
        xs.append(base + t)
        ys.append(ys[-1] + pv(Rd, base + t))
    p = interpolate(xs, ys)
    PD[d] = p
    # 恒等式 p(k)-p(k-1) == R_d(k)（作为 k 的多项式，精确 Fraction）
    if trim(psub(p, kshift(p, -1))) != trim(Rd):
        ok_id = False
    if len(p) - 1 != 2 * d:
        ok_deg = False
    if p[-1] != Fraction(2, 2 ** d * factorial(d)):
        ok_lead = False
report('c4-pd-identity', ok_id, 'd<=12：p_d(k)-p_d(k-1) == p_{d-1}(k-1)+(k-d-1)[p_{d-1}(k-3)+2p_{d-2}(k-3)+p_{d-3}(k-3)] 作为多项式恒等（Fraction 精确）')
report('c4-pd-degree-lead', ok_deg and ok_lead, 'd<=12：deg p_d = 2d，首项系数 = 2/(2^d d!)')

# ---- 1d. 公式表（c4.md 表 1，d<=5）与构造结果一致
P_TABLE = {
    0: (1, [2]),
    1: (1, [1, -1, -4]),
    2: (4, [1, -10, 43, -98, 164]),
    3: (24, [1, -27, 331, -2225, 8560, -17392, 11088]),
    4: (192, [1, -52, 1242, -17280, 151217, -845644, 2926356, -5702176, 5014464]),
    5: (1920, [1, -85, 3350, -79370, 1241073, -13308173, 98708360, -498528820, 1637903536,
               -3158022432, 2686170240]),
}
ok = True
for d, (den, cs) in P_TABLE.items():
    p = [Fraction(c, den) for c in reversed(cs)]
    if trim(p) != trim(PD[d]):
        ok = False
    if den != (2 ** (d - 1) * factorial(d) if d >= 1 else 1):
        ok = False
report('c4-pd-table', ok, 'c4.md 表1 的 p_d (d<=5，分母 2^{d-1}d!) == 构造性归纳得到的多项式')

# ---- 1e. 门槛：对 DP 表核对 D(k,d)=p_d(k) (2d+2<=k<=60)，并且 d+1<=k<=2d+1 全是例外；两个缺陷闭式
ok_thr, ok_exc, ok_e1, ok_e0 = True, True, True, True
for d in range(0, DMAX + 1):
    for k in range(2 * d + 2, K + 1):
        if pv(PD[d], k) != D(ND, k, d):
            ok_thr = False
    for k in range(d + 1, 2 * d + 2):
        if pv(PD[d], k) == D(ND, k, d):
            ok_exc = False
    if D(ND, 2 * d + 1, d) - pv(PD[d], 2 * d + 1) != (-1) ** (d + 1) * factorial(d + 1):
        ok_e1 = False
    if D(ND, 2 * d, d) - pv(PD[d], 2 * d) != Fraction((-1) ** (d + 1) * factorial(d + 2), 2):
        ok_e0 = False
report('c4-pd-threshold', ok_thr, 'd<=12：D(k,d)=p_d(k) 对全部 2d+2<=k<=60 成立（对 DP 表）')
report('c4-pd-exceptions', ok_exc, 'd<=12：门槛以下 d+1<=k<=2d+1 的每个 k 都是例外（D(k,d)!=p_d(k)），故门槛恰为 2d+2')
report('c4-defect-closed', ok_e1 and ok_e0, 'd<=12：D(2d+1,d)-p_d(2d+1)=(-1)^{d+1}(d+1)!，D(2d,d)-p_d(2d)=(-1)^{d+1}(d+2)!/2')

# ---- 1e'. 次首项系数与平移后单项式系数
ok = True
for d in range(1, DMAX + 1):
    cd = Fraction(2, 2 ** d * factorial(d))
    if PD[d][-2] != -(4 * d * d - 3 * d) * cd:
        ok = False
report('c4-pd-second', ok, '1<=d<=12：p_d(k) = (2/(2^d d!)) (k^{2d} - (4d^2-3d) k^{2d-1} + ...)（次首项系数）')
ok = True
for d in range(0, DMAX + 1):
    ps = kshift(PD[d], 2 * d + 1)
    if not all(c > 0 for c in ps):
        ok = False
    if d >= 1 and ps[-2] != 5 * d * ps[-1]:
        ok = False
report('c4-pd-shiftpos', ok, 'd<=12：p_d(2d+1+m) 关于 m 的单项式系数全为正，且 [m^{2d-1}] = 5d * [m^{2d}]（数值观察；一般 d 已被第二轮复核否定：d=47 起出现负系数，见 rv-c4-shiftpos-cex）')

# ---- 1f. Newton 系数正性
ok2, ok1 = True, True
for d in range(0, DMAX + 1):
    n2 = newton(PD[d], 2 * d + 2, 2 * d)
    n1 = newton(PD[d], 2 * d + 1, 2 * d)
    if not all(c.denominator == 1 and c > 0 for c in n2):
        ok2 = False
    if not all(c.denominator == 1 and c > 0 for c in n1):
        ok1 = False
    if n2[-1] != 2 * (factorial(2 * d) // (2 ** d * factorial(d))):
        ok2 = False
report('c4-newton-pos', ok2, 'd<=12：p_d(k)=sum_i T_i C(k-2d-2,i) 的 Newton 系数 T_i 均为正整数，T_{2d}=2(2d-1)!!')
report('c4-newton-pos-2d1', ok1, 'd<=12：基点 2d+1 的 Newton 系数也全为正整数（数值观察；一般 d 已被第二轮复核否定：d=69 时第 0 个为负，见 rv-c4-newton-cex）')

# ---- 1g. 「二阶 Euler 型」基 C(k+c-j,2d) 下无非负展开（任意整数平移 c），1<=d<=8
ok = True
for d in range(1, 9):
    p = PD[d]
    n = 2 * d
    # h_j(s) = sum_i (-1)^i C(n+1,i) p(j-i+s)：p(k) = sum_j h_j(s) C(k-s-j+2d,2d)，c=2d-s
    h1 = psub(kshift(p, 1), pscale(p, n + 1))       # 作为 s 的多项式
    lead = h1[-1]
    if not lead < 0:
        ok = False
    # Fujiwara 根界：所有复根 |z| <= 2*max_i r_i^{1/i}，r_i=|a_{n-i}/a_n| (i<n), r_n=|a_0/(2a_n)|
    nn = len(h1) - 1
    bmax = 0
    for i in range(1, nn + 1):
        r = abs(Fraction(h1[nn - i]) / lead)
        if i == nn:
            r = r / 2
        b = 0
        while Fraction(b) ** i < r:
            b += 1
        bmax = max(bmax, b)
    Bi = 2 * bmax + 1      # |s| > 2*bmax 时 h1(s) 与首项同号（<0），无需检查
    found = False
    for s in range(-Bi, Bi + 1):
        hs = [sum((-1) ** i * comb(n + 1, i) * pv(p, j - i + s) for i in range(j + 1)) for j in range(n + 1)]
        if all(h >= 0 for h in hs):
            found = True
    if found:
        ok = False
    # 同时：完整序列分子 Q_d(x)=(1-x)^{2d+1} sum_k D(k,d) x^k 是多项式且有负系数
    ser = [D(ND, k, d) for k in range(K + 1)]
    for _ in range(2 * d + 1):
        ser = [ser[i] - (ser[i - 1] if i > 0 else 0) for i in range(K + 1)]
    if any(ser[i] != 0 for i in range(4 * d + 3, K + 1)) or min(ser[:4 * d + 3]) >= 0:
        ok = False
report('c4-hstar-neg', ok, '1<=d<=8：任意整数 c，p_d 在基 {C(k+c-j,2d)}_{j=0..2d} 下都有负系数（Fujiwara 根界内穷举，界外 h_1<0）；(1-x)^{2d+1}sum_k D(k,d)x^k 为 <=4d+2 次多项式且有负系数')

# ---- 1h. Stirling 类比 S(k,k-d) = sum_j <<d,j>> C(k+d-1-j,2d)
S2 = stirling2_table(K)
E2 = euler2(10)
ok = True
for d in range(0, 9):
    for k in range(d, K + 1):
        val = sum(E2[d][j] * comb(k + d - 1 - j, 2 * d) for j in range(0, max(d, 1))) if d > 0 else 1
        if val != S2[k][k - d] and not (d == 0 and k == 0):
            ok = False
report('c4-stirling-analog', ok, 'S(k,k-d)=sum_j <<d,j>> C(k+d-1-j,2d) 对 0<=d<=8, d<=k<=60 成立（无例外；对照 D 的门槛 2d+2）')


# ---- 1i. 模式展开（c4.md §3 定理 3）
def pattern_counts(d):
    res = defaultdict(int)
    if d == 0:
        res[(0, 0)] += 1
    for sigma in range(1, 2 * d + 4):          # 多枚举一层 sigma=2d+3，使 c4-pattern-props 的「sigma<=2d+2」不再是空检查
        st = defaultdict(int)
        st[(0, 0, 0, 0)] = 1
        for x in range(sigma, 0, -1):
            new = defaultdict(int)
            for (p, e, closed, beta), w in st.items():
                room = d - e
                for j in range(0, p + 1):
                    wj = w * comb(p, j)
                    if closed:
                        opts = [(0, 0, 0)]
                    else:
                        opts = [(s, t, E) for t in range(0, room + 2) for s in range(0, room + 2) for E in (0, 1)]
                    for (s, t, E) in opts:
                        mu = s + 2 * t + E + j
                        if mu < 1 or (s == 1 and t == 0 and E == 0 and j == 0):
                            continue
                        e2 = e + mu - 1
                        if e2 > d:
                            continue
                        new[(p - j + t + E, e2, 1 if (closed or E) else 0, x if E else beta)] += wj * comb(s + t, s)
            st = new
        for (p, e, closed, beta), w in st.items():
            if p == 0 and e == d:
                res[(sigma, beta)] += w
    return dict(res)


def decompose(w):
    blocks, i, n = [], 0, len(w)
    while i < n:
        M = max(w[i:])
        if w[i] == M:
            blocks.append(('S', M, None)); i += 1
        elif n - i == 2:
            blocks.append(('E', M, w[i])); i += 2
        else:
            if not (w[i + 1] == M and w[i + 2] == M):
                raise AssertionError('first max not at position 1/2: lemma violated')
            blocks.append(('T', M, w[i])); i += 3
    return blocks


def good3(a, b, c):
    return b == c or (a >= b and a >= c)


def brute_patterns(d):
    res = defaultdict(int)
    if d == 0:
        res[(0, 0)] += 1
    for sigma in range(1, 2 * d + 3):
        L = sigma + d
        seq, used = [], [0] * (sigma + 1)

        def dfs():
            missing = sum(1 for v in range(1, sigma + 1) if used[v] == 0)
            if missing > L - len(seq):
                return
            if len(seq) == L:
                bl = decompose(seq)
                mu = defaultdict(int)
                for x in seq:
                    mu[x] += 1
                if any(t == 'S' and mu[v] == 1 for t, v, a in bl):
                    return
                res[(sigma, bl[-1][1] if bl[-1][0] == 'E' else 0)] += 1
                return
            for v in range(1, sigma + 1):
                if len(seq) >= 2 and not good3(seq[-2], seq[-1], v):
                    continue
                seq.append(v); used[v] += 1
                dfs()
                seq.pop(); used[v] -= 1
        dfs()
    return dict(res)


PAT = {d: pattern_counts(d) for d in range(0, 7)}
ok_cnt, ok_poly = True, True
for d in range(0, 7):
    M = PAT[d]
    for k in range(d, K + 1):
        q = k - d
        if sum(w * Cplus(q - b, s - b) for (s, b), w in M.items()) != D(ND, k, d):
            ok_cnt = False
    poly = []
    for (s, b), w in M.items():
        poly = padd(poly, pscale(binom_poly(-d - b, s - b), w))
    if trim(poly) != trim(PD[d]):
        ok_poly = False
report('c4-pattern-expansion', ok_cnt, 'd<=6：D(k,d) = sum_{sigma,beta} M(d;sigma,beta) C+(k-d-beta, sigma-beta) 对全部 d<=k<=60 成立（对 DP 表；C+ 为组合意义二项式）')
report('c4-pattern-poly', ok_poly, 'd<=6：sum M(d;sigma,beta) C(k-d-beta,sigma-beta)（多项式二项式）== p_d(k)')
ok = all(brute_patterns(d) == PAT[d] for d in range(0, 4))
report('c4-pattern-brute', ok, 'd<=3：按定义暴力枚举「全特殊值」合法满射词（块分解+平凡值判定）得到的 M(d;sigma,beta) == 模式 DP')
ok = True
for d in range(0, 7):
    M = PAT[d]
    df = factorial(2 * d) // (2 ** d * factorial(d))      # (2d-1)!!
    for (s, b), w in M.items():
        if w <= 0 or s > 2 * d + 2 or b > d + 2 or b == 1 or (b > 0 and b > s):
            ok = False
    if M.get((2 * d, 0), 0) != df or M.get((2 * d + 2, 2), 0) != df or M.get((2 * d + 2, d + 2), 0) != factorial(d + 1):
        ok = False
    if sum(w for (s, b), w in M.items() if s - b == 2 * d) != 2 * df:
        ok = False
    if sum(w for (s, b), w in M.items() if b == d + 2) != factorial(d + 1):
        ok = False
report('c4-pattern-props', ok, 'd<=6：sigma<=2d+2（模式 DP 枚举到 sigma=2d+3，该层为空），beta in {0}∪[2,d+2]；M(d;2d,0)=M(d;2d+2,2)=(2d-1)!!；beta=d+2 只有 (sigma=2d+2) 共 (d+1)! 个；sigma-beta=2d 的模式共 2(2d-1)!! 个')

ok = True
for d in range(1, 7):
    M = PAT[d]
    df1 = factorial(2 * d) // (2 ** d * factorial(d))
    if not (M.get((2 * d - 1, 0)) == df1 and M.get((2 * d + 1, 2)) == df1):
        ok = False
    if M.get((2 * d + 2, d + 1)) != d * factorial(d + 1) // 2:
        ok = False
    if d >= 2 and M.get((2 * d - 2, 0)) != 4 * (d - 1) * (factorial(2 * d - 2) // (2 ** (d - 1) * factorial(d - 1))):
        ok = False
report('c4-pattern-families', ok, '1<=d<=6（四个族已由第二轮复核者 r-c4i §5 证明，这里是数据核对）：M(d;2d-1,0)=M(d;2d+1,2)=(2d-1)!!，M(d;2d+2,d+1)=d(d+1)!/2，M(d;2d-2,0)=4(d-1)(2d-3)!! (d>=2)')

# =====================================================================
# 2. (C7) 分子 Num_q = P_{q-1} * F_q,  F_q = sum_k N(k,q) x^k
# =====================================================================
QR = 70
NUM = {1: [0, 1], 2: [0, 0, 2, 0, 1]}
for q in range(3, QR + 1):
    NUM[q] = padd(pmul([0, 1, 0, 2 * (q - 1)], NUM[q - 1]),
                  pmul(pscale(pshift(b_poly(q - 2), 3), q - 1), NUM[q - 2]))


def Fser(q):
    if q < 0:
        return [0] * (K + 1)
    return [ND[k][q] if q <= k else 0 for k in range(K + 1)]


# ---- 2a. F_q 的一阶递推（含 k<=2 边界缺陷项 [q=2]x^2）
ok = True
for q in range(1, 31):
    lhs = series_mul(b_poly(q - 1), Fser(q), K + 1)
    r1 = series_mul([0, 1, 0, 2 * (q - 1)], Fser(q - 1), K + 1)
    r2 = series_mul([0, 0, 0, q - 1], Fser(q - 2), K + 1)
    rhs = [r1[i] + r2[i] + (1 if (q == 2 and i == 2) else 0) for i in range(K + 1)]
    if [lhs[i] for i in range(K + 1)] != rhs:
        ok = False
report('c4-F-rec', ok, 'b_{q-1}F_q = (x+2(q-1)x^3)F_{q-1} + (q-1)x^3 F_{q-2} + [q=2]x^2（F_0=1,F_{-1}=0），1<=q<=30，模 x^61（F 取自 DP）')

# ---- 2b. 分子是多项式且等于三项递推的结果
ok = True
for q in range(1, 20):
    pr = series_mul(Fser(q), P_poly(q - 1), K + 1)
    if any(pr[i] != 0 for i in range(3 * q - 1, K + 1)):
        ok = False
    if trim(pr[:3 * q - 1]) != trim(NUM[q]):
        ok = False
report('c4-Num-rec', ok, 'P_{q-1}F_q（F 取自 DP，截断 x^60）是多项式，且 == 三项递推 Num_q=(x+2(q-1)x^3)Num_{q-1}+(q-1)x^3 b_{q-2} Num_{q-2}（Num_1=x,Num_2=2x^2+x^4），q<=19')

# ---- 2c. 次数/首项/最低项
ok = True
for q in range(1, QR + 1):
    p = NUM[q]
    if len(p) - 1 != 3 * q - 2 or p[-1] != factorial(q - 1):
        ok = False
    low = min(i for i, c in enumerate(p) if c != 0)
    if q == 1:
        ok = ok and (low == 1 and p[1] == 1)
    elif not (low == q and p[q] == 2):
        ok = False
report('c4-Num-deg-lead-low', ok, 'q<=70：deg Num_q = 3q-2，首项 (q-1)! x^{3q-2}，最低项 2x^q (q>=2；q=1 时为 x)')

# ---- 2d. 容斥式与 W_m
W = {-1: [1]}
for m in range(0, 25):
    W[m] = padd(W[m - 1], pshift(pscale(P_poly(m - 1), m), 2))
ok = True
for m in range(0, 16):
    G = [TU[k][m] for k in range(K + 1)]
    pr = series_mul(G, P_poly(m), K + 1)
    if trim(pr) != trim(W[m]):
        ok = False
report('c4-Wm', ok, 'P_m * sum_k U_k(m) x^k == W_m := 1 + x^2 sum_{j=1}^m j P_{j-1}（U 取自 DP），m<=15，模 x^61')
ok = True
for q in range(1, 20):
    tot = []
    for i in range(0, q + 1):
        prod = [1]
        for v in range(i, q):
            prod = pmul(prod, b_poly(v))
        tot = padd(tot, pscale(pmul(W[i - 1], prod), (-1) ** (q - i) * comb(q, i)))
    pr = series_mul(Fser(q), P_poly(q - 1), K + 1)
    if trim(tot) != trim(pr[:3 * q - 1]):
        ok = False
report('c4-Num-IE', ok, '容斥式 Num_q = sum_{i=0}^q (-1)^{q-i} C(q,i) W_{i-1} prod_{v=i}^{q-1} b_v (W_{-1}=1) == DP 得到的分子，q<=19')

# ---- 2e. gcd(Num_q, P_{q-1}) = 1
ok = True
for q in range(1, 17):
    g = pgcd(NUM[q], P_poly(q - 1))
    if len(g) != 1:
        ok = False
report('c4-Num-gcd16', ok, 'gcd(Num_q, P_{q-1}) = 1（有理系数 Euclid 全量计算），q<=16：Num_q/P_{q-1} 为既约分式')
ok = True
for q in range(1, 41):
    if peval(NUM[q], 1) == 0:
        ok = False
    for i in range(1, q):
        _, r = pdiv(NUM[q], b_poly(i))
        if not r:
            ok = False
    for (i, s, quad) in ((4, 2, [1, 1, 2]), (18, 3, [1, 2, 6])):
        if i < q:
            if trim(pmul([1, -s], quad)) != trim(b_poly(i)):
                ok = False
            if peval(NUM[q], Fraction(1, s)) == 0:
                ok = False
            _, r2 = pdiv(NUM[q], quad)
            if not r2:
                ok = False
report('c4-Num-gcd40', ok, 'q<=40：Num_q 与每个 b_i (0<=i<=q-1) 互素（余式非零；b_4=(1-2x)(1+x+2x^2), b_18=(1-3x)(1+2x+6x^2) 的因子分别检验）')

# ---- 2f. Num_q(1) = A000262(q) = sum_j L(q,j)
ok = True
for q in range(1, 41):
    lah = sum(Fraction(factorial(q), factorial(j)) * comb(q - 1, j - 1) for j in range(1, q + 1))
    if peval(NUM[q], 1) != lah:
        ok = False
report('c4-Num-at-1', ok, 'Num_q(1) = sum_j (q!/j!)C(q-1,j-1)（无符号 Lah 数之和 = OEIS A000262），q<=40')

# ---- 2g. 系数非负、支撑；正项全历史递推
ok = True
for q in range(2, QR + 1):
    p = NUM[q]
    supp = [i for i, c in enumerate(p) if c != 0]
    if any(c < 0 for c in p) or supp != list(range(q, 3 * q - 3)) + [3 * q - 2]:
        ok = False
report('c4-Num-support', ok, '2<=q<=70：Num_q 系数全非负，非零项恰为 x^q..x^{3q-4} 与 x^{3q-2}（[x^{3q-3}]=0）')
ok = True
for q in range(3, 41):
    s = pshift(NUM[q - 1], 1)
    for m in range(2, q - 1):
        s = padd(s, pscale(pmul(pshift([q - 1 - m, 1], 3 * (q - 1 - m)), NUM[m]), factorial(q - 1) // factorial(m)))
    bd = [0] * (3 * q - 1)
    bd[3 * q - 5] += q - 2
    bd[3 * q - 4] += q
    bd[3 * q - 2] += 1
    s = padd(s, pscale(bd, factorial(q - 1)))
    if trim(s) != trim(NUM[q]):
        ok = False
report('c4-Num-posrec', ok, '3<=q<=40：正项全历史递推 Num_q = x Num_{q-1} + sum_{m=2}^{q-2} (q-1)!/m! x^{3(q-1-m)}(q-1-m+x) Num_m + (q-1)!((q-2)x^{3q-5}+q x^{3q-4}+x^{3q-2})')

# ---- 2h. 低次系数 nu_j(q) = [x^{q+j}] Num_q
E2b = euler2(12)


def cpoly(b):
    """c(q,q-b)（第一类无符号 Stirling）作为 q 的多项式：GKP (6.44) sum_k <<b,k>> C(q+k,2b)。"""
    if b == 0:
        return [Fraction(1)]
    p = []
    for k in range(0, b):
        p = padd(p, pscale(binom_poly(k, 2 * b), E2b[b][k]))
    return p


_PICACHE = {}


def pipoly(i):
    if i in _PICACHE:
        return _PICACHE[i]
    _PICACHE[i] = _pipoly(i)
    return _PICACHE[i]


def _pipoly(i):
    """pi_i(q) = [x^i] P_{q-1} = sum_{a+3b=i} (-1)^{a+b} c(q,q-b) C(q-b,a)。"""
    p = []
    for b in range(0, i // 3 + 1):
        a = i - 3 * b
        p = padd(p, pscale(pmul(cpoly(b), binom_poly(-b, a)), (-1) ** (a + b)))
    return p


C1 = stirling1_table(max(K, QR) + 2)
ok = all(pv(cpoly(b), q) == (C1[q][q - b] if q - b >= 0 else 0) for b in range(0, 9) for q in range(0, K + 1))
for i in range(0, 13):
    pi = pipoly(i)
    for q in range(0, K + 1):
        P = P_poly(q - 1)
        if pv(pi, q) != (P[i] if i < len(P) else 0):
            ok = False
report('c4-pi-poly', ok, 'c(q,q-b)=sum_k <<b,k>>C(q+k,2b) (b<=8, q<=60)，且 [x^i]P_{q-1} == sum_{a+3b=i}(-1)^{a+b}c(q,q-b)C(q-b,a) 作为 q 的多项式 (i<=12, 0<=q<=60)')
NU_TABLE = {
    0: (1, [2]),
    1: (1, [1, -1, -4]),
    2: (4, [1, -6, 7, -2, 76]),
    3: (24, [1, -15, 85, -193, 358, -236, -3144]),
    4: (192, [1, -28, 330, -1952, 6481, -12708, 2692, 5184, 223872]),
    5: (1920, [1, -45, 890, -9690, 63513, -260965, 654060, -910900, 1601856, -1138720, -24443520]),
    6: (23040, [1, -66, 1961, -33650, 366603, -2651598, 12951003, -42452550, 93367136, -137063416,
                -12165104, 87679680, 3793098240]),
}
ok_id, ok_thr, ok_tab = True, True, True
for j in range(0, 9):
    nu = []
    for i in range(0, j + 1):
        nu = padd(nu, pmul(pipoly(i), kshift(PD[j - i], j - i)))
    # 系数提取恒等式（DP 数据）
    for q in range(1, 20):
        val = sum(pv(pipoly(i), q) * D(ND, q + j - i, j - i) for i in range(0, j + 1))
        if val != (NUM[q][q + j] if q + j < len(NUM[q]) else 0):
            ok_id = False
    for q in range(j + 2, QR + 1):
        if pv(nu, q) != (NUM[q][q + j] if q + j < len(NUM[q]) else 0):
            ok_thr = False
    q = j + 1
    if (NUM[q][q + j] if q + j < len(NUM[q]) else 0) - pv(nu, q) != (-1) ** (j + 1) * factorial(j + 1):
        ok_thr = False
    if len(nu) - 1 != 2 * j or nu[-1] != Fraction(2, 2 ** j * factorial(j)):
        ok_thr = False
    if j in NU_TABLE:
        den, cs = NU_TABLE[j]
        if trim([Fraction(c, den) for c in reversed(cs)]) != trim(nu):
            ok_tab = False
report('c4-Num-low-id', ok_id, 'j<=8, q<=19：[x^{q+j}]Num_q = sum_{i=0}^j pi_i(q) D(q+j-i, j-i)（DP 数据）')
report('c4-Num-low-poly', ok_thr, 'j<=8：nu_j(q)=sum_i pi_i(q) p_{j-i}(q+j-i) 是 2j 次多项式(首项 2/(2^j j!))，对 j+2<=q<=70 等于 [x^{q+j}]Num_q，q=j+1 处差 (-1)^{j+1}(j+1)!（门槛恰为 j+2）')
report('c4-Num-low-table', ok_tab, 'c4.md 表 5 的 nu_j (j<=6) == 构造多项式')

# ---- 2i. 高次系数 a_{q,j} = [x^{3q-2-j}]Num_q 的第一类 Stirling 数公式（j<=8）
HF = {
    0: {1: [1]},
    1: {},
    2: {1: [-1, 1], 2: [1]},
    3: {1: [1, -1], 2: [-1, 1]},
    4: {1: [-1, 1], 2: [-1], 3: [1]},
    5: {1: [1, Fraction(-3, 2), Fraction(1, 2)], 2: [2, -1], 3: [-2, 1]},
    6: {1: [Fraction(-3, 2), Fraction(11, 4), Fraction(-5, 4)], 2: [-2, Fraction(1, 2), Fraction(1, 2)], 3: [0, -1], 4: [1]},
    7: {1: [Fraction(3, 2), Fraction(-9, 4), Fraction(3, 4)], 2: [2, -1], 3: [3, -1], 4: [-3, 1]},
    8: {1: [Fraction(-9, 4), Fraction(55, 24), Fraction(-1, 8), Fraction(1, 12)], 2: [Fraction(-5, 2), 2, -1],
        3: [-4, Fraction(3, 2), Fraction(1, 2)], 4: [2, -2], 5: [1]},
}


def hval(j, q):
    if j < 0:
        return 0
    return sum(pv(pol, q) * C1[q][i] for i, pol in HF[j].items())


ok = True
for j in range(0, 9):
    for q in range(1, QR + 1):
        e = 3 * q - 2 - j
        actual = NUM[q][e] if 0 <= e < len(NUM[q]) else 0
        if hval(j, q) != actual:
            ok = False
report('c4-Num-high-values', ok, 'j<=8, 1<=q<=70：[x^{3q-2-j}]Num_q == 表 6 的公式 sum_i pi_{j,i}(q) c(q,i)（c 为第一类无符号 Stirling 数）')


def to_base2(F, shift):
    """F(q+shift) 的表示 sum_i pol_i(q+shift) c(q+shift,i) 化成 c(q-2,i) 基（多项式系数为 q 的多项式），shift in {0,-1,-2}。"""
    out = defaultdict(list)
    for i, pol in F.items():
        P = kshift([Fraction(a) for a in pol], shift)
        if shift == 0:
            # c(q,i) = (q-1)(q-2)c(q-2,i) + (2q-3)c(q-2,i-1) + c(q-2,i-2)
            out[i] = padd(out[i], pmul(P, [Fraction(2), Fraction(-3), Fraction(1)]))
            out[i - 1] = padd(out[i - 1], pmul(P, [Fraction(-3), Fraction(2)]))
            out[i - 2] = padd(out[i - 2], P)
        elif shift == -1:
            # c(q-1,i) = (q-2)c(q-2,i) + c(q-2,i-1)
            out[i] = padd(out[i], pmul(P, [Fraction(-2), Fraction(1)]))
            out[i - 1] = padd(out[i - 1], P)
        else:
            out[i] = padd(out[i], P)
    return out


def comb_add(acc, part, factor):
    for i, pol in part.items():
        acc[i] = padd(acc[i], pmul(pol, factor))


ok = True
for j in range(0, 9):
    acc = defaultdict(list)
    comb_add(acc, to_base2(HF[j], 0), [Fraction(1)])
    comb_add(acc, to_base2(HF[j], -1), [Fraction(2), Fraction(-2)])            # -2(q-1)
    if j - 2 >= 0:
        comb_add(acc, to_base2(HF[j - 2], -1), [Fraction(-1)])
    if j - 3 >= 0:
        comb_add(acc, to_base2(HF[j - 3], -2), [Fraction(1), Fraction(-1)])     # -(q-1)
    if j - 2 >= 0:
        comb_add(acc, to_base2(HF[j - 2], -2), [Fraction(-1), Fraction(1)])     # +(q-1)
    comb_add(acc, to_base2(HF[j], -2), [Fraction(2), Fraction(-3), Fraction(1)])  # +(q-1)(q-2)
    for i, pol in acc.items():
        if i >= 1 and trim(pol) != []:
            ok = False
    # 初值 q=1,2
    for q in (1, 2):
        e = 3 * q - 2 - j
        actual = NUM[q][e] if 0 <= e < len(NUM[q]) else 0
        if hval(j, q) != actual:
            ok = False
report('c4-Num-high-proof', ok, 'j<=8：表 6 公式代入 a_{q,j}=2(q-1)a_{q-1,j}+a_{q-1,j-2}+(q-1)[a_{q-2,j-3}-a_{q-2,j-2}-(q-2)a_{q-2,j}] 后在 c(q-2,i) 基下系数多项式恒为 0（q>=3），且 q=1,2 初值吻合 ⇒ 对全部 q>=1 成立')

# ---- 2j. 反转分子 R_q(y)=y^{3q-2}Num_q(1/y) 的指数母函数闭式
Z = 14


def yadd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def sadd(A, B):
    return [yadd(A[i], B[i]) for i in range(Z + 1)]


def smul(A, B):
    C = [[] for _ in range(Z + 1)]
    for i in range(Z + 1):
        if not A[i]:
            continue
        for j in range(Z + 1 - i):
            if B[j]:
                C[i + j] = yadd(C[i + j], pmul(A[i], B[j]))
    return C


def sy(A, p):
    return [pmul(a, p) if a else [] for a in A]


def sc(A, c):
    return [pscale(a, c) if a else [] for a in A]


Lser = [[]] + [[Fraction(1, n)] for n in range(1, Z + 1)]          # -ln(1-z)
Gser = [[]] + [[Fraction(1)] for n in range(1, Z + 1)]             # z/(1-z)
Lam = sadd(sy(Lser, [Fraction(1), Fraction(-1)]), sy(Gser, [Fraction(0), Fraction(1)]))   # (y-1)ln(1-z)+yz/(1-z)
one = [[Fraction(1)]] + [[] for _ in range(Z)]
Ex, T1, term = [list(x) for x in one], [[] for _ in range(Z + 1)], [list(x) for x in one]
for r in range(1, Z + 1):
    term = sc(smul(term, Lam), Fraction(1, r))                     # Lam^r/r!
    Ex = sadd(Ex, sy(term, [0] * (2 * r) + [Fraction(1)]))           # exp(y^2 Lam)
    T1 = sadd(T1, sy(term, [0] * (2 * r - 2) + [Fraction(1)]))       # (exp(y^2 Lam)-1)/y^2
T1 = sy(T1, [Fraction(1), Fraction(1)])
ee = [0, 0, Fraction(-1), Fraction(1)]                               # e = y^3 - y^2
bino = [[Fraction(1)]]
ex3 = [[Fraction(1)]]
for n in range(1, Z + 1):
    bino.append(pscale(pmul(bino[-1], yadd(ee, [Fraction(-(n - 1))])), Fraction(1, n)))   # C(e,n)
    ex3.append(pscale(pmul(ex3[-1], [0, 0, 0, Fraction(-1)]), Fraction(1, n)))           # (-y^3)^n/n!
gco = [[] for _ in range(Z + 1)]
for n in range(Z + 1):
    for i in range(n + 1):
        gco[n] = yadd(gco[n], pmul(bino[i], ex3[n - i]))
Iser = [[] for _ in range(Z + 1)]
Gp = [list(x) for x in Gser]
for n in range(0, Z):
    Iser = sadd(Iser, sy(Gp, pscale(gco[n], Fraction(1, n + 1))))
    Gp = smul(Gp, Gser)
Aser = sadd(T1, sy(smul(Ex, Iser), [0, Fraction(-1)]))
ok = (Aser[0] == [])
for q in range(1, Z + 1):
    Rq = trim(list(reversed([Fraction(c) for c in NUM[q]])))
    if trim([c * factorial(q) for c in Aser[q]]) != Rq:
        ok = False
report('c4-Num-egf', ok, 'q<=14：sum_q R_q(y) z^q/q! == (y+1)(e^{y^2 Lam}-1)/y^2 - y e^{y^2 Lam} int_0^{z/(1-z)} (1+w)^{y^3-y^2} e^{-y^3 w} dw，Lam=(y-1)ln(1-z)+yz/(1-z)（Q[y][[z]] 中逐项精确展开）')
# ODE: (1-z)^2 A'' = (y^2-1) + (2(1-z) + y^2(1-z) + y^3 z) A' + (y^3-y^2) A，A 由真实 R_q 构成
Areal = [[]] + [pscale(trim(list(reversed([Fraction(c) for c in NUM[q]]))), Fraction(1, factorial(q))) for q in range(1, Z + 1)]


def sder(A):
    return [pscale(A[i + 1], i + 1) if A[i + 1] else [] for i in range(Z)] + [[]]


A1, A2 = sder(Areal), sder(sder(Areal))
lhs = smul([[Fraction(1)], [Fraction(-2)], [Fraction(1)]] + [[] for _ in range(Z - 2)], A2)
coefA1 = [[Fraction(2), 0, Fraction(1)], [Fraction(-2), 0, Fraction(-1), Fraction(1)]] + [[] for _ in range(Z - 1)]
rhs = sadd(smul(coefA1, A1), sy(Areal, ee))
rhs[0] = yadd(rhs[0], [Fraction(-1), 0, Fraction(1)])
ok = all(trim(lhs[i]) == trim(rhs[i]) for i in range(Z - 1))
report('c4-Num-ode', ok, '由三项递推得到的 A(z)=sum R_q z^q/q! 满足 (1-z)^2A\'\'=(y^2-1)+(2(1-z)+y^2(1-z)+y^3 z)A\'+(y^3-y^2)A，逐项到 z^12')

# =====================================================================
npass = sum(RESULTS)
nfail = len(RESULTS) - npass
print('# runtime %.1fs' % (time.time() - T0))
print('SUMMARY c4 pass=%d fail=%d' % (npass, nfail))
sys.exit(0 if nfail == 0 else 1)
