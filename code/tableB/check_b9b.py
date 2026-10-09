# -*- coding: utf-8 -*-
"""表 B 的 B9（续）：固定位置系数转正门槛 τ_i 的增长（2026-10-09）。证明与说明见 notes/18-主Agent-表B-B9-门槛的增长.md。

逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b9b pass=<n> fail=<n>」。只用标准库。
h_k 用 T1.7 的递推（截断到 i<=I，对 i<=I 的系数精确）；U 由引理 1.1 的三项递推算，N 由三角递推（T1.4(2)）算，作为两种独立对照。
用法：py -3.14 code/tableB/check_b9b.py [--full]
  默认：扫描 k<=2000，认证 τ_i（i<=60），约 2 s；--full：扫描 k<=20000，认证 τ_i（i<=579），约 8.5 分钟、峰值约 0.2 GB。
  b9b-lem11   引理 1.1：u_jP_j/D_j <= c_j <= (u_j+j)P_j/D_j（1<=j<=80，60 位十进制）
  b9b-lem12   引理 1.2：λ_j=ln(P_{j+1}/P_j)>=1。j<=3 用 ρ 的有理区间直接验证（证明的有限部分）；j>=4 用的下界
              φ(a)=2a-(3a-1)/(a(3a-2))-1/(a(3a-2))^2 在 a=2 处为 3.359 且递增（整个式子抽样）；另对 j<=5000 浮点验证 λ_j>=1，
              且 λ_j-1 ~ 2/(3ρ_j)（常数 1 不能改大）
  b9b-lem13   引理 1.3：ρ_j/ρ_i <= exp(-(i-j)/D_i)（0<=j<i<=300，浮点）
  b9b-lem14   引理 1.4：M(ρ)=(ρ/(ρ-1))sqrt((3ρ-2)/(3ρ+1)) 递减，M(ρ_1)<2.1（ρ_1 用有理下界）
  b9b-scan    截断递推 = 完整递推（k<=300）= U 的反演（k<=60）= N 三角公式 h_{k,i}=Σ_q (-1)^{i+1-q}C(k-q,i+1-q)N(k,q)
              （抽样 k，i<=119）
  b9b-K       K_i:=D_i(ln(D_i/0.26)+lnln(D_i/0.26)) 的上界（ρ_i 取有理上界，浮点计算后加 1 的余量；名义值另列）；
              所有要认证的 i 都有 K_i 的上界 <= 扫描上限
  b9b-thm     定理 1：|h_{k,i}/(c_iρ_i^k)-1| <= 3(e^X-1)(1+4.2E)+4.2E 对 1<=i<=40 与 0<=k<=扫描上限 的每一点成立（逐点，含 k<K_i）；
              K_i 处 X<=0.26、E<=0.01、右边 <=0.9702
  b9b-tau     推论 2（计算机辅助）：认证函数只在「每个 i 的 K_i 上界都 <= 扫描上限」时才输出 τ_i=1+max{k<=K: h_{k,i}<=0}；
              i<=40 与 notes/16、41<=i<=100 与复核者 s14-b9 的证书一致
  b9b-rev     反向检查：用 N 三角公式（与扫描不同的算法）独立算 h_{τ_i-1,i}<=0<h_{τ_i,i}（全部认证的 i）；定理 1 的界在 k=τ_i 处 >=1
              （1<=i<=100）——门槛附近必须靠精确计算；扫描上限取 1/3 时认证函数拒绝输出；把递推里的 (k-2) 改成 (k-3) 后门槛表改变
  b9b-model   数值佐证（不是证明；猜想 3）：ξ*=max g、g 单峰；ℓ_k-ξ*k 的范围；τ 的窗口平均差与 α*=1/ξ*；k=300 的根计数与模型；
              系数增长率的偏差按 k^(-1/3) 缩小；|t|=s（10^-12<=s<=0.075）的圆周上 Φ 在 θ=0 取严格最大；h_k（k=600，--full 为 1500）
              按 ξ 分窗的变号数与复鞍点模型 k∫arg t_s dξ/π 对照；另报告恒等式 ∫_{ξ*}^{2/3} arg t_s dξ/π=1/3（只说明路径延拓正确，不是证据）
"""
import cmath
import math
import sys
import time
from decimal import Decimal as Dm, getcontext
from fractions import Fraction as Fr
from math import comb

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []
TAU40 = [2, 8, 16, 24, 33, 41, 50, 59, 68, 77, 86, 95, 105, 114, 123, 132, 141, 151, 160, 169,
         178, 188, 197, 206, 216, 225, 234, 244, 253, 263, 272, 281, 291, 300, 310, 319, 328, 338, 347, 357]
# 复核者 s14-b9 的独立证书（notes/16 注 2.0，logs/review_s14-b9_r2b_tau_more.log）
REV41_100 = [366, 376, 385, 394, 404, 413, 423, 432, 442, 451, 461, 470, 480, 489, 498, 508, 517, 527, 536, 546,
             555, 565, 574, 584, 593, 603, 612, 622, 631, 641, 650, 660, 669, 679, 688, 698, 707, 717, 726, 736,
             745, 755, 765, 774, 784, 793, 803, 812, 822, 831, 841, 850, 860, 869, 879, 888, 898, 907, 917, 927]


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


# ------------------------------------------------------------------ ρ_j 与相关量
def rho_bracket(j, bits=110):
    """y^3-y^2=j 的实根 ρ_j>=1 的有理区间 [lo,hi]，宽度 < 2^-bits。"""
    if j == 0:
        return Fr(1), Fr(1)
    lo, hi = Fr(1), Fr(max(2, j))
    while hi - lo > Fr(1, 1 << bits):
        m = (lo + hi) / 2
        if m ** 3 - m ** 2 < j:
            lo = m
        else:
            hi = m
    return lo, hi


def rho_dec(j):
    lo, hi = rho_bracket(j, 220)
    return Dm(lo.numerator) / Dm(lo.denominator)


def rho_float(j):
    if j == 0:
        return 1.0
    y = max(1.0, j ** (1 / 3) + 1 / 3)
    for _ in range(100):
        y2 = y - (y ** 3 - y ** 2 - j) / (3 * y * y - 2 * y)
        if abs(y2 - y) < 1e-15 * y:
            return y2
        y = y2
    return y


def c_dec(j):
    """c_j=ĝ_j(ρ_j)/(ρ_j^2+3j)，ĝ_j(y)=y^{3j+3}/j!+Σ_{l<j}(j-l)y^{3l+1}/l!（notes/16 引理 1）。"""
    r = rho_dec(j)
    u = r ** 3
    g = u ** (j + 1) / Dm(math.factorial(j))
    s = Dm(0)
    for l in range(j):
        s += (j - l) * r * u ** l / Dm(math.factorial(l))
    return (g + s) / (r * r + 3 * j), r, u


def lnc_float(j):
    """ln c_j（浮点；用 lgamma 与对数求和避免溢出）。"""
    r = rho_float(j)
    u = r ** 3
    terms = [(j + 1) * math.log(u) - math.lgamma(j + 1)]
    for l in range(j):
        terms.append(math.log(j - l) + math.log(r) + l * math.log(u) - math.lgamma(l + 1))
    m = max(terms)
    return m + math.log(sum(math.exp(t - m) for t in terms)) - math.log(r * r + 3 * j), r


def M_of(rho):
    return (rho / (rho - 1)) * math.sqrt((3 * rho - 2) / (3 * rho + 1))


def K_nominal(i):
    r = rho_float(i)
    D = r * r + 3 * i
    A = D / 0.26
    return D * (math.log(A) + math.log(math.log(A)))


def K_upper(i):
    """K_i 的上界：用 ρ_i 的有理上界算 D_i 的上界（K 关于 D 递增），浮点计算后加 1 的余量再取整。
    （复核者 s17-b9b 用 50 位十进制独立确认这些上界都成立，见 logs/review_s17-b9b_r3_constants.log。）"""
    lo, hi = rho_bracket(i, 80)
    D = float(hi * hi) + 3 * i
    A = D / 0.26
    return math.ceil(D * (math.log(A) + math.log(math.log(A))) + 1)


def thm_log_bound(k, rho, u, D):
    """返回 (ln B, B 或 None, X, E)，B=3(e^X-1)(1+4.2E)+4.2E。X 很大时只给 ln B 的下界（比较方向保守）。"""
    X = (k + 1 + u) * math.exp(-1 - k / D)
    E = math.exp(-k / (2 * rho))
    if X < 700:
        B = 3 * math.expm1(X) * (1 + 4.2 * E) + 4.2 * E      # k 很大时 X、E 下溢为 0，B=0（比较时有 1e-9 的浮点容差）
        return (math.log(B) if B > 0 else -math.inf), B, X, E
    return X + math.log(3 * (1 + 4.2 * E)) - 1e-12, None, X, E


def lnbig(x):
    b = x.bit_length()
    if b < 1000:
        return math.log(x)
    s = b - 900
    return math.log(x >> s) + s * math.log(2)


# ------------------------------------------------------------------ h_k
def stream_scan(K, I, kfix=-2, thm=None, keep_full=300, prefix_ks=(), prefix_len=0, val_req=None):
    """T1.7 截断到 i<=I，逐行流过 k=0..K，不保留整张表。
    thm：{i: (lnc_i, ρ_i, u_i, D_i)}，对每个 k、每个这样的 i 逐点核对定理 1 的不等式（含 h<=0 与 h=0 的 k）。
    返回 last_bad[i]、ell[k]、k<=keep_full 的完整截断行、prefix_ks 中各 k 的前 prefix_len 项、val_req 中各 (k,i) 的值、定理核对统计。"""
    rows = {0: [1] + [0] * I, 1: [1] + [0] * I, 2: [1, 1] + [0] * (I - 1)}
    last_bad = [-1] * (I + 1)
    ell, full, pref, vals = {}, {}, {}, {}
    pk = set(prefix_ks)
    stats = {'n': 0, 'bad': 0, 'maxr': 0.0, 'first_bad': None}
    vreq = val_req or {}
    for k in range(K + 1):
        if k >= 3:
            gk, hk1 = rows[k - 3], rows[k - 1]
            A = [(m + 1) * gk[m + 1] + (k + kfix - m) * gk[m] for m in range(I)]
            rows[k] = [hk1[0], hk1[1] + A[0]] + [hk1[n] + A[n - 1] - A[n - 2] for n in range(2, I + 1)]
            del rows[k - 3]
        h = rows[k]
        first = None
        for i in range(I + 1):
            if h[i] <= 0:
                last_bad[i] = k
                if first is None:
                    first = i
        ell[k] = first
        if k <= keep_full:
            full[k] = h[:]
        if k in pk:
            pref[k] = h[:prefix_len]
        for i in vreq.get(k, ()):
            vals[(k, i)] = h[i]
        if thm:
            for i, (lnc, rho, u, D) in thm.items():
                lnB, B, X, E = thm_log_bound(k, rho, u, D)
                hv = h[i]
                if hv == 0:
                    ok = (B is None) or B >= 1 - 1e-9
                    ratio_err = 1.0
                else:
                    lr = lnbig(abs(hv)) - lnc - k * math.log(rho)
                    if lr < 700:
                        r = math.exp(lr) if hv > 0 else -math.exp(lr)
                        ratio_err = abs(r - 1)
                        ok = ratio_err <= B + 1e-9 if B is not None else True
                    else:
                        ratio_err = float('inf')
                        ok = lr + 1e-9 <= lnB
                stats['n'] += 1
                if not ok:
                    stats['bad'] += 1
                    if stats['first_bad'] is None:
                        stats['first_bad'] = (k, i)
                if B is not None and 1e-6 < B < 1e300 and ratio_err != float('inf'):
                    stats['maxr'] = max(stats['maxr'], ratio_err / B)
    return last_bad, ell, full, pref, vals, stats


def h_full_rows(K, want=None):
    rows = {0: [1], 1: [1], 2: [1, 1]}
    out = {k: rows[k] for k in (0, 1, 2) if want is None or k in want}
    for k in range(3, K + 1):
        g, hk1 = rows[k - 3], rows[k - 1]
        d = len(g)
        A = [(m + 1) * (g[m + 1] if m + 1 < d else 0) + (k - 2 - m) * g[m] for m in range(d)]
        n_out = max(len(hk1), d + 2)
        h = []
        for n in range(n_out):
            v = hk1[n] if n < len(hk1) else 0
            if 1 <= n <= d:
                v += A[n - 1]
            if 2 <= n <= d + 1:
                v -= A[n - 2]
            h.append(v)
        while len(h) > 1 and h[-1] == 0:
            h.pop()
        rows[k] = h
        if want is None or k in want:
            out[k] = h
        del rows[k - 3]
    return out


def U_cols(M, K):
    U = []
    for m in range(M + 1):
        col = [0] * (K + 1)
        for k in range(K + 1):
            if k == 0:
                col[k] = 1
                continue
            prev_m = U[m - 1][k] if m >= 1 else 0
            km3 = col[k - 3] if k >= 3 else (1 if k == 2 else 0)
            col[k] = prev_m + col[k - 1] + m * km3
        U.append(col)
    return U


def N_stream(K, Q, visit):
    """N(k,q)（q<=Q）的三角递推（check_b9.N_table 的截断版），逐行调用 visit(k, row)。"""
    rows = {0: [1] + [0] * Q, 1: [0, 1] + [0] * (Q - 1), 2: [0, 1, 2] + [0] * (Q - 2)}
    for k in (0, 1, 2):
        visit(k, rows[k])
    for k in range(3, K + 1):
        p1, p3 = rows[k - 1], rows[k - 3]
        r = [0] * (Q + 1)
        for q in range(1, Q + 1):
            t = (p3[q - 2] if q >= 2 else 0) + 2 * p3[q - 1] + p3[q]
            r[q] = p1[q - 1] + p1[q] + (q - 1) * t
        rows[k] = r
        del rows[k - 3]
        visit(k, r)


def h_from_N(Nrow, k, i):
    """h_k(t)=Σ_q N(k,q)t^{q-1}(1-t)^{k-q}（由 U_k(m)=Σ_q C(m+1,q)N(k,q) 与 f_k=h_k/(1-t)^{k+1}）；q>k 时 N=0。"""
    return sum((-1) ** (i + 1 - q) * comb(k - q, i + 1 - q) * Nrow[q] for q in range(1, min(i + 1, k) + 1))


def certify(last_bad, Ks, K_scan, I_cert):
    """推论 2 的认证：只有当每个 1<=i<=I_cert 的 K_i 上界都 <= 扫描上限时才输出 τ；否则返回 None（拒绝）。"""
    if any(Ks[i] > K_scan for i in range(1, I_cert + 1)):
        return None
    return [None] + [last_bad[i] + 1 for i in range(1, I_cert + 1)]


# ------------------------------------------------------------------ 模型（猜想 3）
def psi_r(t):
    return t - 1 - math.log(t)


def g_r(t):
    return (1 - t) / (3 * psi_r(t)) - t / (1 - t)


def g_prime(t):
    p = psi_r(t)
    return (-p - (1 - t) * (1 - 1 / t)) / (3 * p * p) - 1 / (1 - t) ** 2


def xi_star():
    """t*：g'(t)=0 在 (0.01,0.3) 中的根（g 单峰，g' 由正变负），二分到浮点精度。"""
    lo, hi = 0.01, 0.3
    assert g_prime(lo) > 0 > g_prime(hi)
    for _ in range(200):
        m = (lo + hi) / 2
        if g_prime(m) > 0:
            lo = m
        else:
            hi = m
    t = (lo + hi) / 2
    return t, g_r(t)


def Phi_c(t):
    """Φ(t)=ln|1-t|-(1/3)ln|ψ(t)|，ψ 取主支（t-1-Log t）。"""
    return math.log(abs(1 - t)) - math.log(abs(t - 1 - cmath.log(t))) / 3


def neg_cdf(tau):
    v = tau + 1 + math.log(tau)
    return (math.atan(v / math.pi) + math.pi / 2) / (3 * math.pi)


def saddle_path(xi_max, N=40000):
    """ξ∈(ξ*,xi_max] 上的复鞍点 t_s(ξ)（上半平面，从汇合点 t* 延拓；主支 ψ）。返回 [(ξ, t_s)]。"""
    def G(t):
        return (1 - t) / (3 * (t - 1 - cmath.log(t))) - t / (1 - t)

    def dG(t):
        p = t - 1 - cmath.log(t)
        return (-p - (1 - t) * (1 - 1 / t)) / (3 * p * p) - 1 / (1 - t) ** 2

    ts, xs = xi_star()
    G2 = g_r(ts + 1e-4) + g_r(ts - 1e-4) - 2 * g_r(ts)
    G2 /= 1e-8
    out, t = [], None
    for n in range(1, N + 1):
        xi = xs + (xi_max - xs) * (n / N) ** 2
        if t is None:
            t = ts + 1j * math.sqrt(2 * (xi - xs) / abs(G2))
        for _ in range(60):
            f = G(t) - xi
            st = f / dG(t)
            if abs(st) > 0.5 * abs(t):
                st *= 0.5 * abs(t) / abs(st)
            t = t - st
            if abs(f) < 1e-13:
                break
        if t.imag < 0:
            t = t.conjugate()
        out.append((xi, t))
    return out


def path_integral(path, a, b):
    """∫_a^b arg t_s(ξ) dξ/π（梯形；path 从 ξ* 开始，ξ* 处 arg=0）。"""
    ts, xs = xi_star()
    pts = [(xs, 0.0)] + [(x, max(0.0, cmath.phase(t))) for x, t in path]
    tot = 0.0
    for (x0, a0), (x1, a1) in zip(pts, pts[1:]):
        lo, hi = max(x0, a), min(x1, b)
        if hi <= lo:
            continue
        # 线性插值后在 [lo,hi] 上积分
        f = lambda x: a0 + (a1 - a0) * (x - x0) / (x1 - x0)
        tot += (hi - lo) * (f(lo) + f(hi)) / 2
    return tot / math.pi


def taylor_shift(c, p):
    c = list(c)
    n = len(c)
    for i in range(n):
        for j in range(n - 2, i - 1, -1):
            c[j] += p * c[j + 1]
    return c


def count_roots(h, a, b):
    """h 实根（A19）时 (a,b) 中的根数：h(a+(b-a)x) → 反转 → 平移 1，数系数变号（Descartes 对实根多项式精确）。"""
    d = len(h) - 1
    an, ad, bn, bd = a.numerator, a.denominator, b.numerator, b.denominator
    G = taylor_shift([h[i] * ad ** (d - i) for i in range(d + 1)], an)
    e = ad * bn - an * bd
    S = taylor_shift([G[j] * e ** j * bd ** (d - j) for j in range(d + 1)][::-1], 1)
    sg = [1 if c > 0 else -1 for c in S if c != 0]
    return sum(1 for u, v in zip(sg, sg[1:]) if u != v)


# ------------------------------------------------------------------ 主程序
def main(full=False):
    t_start = time.time()
    getcontext().prec = 60
    K_SCAN, I_CERT = (20000, 579) if full else (2000, 60)
    print('# check_b9b：%s；扫描 k<=%d，认证 i<=%d' % ('--full' if full else '默认', K_SCAN, I_CERT), flush=True)

    # b9b-lem11
    ok, worst = True, Dm(10)
    for j in range(1, 81):
        c, r, u = c_dec(j)
        P = u ** j / Dm(math.factorial(j))
        D = r * r + 3 * j
        lo, hi = u * P / D, (u + j) * P / D
        ok = ok and lo <= c <= hi
        worst = min(worst, (c - lo) / c, (hi - c) / c)
    report('b9b-lem11', ok and worst > Dm(10) ** -30,
           '引理 1.1：u_jP_j/D_j <= c_j <= (u_j+j)P_j/D_j 对 1<=j<=80 成立（60 位；最小相对余量 %.3e）' % worst)

    # b9b-lem12
    ok = True
    lam_small = []
    for j in range(4):
        alo, ahi = rho_bracket(j, 100)
        blo, bhi = rho_bracket(j + 1, 100)
        if j == 0:
            lam = 3 * math.log(float(blo))          # λ_0 = ln u_1 = 3 ln ρ_1
        else:
            lam = math.log(float(bhi / (bhi - 1))) + 3 * j * math.log(float(blo / ahi))
        lam_small.append(lam)
        ok = ok and lam >= 1 + 1e-6

    def phi(a):
        w = a * (3 * a - 2)
        return 2 * a - (3 * a - 1) / w - 1 / w ** 2
    b0 = phi(2.0)
    mono = all(phi(2 + 0.01 * s) < phi(2 + 0.01 * (s + 1)) for s in range(9800))
    lam_ok, ratio = True, []
    for j in range(0, 5001):
        aa, bb = rho_float(j), rho_float(j + 1)
        lam = 3 * math.log(bb) if j == 0 else math.log(bb / (bb - 1)) + 3 * j * math.log(bb / aa)
        lam_ok = lam_ok and lam >= 1
        if j in (100, 1000, 5000):
            ratio.append((lam - 1) / (2 / (3 * aa)))
    report('b9b-lem12', ok and b0 > 1 and mono and lam_ok and all(0.8 < x < 1.25 for x in ratio),
           '引理 1.2：λ_0..λ_3 = %s（有理区间下界，均 >1）；j>=4 用的下界 φ(a)（含 -1/(a(3a-2))^2 项）在 a=2 处为 %.4f>1、'
           '在 [2,100] 上递增（抽样）；浮点 j<=5000 全部 λ_j>=1；(λ_j-1)/(2/(3ρ_j)) 在 j=100、1000、5000 为 %s（趋于 1，常数 1 不能改大）'
           % ([round(x, 4) for x in lam_small], b0, [round(x, 3) for x in ratio]))

    # b9b-lem13
    ok = True
    rf = [rho_float(j) for j in range(301)]
    for i in range(1, 301):
        D = rf[i] ** 2 + 3 * i
        for j in range(i):
            ok = ok and rf[j] / rf[i] <= math.exp(-(i - j) / D) * (1 + 1e-12)
    report('b9b-lem13', ok, '引理 1.3：ρ_j/ρ_i <= exp(-(i-j)/D_i) 对 0<=j<i<=300 成立（浮点，相对容差 1e-12）')

    # b9b-lem14
    r1lo, r1hi = rho_bracket(1, 100)
    M1 = M_of(float(r1lo))          # M 递减，用 ρ_1 的下界得上界
    dec = all(M_of(1.47 + 0.01 * s) > M_of(1.47 + 0.01 * (s + 1)) for s in range(5000))
    deriv_ok = all(4.5 * x * (x - 1) < 9 * x * x - 3 * x - 2 for x in [1 + 0.01 * s for s in range(1, 10000)])
    report('b9b-lem14', M1 < 2.1 and dec and deriv_ok,
           '引理 1.4：M(ρ_1) <= %.5f < 2.1；M 在 [1.47,51.47] 上递减（d ln M/dρ<0 ⇔ 4.5ρ(ρ-1)<9ρ^2-3ρ-2，抽样核对）' % M1)

    # 扫描（逐行流过，同时逐点核对定理 1）
    I_SCAN = max(I_CERT + 12, int(0.12 * K_SCAN) + 10)
    thm = {}
    for i in range(1, 41):
        lnc, rho = lnc_float(i)
        thm[i] = (lnc, rho, rho ** 3, rho * rho + 3 * i)
    step = K_SCAN // 50
    sample_ks = list(range(step, K_SCAN + 1, step))
    QP = 120
    kA, kB = K_SCAN // 2, K_SCAN
    xis = (0.04, 0.08, 0.1)
    val_req = {kA: [int(x * kA) for x in xis], kB: [int(x * kB) for x in xis]}
    t0 = time.time()
    last_bad, ell, full_rows_scan, pref, vals, st = stream_scan(
        K_SCAN, I_SCAN, thm=thm, prefix_ks=sample_ks, prefix_len=QP, val_req=val_req)
    t_scan = time.time() - t0

    # b9b-scan
    full_rows = h_full_rows(300)
    ok1 = all((full_rows[k] + [0] * (I_SCAN + 1))[:I_SCAN + 1] == full_rows_scan[k] for k in range(301))
    U = U_cols(40, 60)
    ok2 = True
    for k in range(61):
        for i in range(41):
            hv = sum((-1) ** r * comb(k + 1, r) * U[i - r][k] for r in range(i + 1))
            ok2 = ok2 and hv == full_rows_scan[k][i]
    t1 = time.time()
    chk = {'ok': True, 'n': 0}
    want = set(sample_ks)

    def visit_prefix(k, row):
        if k in want:
            for i in range(QP):
                chk['ok'] = chk['ok'] and h_from_N(row, k, i) == pref[k][i]
                chk['n'] += 1
    N_stream(K_SCAN, QP + 1, visit_prefix)
    report('b9b-scan', ok1 and ok2 and chk['ok'] and chk['n'] == QP * len(want),
           '截断递推（k<=%d，i<=%d，%.1f s）= 完整递推（k<=300）= U 的反演（k<=60，i<=40）= N 三角公式（%d 个抽样 k、i<%d，共 %d 个系数，%.1f s）'
           % (K_SCAN, I_SCAN, t_scan, len(want), QP, chk['n'], time.time() - t1))

    # b9b-K
    Ks = [None] + [K_upper(i) for i in range(1, I_CERT + 1)]
    okK = all(Ks[i] <= K_SCAN for i in range(1, I_CERT + 1))
    i_max = I_CERT
    while K_upper(i_max + 1) <= K_SCAN:
        i_max += 1
    shown = [i for i in (1, 10, 40, 100, 300) if i < I_CERT] + [I_CERT]
    report('b9b-K', okK,
           'K_i 的上界：%s，全部 <= 扫描上限 %d（这次扫描最多能认证到 i=%d，K_%d<=%d 已超出）；名义值 K_1=%.4f、K_10=%.3f、K_40=%.3f、K_100=%.3f、K_300=%.3f；'
           'K_i/(3i ln i)：i=10:%.3f、i=%d:%.3f'
           % ('、'.join('K_%d<=%d' % (i, Ks[i]) for i in shown), K_SCAN, i_max, i_max + 1, K_upper(i_max + 1),
              K_nominal(1), K_nominal(10), K_nominal(40), K_nominal(100), K_nominal(300),
              K_nominal(10) / (30 * math.log(10)), I_CERT, K_nominal(I_CERT) / (3 * I_CERT * math.log(I_CERT))))

    # b9b-thm
    okKpt = True
    for i in range(1, 41):
        lnc, rho, u, D = thm[i]
        lnB, B, X, E = thm_log_bound(Ks[i], rho, u, D)
        okKpt = okKpt and X <= 0.26 + 1e-12 and E <= 0.01 and B is not None and B <= 0.97021
    report('b9b-thm', okKpt and st['bad'] == 0 and st['n'] == 40 * (K_SCAN + 1),
           '定理 1：1<=i<=40 与 0<=k<=%d 的全部 %d 个点上 |h_{k,i}/(c_iρ_i^k)-1| <= 界（含 h<=0 的 k；浮点容差 1e-9），'
           '界在 (1e-6,1e300) 内的点上「实际/界」最大 %.3f；K_i 处 X<=0.26、E<=0.01、界<=0.9702'
           % (K_SCAN, st['n'], st['maxr']))

    # b9b-tau
    cert = certify(last_bad, Ks, K_SCAN, I_CERT)
    if cert is None:
        report('b9b-tau', False, '认证函数拒绝：有 K_i 超过扫描上限')
        tau = None
    else:
        tau = cert
        ok40 = tau[1:41] == TAU40
        okrev = tau[41:min(I_CERT, 100) + 1] == REV41_100[:min(I_CERT, 100) - 40]
        diffs = [tau[i + 1] - tau[i] for i in range(8, I_CERT)]
        report('b9b-tau', ok40 and okrev,
               '推论 2：τ_1..τ_%d 由「定理 1 + 精确扫描」认证（每个 i 都有 K_i<=%d）；i<=40 与 notes/16 相同，41<=i<=%d 与复核者 s14-b9 的证书相同；'
               'τ_%d=%d；8<=i<%d 时相邻差只取 %s（9 有 %d 次、10 有 %d 次）'
               % (I_CERT, K_SCAN, min(I_CERT, 100), I_CERT, tau[I_CERT], I_CERT, sorted(set(diffs)),
                  diffs.count(9), diffs.count(10)))
        print('# tau_1..tau_%d = %s' % (I_CERT, tau[1:]), flush=True)

    # b9b-rev
    if tau is not None:
        need = {}
        for i in range(1, I_CERT + 1):
            need.setdefault(tau[i] - 1, []).append((i, 'le0'))
            need.setdefault(tau[i], []).append((i, 'gt0'))
        bres = {'ok': True, 'n': 0}

        def visit_boundary(k, row):
            for i, kind in need.get(k, ()):
                v = h_from_N(row, k, i)
                bres['ok'] = bres['ok'] and (v <= 0 if kind == 'le0' else v > 0)
                bres['n'] += 1
        t2 = time.time()
        N_stream(max(tau[1:]), I_CERT + 2, visit_boundary)
        tb = time.time() - t2
        bad_at_tau = 0
        for i in range(1, min(I_CERT, 100) + 1):
            lnc, rho = lnc_float(i)
            lnB, B, X, E = thm_log_bound(tau[i], rho, rho ** 3, rho * rho + 3 * i)
            if B is None or B >= 1:
                bad_at_tau += 1
        refuse = certify(last_bad, Ks, K_SCAN // 3, I_CERT) is None
        lb2 = stream_scan(min(K_SCAN, 2000), 60, kfix=-3)[0]
        tau2 = [x + 1 for x in lb2[1:41]]
        report('b9b-rev', bres['ok'] and bres['n'] == 2 * I_CERT and bad_at_tau == min(I_CERT, 100) and refuse and tau2 != TAU40,
               '反向检查：用 N 三角公式（与扫描不同的算法）独立算出 h_{τ_i-1,i}<=0<h_{τ_i,i}，1<=i<=%d 全部成立（%d 个值，%.1f s）；'
               '定理 1 的界在 k=τ_i 处 >=1（1<=i<=%d 全部）——门槛附近必须靠精确计算；扫描上限取 %d 时认证函数拒绝输出；'
               '递推改成 (k-3) 后 τ_1..τ_40 改变（前几项 %s）'
               % (I_CERT, bres['n'], tb, min(I_CERT, 100), K_SCAN // 3, tau2[:6]))
    else:
        report('b9b-rev', False, '没有认证结果，反向检查不做')

    # b9b-model（数值佐证）
    ts, xs = xi_star()
    alpha = 1 / xs
    uni = all((g_r(0.001 * s) < g_r(0.001 * (s + 1))) == (0.001 * (s + 1) < ts + 0.001) for s in range(1, 900)
              if abs(0.001 * s - ts) > 0.002)
    devs = [ell[k] - xs * k for k in range(1000, K_SCAN + 1) if ell.get(k) is not None]
    w0 = 200 if full else 40
    w1 = min(I_CERT, 579)
    mean_diff = (tau[w1] - tau[w0 + 1]) / (w1 - w0 - 1) if tau else float('nan')
    md_tol = 0.05 if full else 0.3
    h300 = h_full_rows(300, want={300})[300]
    rc_ok, rc_dev = True, []
    for tau_ in (Fr(1, 10), Fr(1, 2), Fr(1), Fr(2), Fr(5), Fr(10)):
        c = count_roots(h300, -tau_, Fr(0))
        dev = c - 300 * neg_cdf(float(tau_))
        rc_dev.append(round(dev, 1))
        rc_ok = rc_ok and abs(dev) <= 4
    npos = count_roots(h300, Fr(1), Fr(10 ** 9))
    nnear = count_roots(h300, Fr(1), Fr(21, 20))

    def rate_diff(k, xi):
        i = int(xi * k)
        s_lo, s_hi = 1e-300, ts
        for _ in range(300):
            m = (s_lo + s_hi) / 2
            if g_r(m) < i / k:
                s_lo = m
            else:
                s_hi = m
        s = (s_lo + s_hi) / 2
        model = math.log(1 - s) - math.log(psi_r(s)) / 3 - (i / k) * math.log(s)
        return lnbig(vals[(k, i)]) / k - math.log(k / (3 * math.e)) / 3 - model
    rats = [rate_diff(kB, xi) / rate_diff(kA, xi) for xi in xis]
    peak_ok = True
    for s in (1e-12, 1e-9, 1e-6, 1e-4, 1e-3, 0.01, 0.03, 0.05, 0.07, 0.075):
        base = Phi_c(s)
        peak_ok = peak_ok and all(Phi_c(s * cmath.exp(1j * math.pi * n / 4000)) < base for n in range(1, 4001))
    # 分窗变号数
    k_sign = 1500 if full else 600
    hk = h_full_rows(k_sign, want={k_sign})[k_sign]
    path = saddle_path(2 / 3 - 1e-6)
    ident = path_integral(path, xs, 2 / 3)
    wins = [(0.0, xs), (xs, 0.13), (0.13, 0.16), (0.16, 0.30), (0.30, 0.35), (0.35, 0.60), (0.60, 0.65)]
    sg = [(i, 1 if c > 0 else -1) for i, c in enumerate(hk) if c != 0]
    changes = [sg[n + 1][0] for n in range(len(sg) - 1) if sg[n][1] != sg[n + 1][1]]
    win_res, win_ok = [], True
    for a, b in wins:
        act = sum(1 for i in changes if a * k_sign <= i < b * k_sign)
        mod = k_sign * path_integral(path, a, b) if a >= xs else 0.0
        win_res.append((a, b, act, round(mod, 1)))
        tol = max(3.0, (0.10 if full else 0.15) * mod)
        win_ok = win_ok and abs(act - mod) <= tol
    model_ok = (abs(xs - 0.1040749769) < 1e-9 and uni and max(abs(d) for d in devs) <= 8 and abs(mean_diff - alpha) < md_tol
                and rc_ok and npos == 100 and nnear >= 70 and all(abs(r - 2 ** (-1 / 3)) < 0.02 for r in rats) and peak_ok
                and win_ok and abs(ident - 1 / 3) < 1e-4)
    report('b9b-model', model_ok,
           '数值佐证（猜想 3，不是证明）：t*=%.10f，ξ*=g(t*)=%.10f，α*=1/ξ*=%.8f，g 在 (0,1) 单峰；1000<=k<=%d 时 ℓ_k-ξ*k ∈ [%.2f, %.2f]；'
           'τ 在 %d<i<=%d 上的平均差 %.4f（α*=%.4f）；k=300 时 (-τ,0) 的根数减模型 300F(τ) = %s（τ=0.1,0.5,1,2,5,10）、正根 %d 个、'
           '其中 %d 个在 (1,1.05)；增长率偏差之比（k=%d 对 %d）%s（2^(-1/3)=0.7937）；|t|=s（10^-12..0.075）的圆周上 Φ 在 θ=0 取严格最大；'
           'h_%d 分窗变号数（窗口、实际、模型）%s；恒等式 ∫arg t_s dξ/π=%.6f（=1/3，只说明路径延拓正确）'
           % (ts, xs, alpha, K_SCAN, min(devs), max(devs), w0 + 1, w1, mean_diff, alpha, rc_dev, npos, nnear, kB, kA,
              [round(r, 4) for r in rats], k_sign, ['[%.3f,%.3f):%d/%.1f' % w for w in win_res], ident))

    print('# elapsed %.1fs' % (time.time() - t_start))
    n_fail = RESULTS.count(False)
    print('SUMMARY b9b pass=%d fail=%d' % (RESULTS.count(True), n_fail))
    return n_fail


if __name__ == '__main__':
    sys.exit(1 if main('--full' in sys.argv) else 0)
