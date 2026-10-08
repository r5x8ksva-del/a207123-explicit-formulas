# -*- coding: utf-8 -*-
"""s13-b5skel 复核 r1：notes/14（骨架型两层和不存在）的独立核对。只用标准库，不导入仓库里的任何模块。

  r1-dp       自写 DP：U、E（以上升结尾 h_{k-1}<h_k）按最后两个值计数；容斥得 N、N^c、N^E；
              与按定义的掩码 DP（值域恰为 {1..q}）比对（k<=9，q<=5）
  r1-gfc      确认定义一致：P_m * (U^c 级数) = 1、P_m * (E 级数) = W_m - 1（mod x^(K+1)，m<=4）
  r1-num      Num_q = P_{q-1} F^T_q 的 x^(3q-1..K) 系数全为 0（T = N, N^c, N^E；q<=Q）
  r1-res      引理 14.4：由 Num_q 在 Q[x]/(b_w) 中精确算 u'(η)Res_η F^T_q（u' 直接按 x^2(3-2x)/(1-x)^2，
              Res = Num_q(η)/P'_{q-1}(η)），与闭式 -Λ y^(w+1) e^(-y)/(w! w^2 (1+z)) 的 z-展开逐项比较（w=1,2,3,4；w=4 可约，
              在环 Q[x]/(b_4) 中比较即对每个根比较）
  r1-subst    引理 14.5：用 r1-res 的 DP 留数代入 z(η,V)、乘 V^(f-e)/P(η,V)，与 α(1+η^bV)^(-e) τ^3 e^(-2τ/(1+τ)) (1+τ)^(-4)
              比较（w=2，8 组参数，b 含负数，e 含 ±1、±2）
  r1-norm     N(W~_2-1)=17/8、N(W~_2)=103/16、N(η)=1/2、N(1-η)=1，17、103 为素数；
  r1-Nc       N^c、b=1：代入后系数全在 Q ⇔ e=0 且 3(d+1)=d-c+f（R 式参数、两组满足条件的、旧条件成立但 e=1 的、违反的）
  r1-lem141   引理 14.1：随机 A(p,s)（有理数）与参数，按定义算 X(k,q)（含负 k），与行母函数闭式比较
  r1-lem142   引理 14.2：同一批数据，二元恒等式（含低 p 修正 E_p，m=q0+e>=2 的组有修正）；去掉修正项时不成立（反向）
  r1-numfib   数值：b_2 实根 ≈0.5898、复根模 ≈0.9207；情形 C：r=2,4..10 时 U=x^r/(1-x) 过 ξ 的纤维中有不是任何 b_v 根的点
"""
import random
import sys
from fractions import Fraction as Fr
from math import comb, factorial

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def gbinom(n, j):
    """广义二项式 C(n,j)，j>=0，n 任意整数。"""
    r = Fr(1)
    for t in range(j):
        r = r * (n - t) / (t + 1)
    return r


def cbin(n, r):
    """报告的约定：除非 0<=r<=n，否则为 0。"""
    return comb(n, r) if 0 <= r <= n else 0


# ============================================================ 1. 计数 DP（按定义）
def U_dp(m, K):
    """长 k、取值 {0..m} 的合法序列数 U 与其中以上升结尾（h_{k-1}<h_k）的个数 E，k=0..K。m=-1 时只有空序列。"""
    n = m + 1
    U = [0] * (K + 1)
    E = [0] * (K + 1)
    U[0] = 1
    if n == 0:
        return U, E
    if K >= 1:
        U[1] = n
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
        E[k] = sum(v for (a, b), v in cnt.items() if a < b)
    return U, E


def tri_tables(Q, K):
    UE = {m: U_dp(m, K) for m in range(-1, Q)}
    N, Nc, NE = {}, {}, {}
    for q in range(Q + 1):
        for k in range(K + 1):
            sN = sE = 0
            for i in range(q + 1):
                U, E = UE[i - 1]
                sN += (-1) ** (q - i) * comb(q, i) * U[k]
                sE += (-1) ** (q - i) * comb(q, i) * E[k]
            N[k, q], NE[k, q], Nc[k, q] = sN, sE, sN - sE
    return N, Nc, NE, UE


def mask_dp(k, q):
    """按定义：长 k、值域恰为 {1..q}（这里记作 {0..q-1}）的合法词数 与 其中以上升结尾的个数。"""
    if k == 0:
        return (1, 0) if q == 0 else (0, 0)
    if q == 0:
        return (0, 0)
    if k == 1:
        return (1, 0) if q == 1 else (0, 0)
    full = (1 << q) - 1
    cnt = {}
    for a in range(q):
        for b in range(q):
            key = (a, b, (1 << a) | (1 << b))
            cnt[key] = cnt.get(key, 0) + 1
    for _ in range(k - 2):
        new = {}
        for (a, b, msk), v in cnt.items():
            for c in range(q):
                if b == c or (a >= b and a >= c):
                    key = (b, c, msk | (1 << c))
                    new[key] = new.get(key, 0) + v
        cnt = new
    tot = sum(v for (a, b, msk), v in cnt.items() if msk == full)
    asc = sum(v for (a, b, msk), v in cnt.items() if msk == full and a < b)
    return tot, asc


def pmul(A, B):
    C = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        if a:
            for j, b in enumerate(B):
                if b:
                    C[i + j] += a * b
    return C


def Ppoly(m):
    P = [1]
    for v in range(m + 1):
        P = pmul(P, [1, -1, 0, -v])
    return P


# ============================================================ 2. Q[x]/(b_w)
class Rw:
    def __init__(self, w):
        self.w = w
        self.ONE = [Fr(1), Fr(0), Fr(0)]
        self.ZERO = [Fr(0), Fr(0), Fr(0)]
        self.X = [Fr(0), Fr(1), Fr(0)]
        self.X2 = [Fr(0), Fr(0), Fr(1)]

    def red(self, poly):
        """多项式模 b_w = 1 - x - w x^3（x^3 = (1-x)/w），即在 η 处取值。"""
        c = [Fr(v) for v in poly] + [Fr(0)] * 3
        for dg in range(len(c) - 1, 2, -1):
            t = c[dg]
            if t:
                c[dg] = Fr(0)
                c[dg - 3] += t / self.w
                c[dg - 2] -= t / self.w
        return c[:3]

    def mul(self, a, b):
        p = [Fr(0)] * 5
        for i in range(3):
            if a[i]:
                for j in range(3):
                    if b[j]:
                        p[i + j] += a[i] * b[j]
        return self.red(p)

    @staticmethod
    def add(a, b):
        return [u + v for u, v in zip(a, b)]

    @staticmethod
    def sc(c, a):
        return [Fr(c) * u for u in a]

    def mat(self, a):
        cols = [a, self.mul(a, self.X), self.mul(a, self.X2)]
        return [[cols[j][r] for j in range(3)] for r in range(3)]

    def inv(self, a):
        M = [row + [self.ONE[r]] for r, row in enumerate(self.mat(a))]
        for col in range(3):
            piv = next(r for r in range(col, 3) if M[r][col] != 0)
            M[col], M[piv] = M[piv], M[col]
            pv = M[col][col]
            M[col] = [v / pv for v in M[col]]
            for r in range(3):
                if r != col and M[r][col] != 0:
                    fct = M[r][col]
                    M[r] = [M[r][t] - fct * M[col][t] for t in range(4)]
        return [M[r][3] for r in range(3)]

    def pw(self, a, n):
        base = a if n >= 0 else self.inv(a)
        r = self.ONE
        for _ in range(abs(n)):
            r = self.mul(r, base)
        return r

    def norm(self, a):
        M = self.mat(a)
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))

    def smul(self, A, B, Q):
        C = [self.ZERO] * (Q + 1)
        for i, a in enumerate(A[:Q + 1]):
            if any(a):
                for j in range(Q + 1 - i):
                    if j < len(B) and any(B[j]):
                        C[i + j] = self.add(C[i + j], self.mul(a, B[j]))
        return C

    def sexp_neg(self, Y, Q):
        out = [self.ONE] + [self.ZERO] * Q
        term = [self.ONE] + [self.ZERO] * Q
        for n in range(1, Q + 1):
            term = self.smul(term, Y, Q)
            out = [self.add(o, self.sc(Fr((-1) ** n, factorial(n)), t)) for o, t in zip(out, term)]
        return out

    def sbinom(self, cf, n, Q):
        """(1 + cf V)^n 的截断级数。"""
        out, coef, cp = [], Fr(1), self.ONE
        for k in range(Q + 1):
            out.append(self.sc(coef, cp))
            coef = coef * (n - k) / (k + 1)
            cp = self.mul(cp, cf)
        return out


def Wtilde(w):
    Wt = [0] * (3 * w + 3)
    Wt[0] = 1
    for j in range(1, w + 1):
        ff = 1
        for t in range(j):
            ff *= (w - t)
        Wt[3 * j + 2] += j * ff
    return Wt


def lam_elem(R, T):
    Wt = Wtilde(R.w)
    return {'N': R.red(Wt), 'E': R.red([0] + Wt[1:]), 'c': R.ONE}[T]


def residue_series(R, Nums, Q):
    """c_q = u'(η) Res_{x=η} (Num_q / P_{q-1})，q=0..Q；u' 按 x^2(3-2x)/(1-x)^2 直接算。"""
    w = R.w
    up = R.mul(R.red([0, 0, 3, -2]), R.inv(R.red([1, -2, 1])))
    bwp = R.red([-1, 0, -3 * w])
    out = []
    for q in range(Q + 1):
        if q - 1 < w:
            out.append(R.ZERO)
            continue
        den = bwp
        for v in range(q):
            if v != w:
                den = R.mul(den, R.red([1, -1, 0, -v]))
        out.append(R.mul(R.mul(up, R.red(Nums[q])), R.inv(den)))
    return out


def closed_series(R, T, Q, drop_1z=False):
    """-Λ_w(η) y^(w+1) e^(-y) / (w! w^2 (1+z))，y = η^(-3) z/(1+z)，按 z 展开到 z^Q。"""
    w = R.w
    e3 = R.pw(R.X, -3)
    y = [R.ZERO] + [R.sc((-1) ** (j - 1), e3) for j in range(1, Q + 1)]
    ex = R.sexp_neg(y, Q)
    yp = [R.ONE] + [R.ZERO] * Q
    for _ in range(w + 1):
        yp = R.smul(yp, y, Q)
    core = R.smul(yp, ex, Q)
    if not drop_1z:
        core = R.smul(core, [R.sc((-1) ** n, R.ONE) for n in range(Q + 1)], Q)
    cst = R.sc(Fr(-1, factorial(w) * w * w), lam_elem(R, T))
    return [R.mul(cst, t) for t in core]


_COMP = {}


def subst_lhs(R, cs, b, c, d, e, f, Q):
    """Σ_q c_q z(η,V)^q · V^(f-e)/P(η,V)，z(η,V) = η^(b-1)(1-η)V/(1+η^b V)。"""
    eta = R.X
    one_m = R.red([1, -1])
    eb = R.pw(eta, b)
    key = (id(cs), R.w, b, Q)
    if key not in _COMP:
        zV = R.smul([R.ZERO, R.mul(R.pw(eta, b - 1), one_m)] + [R.ZERO] * (Q - 1), R.sbinom(eb, -1, Q), Q)
        comp = [R.ZERO] * (Q + 1)
        pw_ = [R.ONE] + [R.ZERO] * Q
        for q in range(Q + 1):
            comp = [R.add(u, R.mul(cs[q], v)) for u, v in zip(comp, pw_)]
            pw_ = R.smul(pw_, zV, Q)
        _COMP[key] = comp
    comp = _COMP[key]
    a0 = R.mul(R.pw(eta, -(d - c) - b * (f - e)), R.pw(one_m, d + 1))
    return R.smul([R.mul(a0, t) for t in comp], R.sbinom(eb, -(e + 1), Q), Q)


def subst_rhs(R, T, b, c, d, e, f, Q):
    w = R.w
    eta = R.X
    one_m = R.red([1, -1])
    eb = R.pw(eta, b)
    a0 = R.mul(R.pw(eta, -(d - c) - b * (f - e)), R.pw(one_m, d + 1))
    alpha = R.mul(R.sc(Fr(-(w ** (w + 1)), factorial(w) * w * w), lam_elem(R, T)), a0)
    tc = R.pw(eta, b - 1)
    tau = [R.ZERO, tc] + [R.ZERO] * (Q - 1)
    wt = R.smul([R.sc(w, t) for t in tau], R.sbinom(tc, -1, Q), Q)      # wτ/(1+τ)
    ex = R.sexp_neg(wt, Q)
    tp = [R.ONE] + [R.ZERO] * Q
    for _ in range(w + 1):
        tp = R.smul(tp, tau, Q)
    core = R.smul(R.smul(tp, ex, Q), R.sbinom(tc, -(w + 2), Q), Q)
    return [R.mul(alpha, t) for t in R.smul(R.sbinom(eb, -e, Q), core, Q)]


# ============================================================ 3. Laurent 级数（带精度）与 V 级数
INF = 10 ** 9


class LS:
    """x 的截断 Laurent 级数：d 为 指数->系数，对指数 <= prec 精确。"""
    __slots__ = ('d', 'prec')

    def __init__(self, d, prec):
        self.prec = min(prec, INF)
        self.d = {k: v for k, v in d.items() if v != 0 and k <= self.prec}

    def val(self):
        return min(self.d) if self.d else self.prec + 1

    def __add__(self, o):
        p = min(self.prec, o.prec)
        d = dict(self.d)
        for k, v in o.d.items():
            d[k] = d.get(k, 0) + v
        return LS(d, p)

    def __neg__(self):
        return LS({k: -v for k, v in self.d.items()}, self.prec)

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        if isinstance(o, (int, Fr)):
            return LS({k: v * o for k, v in self.d.items()}, self.prec)
        p = min(self.prec + o.val(), o.prec + self.val())
        d = {}
        for k1, v1 in self.d.items():
            for k2, v2 in o.d.items():
                k = k1 + k2
                if k <= p:
                    d[k] = d.get(k, 0) + v1 * v2
        return LS(d, p)


ZLS = LS({}, INF)


def lsx(n, cf=1):
    return LS({n: Fr(cf)}, INF)


def omx(n, XP):
    """(1-x)^n：n>=0 精确；n<0 截断到 x^XP。"""
    if n >= 0:
        return LS({j: Fr((-1) ** j * comb(n, j)) for j in range(n + 1)}, INF)
    return LS({j: Fr(comb(-n + j - 1, j)) for j in range(XP + 1)}, XP)


def ls_eq(A, B):
    """在两边都精确的范围内比较；返回 (是否相等, 比较到的指数上界, 起点)。"""
    p = min(A.prec, B.prec)
    keys = [k for k in set(A.d) | set(B.d) if k <= p]
    ok = all(A.d.get(k, 0) == B.d.get(k, 0) for k in keys)
    lo = min(keys) if keys else p
    return ok, p, lo


class VS:
    """V 的截断级数（指数可为负），系数为 LS，对 V^n（n<=N）精确。"""

    def __init__(self, d, N):
        self.N = N
        self.d = {n: v for n, v in d.items() if n <= N and v.d}

    def vmin(self):
        return min(self.d) if self.d else self.N + 1

    def __add__(self, o):
        N = min(self.N, o.N)
        d = {}
        for n in set(self.d) | set(o.d):
            if n <= N:
                d[n] = self.d.get(n, ZLS) + o.d.get(n, ZLS)
        return VS(d, N)

    def __mul__(self, o):
        if isinstance(o, LS):
            return VS({n: v * o for n, v in self.d.items()}, self.N)
        N = min(self.N + o.vmin(), o.N + self.vmin())
        d = {}
        for n1, A in self.d.items():
            for n2, B in o.d.items():
                n = n1 + n2
                if n <= N:
                    d[n] = d.get(n, ZLS) + A * B
        return VS(d, N)


# ============================================================ 4. 引理 14.1、14.2 的随机检验
def lemma_tests(par, A, KMAX, XP, NV):
    a, b, c, d, e, f, s0, q0 = par
    r = 1 - a
    ps = sorted(set(p for (p, s) in A))
    PSI = {}
    for p in ps:
        tot = ZLS
        for (pp, s), v in A.items():
            if pp == p:
                tot = tot + lsx(r * s) * omx(-s, XP) * v
        PSI[p] = tot

    def X_ls(q):
        sup = [(p, s) for (p, s) in A if cbin(q + e, p + f) != 0]
        if not sup:
            return LS({}, KMAX)
        kmin = min(r * s + q + d - c - b * p for (p, s) in sup)
        dd = {}
        for k in range(kmin, KMAX + 1):
            v = sum(A[(p, s)] * cbin(q + e, p + f) * cbin(k + a * s + b * p + c, s + q + d) for (p, s) in sup)
            if v:
                dd[k] = v
        return LS(dd, KMAX)

    Xs = {q: X_ls(q) for q in range(q0, NV + 1)}
    # ---- 引理 14.1
    ok141, minwin = True, INF
    for q in range(q0, min(q0 + 5, NV) + 1):
        assert q + d + s0 >= 0
        S = ZLS
        for p in ps:
            S = S + lsx(-b * p) * PSI[p] * cbin(q + e, p + f)
        rhs = lsx(q + d - c) * omx(-(q + d + 1), XP) * S
        ok, p_, lo = ls_eq(Xs[q], rhs)
        ok141 &= ok
        minwin = min(minwin, p_ - lo)
    # ---- 引理 14.2（乘以 V^(f-e) 后比较）
    G = VS({j: lsx(b * j, gbinom(-(e + 1), j)) for j in range(NV + 1)}, NV)
    zV = VS({j + 1: lsx(b - 1 + b * j, (-1) ** j) * omx(1, XP) for j in range(NV)}, NV)
    C0 = lsx(-(d - c) - b * (f - e)) * omx(d + 1, XP)
    lhs = VS({}, NV)
    zq = VS({0: lsx(0)}, NV)
    for q in range(0, NV + 1):
        if q >= q0:
            lhs = lhs + (G * zq) * (Xs[q] * C0)
        zq = zq * zV
    psi_part = VS({p + f - e: PSI[p] for p in ps}, NV)
    m = q0 + e
    corr = VS({}, NV)
    ncorr = 0
    for p in ps:
        if 0 <= p + f < m:
            inner = {}
            for q in range(p + f - e, q0):
                cq = cbin(q + e, p + f)
                for j in range(0, NV - q + 1):
                    inner[q + j] = inner.get(q + j, ZLS) + lsx(b * q + b * j, gbinom(-(e + 1 + q), j) * cq)
            corr = corr + VS(inner, NV) * (PSI[p] * lsx(-b * p - b * (f - e)))
            ncorr += 1
    rhs = psi_part + VS({n: -v for n, v in corr.d.items()}, corr.N)

    def vs_eq(Aa, Bb):
        N = min(Aa.N, Bb.N)
        ok, win = True, INF
        for n in set(Aa.d) | set(Bb.d):
            if n <= N:
                o, p_, lo = ls_eq(Aa.d.get(n, ZLS), Bb.d.get(n, ZLS))
                ok &= o
                win = min(win, p_ - lo)
        return ok, win

    ok142, win142 = vs_eq(lhs, rhs)
    nocorr_ok, _ = vs_eq(lhs, psi_part)
    return ok141, minwin, ok142, win142, ncorr, nocorr_ok


# ============================================================ 5. 数值根（Durand-Kerner）
def roots(coeffs):
    n = len(coeffs) - 1
    lead = coeffs[-1]
    a = [complex(c) / lead for c in coeffs]
    z = [complex(0.4, 0.9) ** k for k in range(n)]
    for _ in range(5000):
        nz = []
        for k in range(n):
            num = sum(a[j] * z[k] ** j for j in range(n + 1))
            den = 1
            for j in range(n):
                if j != k:
                    den *= (z[k] - z[j])
            nz.append(z[k] - num / den)
        if max(abs(nz[k] - z[k]) for k in range(n)) < 1e-15:
            z = nz
            break
        z = nz
    return z


def main():
    Q, K = 10, 40
    N, Nc, NE, UE = tri_tables(Q, K)
    tabs = {'N': N, 'c': Nc, 'E': NE}
    # ---- r1-dp
    okdp = True
    for k in range(0, 10):
        for q in range(0, 6):
            tot, asc = mask_dp(k, q)
            okdp &= (tot == N[k, q] and asc == NE[k, q])
    report('r1-dp', okdp, '容斥得到的 N、N^E（自写 U/E DP）与按定义的掩码 DP 一致（0<=k<=9，0<=q<=5）')
    # ---- r1-gfc
    okg = True
    def padd(A_, B_):
        n_ = max(len(A_), len(B_))
        return [(A_[i] if i < len(A_) else 0) + (B_[i] if i < len(B_) else 0) for i in range(n_)]
    for m in range(0, 5):
        U, E = UE[m]
        Pm = Ppoly(m)
        Wm = [1]
        for j in range(1, m + 1):
            Wm = padd(Wm, pmul([0, 0, j], Ppoly(j - 1)))      # W_m = 1 + x^2 Σ_j j P_{j-1}
        prodc = pmul(Pm, [U[k] - E[k] for k in range(K + 1)])[:K + 1]
        prode = pmul(Pm, E[:K + 1])[:K + 1]
        okg &= prodc == [1] + [0] * K
        wm1 = Wm[:] + [0] * (K + 1 - len(Wm))
        wm1[0] -= 1
        okg &= prode == wm1[:K + 1]
    report('r1-gfc', okg, 'P_m·Σ U^c x^k = 1、P_m·Σ E x^k = W_m-1（mod x^%d，m<=4）：「上升结尾」的定义与 1/P_m、(W_m-1)/P_m 一致' % (K + 1))
    # ---- r1-num
    Nums = {T: {} for T in tabs}
    oknum = True
    for T, tab in tabs.items():
        for q in range(0, Q + 1):
            Fq = [tab[k, q] for k in range(K + 1)]
            pr = pmul(Ppoly(q - 1), Fq)[:K + 1]
            dg = 3 * q - 2 if q >= 1 else 0
            oknum &= all(v == 0 for v in pr[dg + 1:])
            Nums[T][q] = pr[:dg + 1]
    report('r1-num', oknum, 'Num_q = P_{q-1} F^T_q 的 x^(3q-1..%d) 系数全为 0（T=N,N^c,N^E；q<=%d）' % (K, Q))
    # ---- r1-res（引理 14.4）
    okres, info, RS = True, [], {}
    for w in (1, 2, 3, 4):
        R = Rw(w)
        for T in ('N', 'c', 'E'):
            act = residue_series(R, Nums[T], Q)
            pred = closed_series(R, T, Q)
            ok = act == pred
            nz = sum(1 for t in act if any(t))
            okres &= ok and nz == Q - w
            info.append('w%d%s:%s/%d' % (w, T, ok, nz))
            RS[w, T] = act
    # 反向：去掉 1/(1+z) 后不符
    R2 = Rw(2)
    rev_res = all(RS[2, T] != closed_series(R2, T, Q, drop_1z=True) for T in ('N', 'c', 'E'))
    report('r1-res', okres and rev_res, '引理 14.4：由 DP 的 Num_q 在 Q[x]/(b_w) 中算的 u\'(η)Res_η F_q 与闭式逐项一致（q<=%d；'
           '各组非零项数 = Q-w）：%s；反向：去掉 1/(1+z) 时三种 T 都不符：%s' % (Q, ' '.join(info), rev_res))
    # ---- r1-subst（引理 14.5，w=2，DP 留数）
    cases = [('E', 1, 0, 0, 0, 0), ('N', -1, 2, -2, 1, -1), ('c', 0, -1, 1, -2, 2), ('E', 2, 1, -1, 2, 0),
             ('N', 3, 0, 0, -1, 1), ('c', -2, 3, 2, 0, -2), ('E', -1, -3, 1, 1, 1), ('N', 1, -1, -1, 2, 3)]
    oks, bad = True, []
    for (T, b, c, d, e, f) in cases:
        L = subst_lhs(R2, RS[2, T], b, c, d, e, f, Q)
        Rr = subst_rhs(R2, T, b, c, d, e, f, Q)
        if L != Rr:
            oks, bad = False, bad + [(T, b, c, d, e, f)]
    report('r1-subst', oks, '引理 14.5（w=2，DP 留数代入）：8 组 (T,b,c,d,e,f)（b∈{-2,-1,0,1,2,3}，e∈{-2..2}）V^<=%d 逐项一致%s'
           % (Q, '' if oks else '；不符 %s' % bad))
    # ---- r1-norm
    nW1, nW, ne, nom = R2.norm(lam_elem(R2, 'E')), R2.norm(lam_elem(R2, 'N')), R2.norm(R2.X), R2.norm(R2.red([1, -1]))
    isp = lambda n: n >= 2 and all(n % t for t in range(2, int(n ** 0.5) + 1))
    okn = nW1 == Fr(17, 8) and nW == Fr(103, 16) and ne == Fr(1, 2) and nom == 1 and isp(17) and isp(103)
    report('r1-norm', okn, 'N(W~_2-1)=%s、N(W~_2)=%s、N(η)=%s、N(1-η)=%s；17、103 是素数' % (nW1, nW, ne, nom))
    # ---- r1-Nc：b=1 时系数全有理 ⇔ e=0 且 3(d+1)=d-c+f
    def all_rat(T, c, d, e, f):
        L = subst_lhs(R2, RS[2, T], 1, c, d, e, f, Q)
        return all(t[1] == 0 and t[2] == 0 for t in L)
    grid = [(c, d, e, f) for c in range(-2, 3) for d in (-2, -1, 0) for e in (-1, 0, 1) for f in (-1, 0, 1)]
    okc = all(all_rat('c', *g) == (g[2] == 0 and 3 * (g[1] + 1) == g[1] - g[0] + g[3]) for g in grid)
    old_but_e = [g for g in grid if 3 * (g[1] + 1) == g[1] - g[0] + g[3] - g[2] and g[2] != 0]
    okE = not any(all_rat(T, *g) for T in ('N', 'E') for g in grid[::7])
    report('r1-Nc', okc and okE and all_rat('c', -1, -1, 0, 0),
           'N^c、b=1：在 %d 组 (c,d,e,f) 上「代入后系数全在 Q」⇔「e=0 且 3(d+1)=d-c+f」：%s（其中旧条件成立但 e≠0 的 %d 组都不是）；'
           'R 式参数全有理；N、N^E 抽查 %d 组都不是：%s' % (len(grid), okc, len(old_but_e), len(grid[::7]), okE))
    # ---- r1-lem141 / r1-lem142（随机）
    rng = random.Random(20261008)
    sets = []
    while len(sets) < 16:
        a = rng.choice([-1, -2, -3])
        b = rng.choice([-1, 0, 1, 2])
        c = rng.randint(-3, 3)
        d = rng.randint(-3, 2)
        e = rng.randint(-2, 2)
        f = rng.randint(-2, 2)
        s0 = rng.randint(-2, 1)
        qmin = max(1, -e, -d - s0)
        if len(sets) < 12:
            q0 = max(qmin, 2 - e) + rng.randint(0, 1)          # m = q0+e >= 2：有低 p 修正
        else:
            q0 = qmin                                       # m 任意（可为 0、1）
        A = {}
        for s in range(s0, s0 + 3):
            for pf in range(0, 4):
                if rng.random() < 0.6:
                    A[(pf - f, s)] = Fr(rng.randint(-4, 4), rng.randint(1, 3))
        A[(-f, s0)] = Fr(rng.choice([1, 2, -1, 3]), rng.randint(1, 3))
        A = {k: v for k, v in A.items() if v != 0}
        sets.append(((a, b, c, d, e, f, s0, q0), A))
    ok1 = ok2 = okrev = True
    win1 = win2 = INF
    nm2, ncorr_sets = 0, 0
    for par, A in sets:
        q0, e = par[7], par[4]
        NV = q0 + 4
        r141, w1, r142, w2, ncorr, nocorr_ok = lemma_tests(par, A, KMAX=36, XP=60, NV=NV)
        ok1 &= r141
        ok2 &= r142
        win1, win2 = min(win1, w1), min(win2, w2)
        if q0 + e >= 2:
            nm2 += 1
        if ncorr:
            ncorr_sets += 1
            okrev &= not nocorr_ok
    report('r1-lem141', ok1, '引理 14.1：16 组随机参数（a∈{-1,-2,-3}，b∈{-1,0,1,2}，c,d,e,f,s_0 含负数）与有理系数 A(p,s)，'
           '按定义算 X(k,q)（含负 k）与行母函数闭式一致；每个比较窗口至少 %d 个系数' % win1)
    report('r1-lem142', ok2 and okrev, '引理 14.2（乘 V^(f-e) 后逐 V^n 比较，含 V 的负幂抵消）：16 组全部一致（其中 m=q0+e>=2 的 %d 组、'
           '有低 p 修正的 %d 组；x 窗口至少 %d 个系数）：%s；反向：去掉修正项后这 %d 组都不一致：%s'
           % (nm2, ncorr_sets, win2, ok2, ncorr_sets, okrev))
    # ---- r1-numfib
    rb2 = roots([1, -1, 0, -2])
    real = [z for z in rb2 if abs(z.imag) < 1e-12]
    cplx = [z for z in rb2 if abs(z.imag) >= 1e-12]
    okb2 = len(real) == 1 and abs(real[0].real - 0.5898) < 1e-4 and all(abs(abs(z) - 0.9207) < 1e-4 for z in cplx)
    okb2 &= all(abs(abs(z) ** 2 - 1 / (2 * real[0].real)) < 1e-12 for z in cplx)
    xi = [z for z in roots([1, -1, 0, -1]) if abs(z.imag) < 1e-12][0].real
    finfo, okC = [], True
    for rr in (2, 4, 5, 6, 7, 8, 9, 10):
        U0 = xi ** (rr - 3)
        co = [-U0, U0] + [0] * (rr - 2) + [1]               # x^r + U0 x - U0
        rs = roots(co)
        has_xi = any(abs(z - xi) < 1e-9 for z in rs)
        free = 0
        for z in rs:
            wv = (1 - z) / z ** 3
            if abs(z - 1) < 1e-9:
                continue
            if not (abs(wv.imag) < 1e-7 and abs(wv.real - round(wv.real)) < 1e-7 and round(wv.real) >= 0):
                free += 1
        mind = min(abs(rs[i] - rs[j]) for i in range(len(rs)) for j in range(i))
        upxi = xi ** (rr - 1) * (rr - (rr - 1) * xi) / (1 - xi) ** 2
        okC &= has_xi and free >= 1 and abs(upxi) > 1e-3
        finfo.append('r=%d:自由点%d,最小根距%.2g' % (rr, free, mind))
    report('r1-numfib', okb2 and okC, '数值：b_2 实根 %.6f、复根模 %.6f（|η_2|^2=1/(2η_1)）；情形 C 纤维（ξ 在其中、U\'(ξ)≠0）：%s'
           % (real[0].real, abs(cplx[0]), '，'.join(finfo)))


if __name__ == '__main__':
    main()
    n_pass = sum(RES)
    n_fail = len(RES) - n_pass
    print('SUMMARY s13-b5skel-r1 pass=%d fail=%d' % (n_pass, n_fail))
    sys.exit(0 if n_fail == 0 else 1)
