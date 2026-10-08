# -*- coding: utf-8 -*-
"""表 B 的 B5（续）：骨架型两层和不存在 的核对脚本（2026-10-08）。证明见 notes/14-主Agent-表B-B5-骨架型两层和不存在.md。

逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b5s pass=<n> fail=<n>」。只用标准库；K_i 的运算取自 check_b4.py，
U、U^c 的真值取自 code/core.py 与 check_b4.py 的按定义 DP。
记号：b_v = 1-x-v x^3，K_2 = Q[x]/(b_2)，η 为 b_2 的根（1-η = 2η^3），u = x^3/(1-x)，u'(η) = (3-2η)/(4η^4)。
  骨架型表示：T(k,q) = sum_{s>=s0} sum_p A(p,s) C(q+e,p+f) C(k+as+bp+c, s+q+d)（k>=k0，q>=q0）。
  V = x^(1-b) z/(1-x-xz)，z = V x^(b-1)(1-x)/(1+x^b V)，P = x^(d-c+b(f-e)) (1-x)^(-(d+1)) V^(f-e) (1+x^b V)^(e+1)。
  b5s-res     引理 14.4（w=2）：sum_q u'(η)Res_η F_q z^q = -(Λ(η)/(8(1+z))) y^3 e^(-y)，y = η^(-3) z/(1+z)；Λ = W~_2-1（N^E）、W~_2（N）、
              1（N^c）；左边的留数由闭式母函数（E_M = x^2 sum_j j/(b_j..b_M)、G_M = W_M/P_M、1/P_M）按留数的定义在 K_2 中算
              （不经过引理 14.4 的化简，也不经过计数；q<=14）
  b5s-resw    引理 14.4 对一般纤维：w = 1, 3 时 sum_q u'(η)Res_η F_q z^q = -Λ_w(η) y^(w+1) e^(-y)/(w! w^2 (1+z))，
              y = η^(-3) z/(1+z)，η 为 b_w 的根，Λ_w = W~_w-1、W~_w、1（q<=12，同样由闭式按留数定义在 K_w 中算）
  b5s-subst   引理 14.5：代入 z = z(η,V)、乘 1/P 后等于 α(η)(1+η^b V)^(-e) V^(e-f) τ^3 e^(-2τ/(1+τ)) (1+τ)^(-4)，τ = η^(b-1) V，
              α = -Λ(η) η^(-(d-c)-b(f-e)) (1-η)^(d+1)（b in {-1,0,1,2}，若干 (c,d,e,f)；V 的阶 <= 12）
  b5s-norm    N(W~_2-1) = 17/8、N(W~_2) = 103/16、N(η) = 1/2、N(1-η) = 1，17、103 是素数；于是 b=1 时 N(α) 的 17-进（N^E）/103-进（N）
              赋值为 1，α 不是有理数
  b5s-Nc      对照：N^c 取 R 式的参数 (a,b,c,d,e,f) = (-2,1,-1,-1,0,0) 时代入后每个 V 系数都是有理数；违反 3(d+1) = d-c+f-e 的参数、
              以及满足它但 e≠0 的参数都不是（定理 14.1(ii)：e=0 且 3(d+1)=d-c+f）
  b5s-Rform   R 式本身：N^c(k,q) = sum_{s,p} C(q,p) R(p,s) C(k-2s+p-1, s+q-1)，R(p,s) = sum_i (-1)^(p-i) C(p,i) S(i-1+s,i-1)
              （1<=q<=10，0<=k<=30，按定义的 DP）
  b5s-bivar   §2 的二元母函数恒等式（含低 p 的修正项）端到端核对：对 N^c 与 R 式，只用 q>=q0 的行（q0 = 1、3）时，
              h_p = psi_p(u) - sum_{p'<q0} psi_{p'}(u) x^(p-p') sum_{q=p'}^{q0-1} C(q,p')(-1)^(p-q) C(p,q)，psi_p = sum_s R(p,s)u^s
              （p<=9，x 的阶 <= 40）；去掉修正项时不成立
  b5s-fiber1  a ≠ -2 的情形用到的事实（数值佐证，证明见 A20）：U = x^r/(1-x)（r = 1-a = 2,4,5,6）过 ξ 的纤维里有不是任何 b_w 的根的点
  b5s-rev     反向检查：把 W~_2 的 x^8 系数 4 改成 3（扰动闭式里的留数元）时，范数不再是 103/16，b5s-res 与 b5s-subst 的 N 部分
              都不再成立；把 e^(-2τ/(1+τ)) 换成 1 时 b5s-subst 不成立
"""
import os
import sys
from fractions import Fraction as Fr
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'code'))
sys.path.insert(0, HERE)
from core import U_fast_table  # noqa: E402
from check_b4 import red, kmul, knorm, Uc_table, is_prime  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []
I = 2
ZERO, ONE = [Fr(0)] * 3, [Fr(1), Fr(0), Fr(0)]
X = [Fr(0), Fr(1), Fr(0)]
NV = 12


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


# ---------------------------------------------------------------- K_2 的运算
def add(a, b):
    return [p + q for p, q in zip(a, b)]


def sc(c, a):
    return [Fr(c) * p for p in a]


def mul(a, b):
    return kmul(a, b, I)


def inv(a):
    cols = [mul(a, e) for e in (ONE, X, [Fr(0), Fr(0), Fr(1)])]
    M = [[cols[j][r] for j in range(3)] + [ONE[r]] for r in range(3)]
    for c in range(3):
        p = next(r for r in range(c, 3) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]
        M[c] = [v / pv for v in M[c]]
        for r in range(3):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [M[r][t] - f * M[c][t] for t in range(4)]
    return [M[r][3] for r in range(3)]


def xp(n):
    e, base = ONE, (X if n >= 0 else inv(X))
    for _ in range(abs(n)):
        e = mul(e, base)
    return e


def kpow(a, n):
    e, base = ONE, (a if n >= 0 else inv(a))
    for _ in range(abs(n)):
        e = mul(e, base)
    return e


ETA3 = xp(3)
OME = add(ONE, sc(-1, X))                                  # 1-η = 2η^3
BV = {v: sc(2 - v, ETA3) for v in range(0, 40) if v != 2}  # b_v(η) = (2-v)η^3
B2P = add(sc(-1, ONE), sc(-6, xp(2)))                       # b_2'(η)
UP = mul(add(sc(3, ONE), sc(-2, X)), inv(sc(4, xp(4))))    # u'(η)
WT2 = red([1, 0, 0, 0, 0, 2, 0, 0, 4], I)                   # W~_2 = 1 + 2x^5 + 4x^8
WT2M1 = red([0, 0, 0, 0, 0, 2, 0, 0, 4], I)


def P_at(j):
    """P_{j}(η) = b_0...b_j (η)。j>=2 时含 b_2(η)=0。"""
    r = ONE
    for v in range(0, j + 1):
        if v == 2:
            return ZERO
        r = mul(r, BV[v])
    return r


def res_E(M):
    """u'(η) Res_η E_M（按定义）。"""
    if M < 2:
        return ZERO
    tot = ZERO
    for j in (1, 2):
        den = B2P
        for v in range(j, M + 1):
            if v != 2:
                den = mul(den, BV[v])
        tot = add(tot, sc(j, mul(xp(2), inv(den))))
    return mul(UP, tot)


def res_Pinv(M):
    if M < 2:
        return ZERO
    den = B2P
    for v in range(0, M + 1):
        if v != 2:
            den = mul(den, BV[v])
    return mul(UP, inv(den))


def res_G(M):
    """u'(η) Res_η G_M，G_M = W_M/P_M，W_M(η) 按定义 1 + η^2 sum_j j P_{j-1}(η) 计算。"""
    if M < 2:
        return ZERO
    W = ONE
    for j in range(1, M + 1):
        W = add(W, sc(j, mul(xp(2), P_at(j - 1))))
    return mul(W, res_Pinv(M))


def row_res(q, kind):
    f = {'E': res_E, 'c': res_Pinv, 'N': res_G}[kind]
    tot = ZERO
    for M in range(0, q):
        tot = add(tot, sc((-1) ** (q - 1 - M) * comb(q, M + 1), f(M)))
    return tot


# ---------------------------------------------------------------- K_2 系数的截断幂级数（关于 z 或 V）
def s_mul(A, B, N=NV):
    C = [ZERO] * (N + 1)
    for i, a in enumerate(A[:N + 1]):
        if a == ZERO:
            continue
        for j in range(N + 1 - i):
            if j < len(B) and B[j] != ZERO:
                C[i + j] = add(C[i + j], mul(a, B[j]))
    return C


def s_scal(c, A):
    return [mul(c, a) for a in A]


def s_const(c, N=NV):
    return [c] + [ZERO] * N


def s_exp_neg(Y, N=NV):
    out, term = s_const(ONE, N), s_const(ONE, N)
    for n in range(1, N + 1):
        term = s_mul(term, Y, N)
        out = [add(o, sc(Fr((-1) ** n, factorial(n)), t)) for o, t in zip(out, term)]
    return out


def s_compose(A, Zs, N=NV):
    out, pw = s_const(ZERO, N), s_const(ONE, N)
    for k in range(N + 1):
        out = [add(o, mul(A[k], p)) for o, p in zip(out, pw)]
        pw = s_mul(pw, Zs, N)
    return out


def s_binom(c, n, N=NV):
    """(1 + c V)^n，c ∈ K_2，n 可为负。"""
    out = []
    cf, cp = Fr(1), ONE
    for k in range(N + 1):
        out.append(sc(cf, cp))
        cf = cf * Fr(n - k, k + 1)
        cp = mul(cp, c)
    return out


def s_inv(A, N=NV):
    """A 的常数项可逆。"""
    a0 = inv(A[0])
    out = [a0]
    for n in range(1, N + 1):
        s = ZERO
        for k in range(1, n + 1):
            if k < len(A) and A[k] != ZERO:
                s = add(s, mul(A[k], out[n - k]))
        out.append(mul(sc(-1, s), a0))
    return out


def is_rat(a):
    return a[1] == 0 and a[2] == 0


LAM = {'E': WT2M1, 'N': WT2, 'c': ONE}


def main():
    # ---- b5s-res
    N = 14
    w = [ZERO] + [sc((-1) ** (n - 1), ONE) for n in range(1, N + 1)]
    inv1z = [sc((-1) ** n, ONE) for n in range(N + 1)]
    y = s_scal(xp(-3), w)
    y3e = s_mul(s_mul(s_mul(y, y, N), y, N), s_exp_neg(y, N), N)
    okr, info = True, []
    for kind in ('E', 'N', 'c'):
        pred = s_scal(sc(Fr(-1, 8), LAM[kind]), s_mul(inv1z, y3e, N))
        act = [row_res(q, kind) for q in range(N + 1)]
        okr &= (act == pred)
        info.append('%s:%s' % (kind, act == pred))
    report('b5s-res', okr, '引理 14.4（w=2）：留数级数（由 E_M、G_M、1/P_M 的闭式按留数定义在 K_2 中算）与闭式一致，q<=%d（%s）'
           % (N, ', '.join(info)))

    # ---- b5s-resw：一般纤维 w
    def fiber_series_ok(wf, Nq=12):
        def mulw(a, b):
            return kmul(a, b, wf)
        def invw(a):
            cols = [mulw(a, e) for e in (ONE, X, [Fr(0), Fr(0), Fr(1)])]
            M = [[cols[j][r] for j in range(3)] + [ONE[r]] for r in range(3)]
            for c in range(3):
                pv_i = next(r for r in range(c, 3) if M[r][c] != 0)
                M[c], M[pv_i] = M[pv_i], M[c]
                pv = M[c][c]
                M[c] = [v / pv for v in M[c]]
                for r in range(3):
                    if r != c and M[r][c] != 0:
                        f = M[r][c]
                        M[r] = [M[r][t] - f * M[c][t] for t in range(4)]
            return [M[r][3] for r in range(3)]
        def xpw(n):
            e_, base = ONE, (X if n >= 0 else invw(X))
            for _ in range(abs(n)):
                e_ = mulw(e_, base)
            return e_
        eta3 = xpw(3)
        bvw = {v: sc(wf - v, eta3) for v in range(0, Nq + 3) if v != wf}           # b_v(η) = (w-v)η^3
        bwp = add(sc(-1, ONE), sc(-3 * wf, xpw(2)))                                 # b_w'(η) = -1 - 3w η^2
        upw = mulw(add(sc(3, ONE), sc(-2, X)), invw(sc(wf * wf, xpw(4))))           # u'(η) = (3-2η)/(w^2 η^4)
        def Pj(j):
            r = ONE
            for v in range(0, j + 1):
                if v == wf:
                    return ZERO
                r = mulw(r, bvw[v])
            return r
        def resP(M):
            if M < wf:
                return ZERO
            den = bwp
            for v in range(0, M + 1):
                if v != wf:
                    den = mulw(den, bvw[v])
            return mulw(upw, invw(den))
        def resE(M):
            if M < wf:
                return ZERO
            tot = ZERO
            for j in range(1, wf + 1):
                den = bwp
                for v in range(j, M + 1):
                    if v != wf:
                        den = mulw(den, bvw[v])
                tot = add(tot, sc(j, mulw(xpw(2), invw(den))))
            return mulw(upw, tot)
        def resG(M):
            if M < wf:
                return ZERO
            W = ONE
            for j in range(1, M + 1):
                W = add(W, sc(j, mulw(xpw(2), Pj(j - 1))))
            return mulw(W, resP(M))
        Wt = [Fr(0)] * (3 * wf + 3)
        Wt[0] = Fr(1)
        for j in range(1, wf + 1):
            fall = 1
            for t in range(j):
                fall *= (wf - t)
            Wt[3 * j + 2] += j * fall
        lam = {'E': red([0] + [c for c in Wt[1:]], wf), 'N': red(Wt, wf), 'c': ONE}
        def smul(A, B):
            C = [ZERO] * (Nq + 1)
            for i_, a in enumerate(A):
                if a != ZERO:
                    for j_ in range(Nq + 1 - i_):
                        if B[j_] != ZERO:
                            C[i_ + j_] = add(C[i_ + j_], mulw(a, B[j_]))
            return C
        wz = [ZERO] + [sc((-1) ** (n - 1), ONE) for n in range(1, Nq + 1)]
        inv1z = [sc((-1) ** n, ONE) for n in range(Nq + 1)]
        y_ = [mulw(xpw(-3), t) for t in wz]
        ex, term = [ONE] + [ZERO] * Nq, [ONE] + [ZERO] * Nq
        for n in range(1, Nq + 1):
            term = smul(term, y_)
            ex = [add(o, sc(Fr((-1) ** n, factorial(n)), t)) for o, t in zip(ex, term)]
        ypow = [ONE] + [ZERO] * Nq
        for _ in range(wf + 1):
            ypow = smul(ypow, y_)
        core = smul(smul(ypow, ex), inv1z)
        ok = True
        for kind, fn in (('E', resE), ('N', resG), ('c', resP)):
            pred = [mulw(sc(Fr(-1, factorial(wf) * wf * wf), lam[kind]), t) for t in core]
            act = []
            for q in range(Nq + 1):
                tot = ZERO
                for M in range(0, q):
                    tot = add(tot, sc((-1) ** (q - 1 - M) * comb(q, M + 1), fn(M)))
                act.append(tot)
            ok &= (act == pred)
        return ok
    okw = {wf: fiber_series_ok(wf) for wf in (1, 3)}
    report('b5s-resw', all(okw.values()), '引理 14.4 对纤维 w=1、3（E、N、N^c；q<=12，由闭式按留数定义在 K_w 中算）：%s' % okw)

    # ---- b5s-subst
    def lhs_series(kind, b, c, d, e, f):
        S = [row_res(q, kind) for q in range(NV + 1)]
        eb = kpow(X, b)
        # z(η,V) = V η^(b-1) (1-η)/(1+η^b V)
        zV = s_mul([ZERO, mul(kpow(X, b - 1), OME)] + [ZERO] * (NV - 1), s_binom(eb, -1))
        comp = s_compose(S, zV)
        a0 = mul(kpow(X, -(d - c) - b * (f - e)), kpow(OME, d + 1))
        return s_mul(s_scal(a0, comp), s_binom(eb, -(e + 1)))          # 乘 1/P，省去 V^(e-f)

    def rhs_series(kind, b, c, d, e, f, with_exp=True, lam=None):
        eb = kpow(X, b)
        a0 = mul(kpow(X, -(d - c) - b * (f - e)), kpow(OME, d + 1))
        alpha = mul(sc(-1, LAM[kind] if lam is None else lam), a0)
        tcoef = kpow(X, b - 1)
        tau = [ZERO, tcoef] + [ZERO] * (NV - 1)
        two_tau = s_mul(s_scal(sc(2, ONE), tau), s_binom(tcoef, -1))      # 2τ/(1+τ)
        ex = s_exp_neg(two_tau) if with_exp else s_const(ONE)
        tau3 = s_mul(s_mul(tau, tau), tau)
        core = s_mul(s_mul(tau3, ex), s_binom(tcoef, -4))
        return s_scal(alpha, s_mul(s_binom(eb, -e), core))                 # 省去 V^(e-f)

    cases = [('E', 1, 0, 0, 0, 0), ('E', 1, -1, -1, 0, 0), ('E', 1, 2, -1, 1, 3), ('N', 1, 0, 1, -2, 1),
             ('E', 0, 1, 0, 2, 0), ('N', 2, -1, 2, 0, 1), ('c', -1, 0, 0, 1, 1), ('E', 2, 3, -2, -1, 2)]
    oks, bad = True, []
    for cs in cases:
        L, R = lhs_series(*cs), rhs_series(*cs)
        if L != R:
            oks = False
            bad.append(cs)
    report('b5s-subst', oks, '引理 14.5（w=2）：代入并乘 1/P 后等于 α(1+η^b V)^(-e) V^(e-f) τ^3 e^(-2τ/(1+τ))(1+τ)^(-4)，%d 组 (类型,b,c,d,e,f)，'
           'b in {-1,0,1,2}，V^<=%d%s' % (len(cases), NV, '' if oks else '；不符：%s' % bad))

    # ---- b5s-norm
    nW1, nW, neta, nome = knorm(WT2M1, I), knorm(WT2, I), knorm(X, I), knorm(OME, I)
    def vq(r, p):
        r, v = Fr(r), 0
        n, dd = r.numerator, r.denominator
        while n % p == 0:
            n //= p
            v += 1
        while dd % p == 0:
            dd //= p
            v -= 1
        return v
    okn = (nW1 == Fr(17, 8) and nW == Fr(103, 16) and neta == Fr(1, 2) and nome == 1 and is_prime(17) and is_prime(103))
    # b=1：α = -Λ η^(-(d-c+f-e)) (1-η)^(d+1)，N(α) = -N(Λ) 2^(d-c+f-e)；17、103 的赋值都是 1
    okn &= all(vq(-nW1 * Fr(2) ** n, 17) == 1 and vq(-nW * Fr(2) ** n, 103) == 1 for n in range(-40, 41))
    report('b5s-norm', okn, 'N(W~_2-1)=%s、N(W~_2)=%s、N(η)=%s、N(1-η)=%s；17、103 为素数；b=1 时 N(α) 的 17-进（N^E）、103-进（N）赋值恒为 1'
           % (nW1, nW, neta, nome))

    # ---- b5s-Nc：R 式参数下每个 V 系数有理；违反 3(d+1)=d-c+f-e 时不然
    Lr = lhs_series('c', 1, -1, -1, 0, 0)
    ok_nc = all(is_rat(t) for t in Lr)
    viol = [(c, d, e, f) for c in (-1, 0, 1) for d in (-1, 0) for e in (0, 1) for f in (0, 1) if 3 * (d + 1) != d - c + f - e]
    ok_nc2 = all(not all(is_rat(t) for t in lhs_series('c', 1, *cs)) for cs in viol)
    # 满足 3(d+1)=d-c+f-e 但 e≠0：因子 (1+ηV)^(-e) 使系数不在 Q 中（定理 14.1(ii) 的 e=0）
    sat_e = [(c, d, e, 3 * (d + 1) - d + c + e) for c in (-2, -1, 0) for d in (-1, 0) for e in (-1, 1, 2)]
    ok_nc3 = all(3 * (d + 1) == d - c + f - e and e != 0 for c, d, e, f in sat_e)
    ok_nc3 &= all(not all(is_rat(t) for t in lhs_series('c', 1, *cs)) for cs in sat_e)
    okE = all(not all(is_rat(t) for t in lhs_series(k, 1, *cs)) for k in ('E', 'N') for cs in [(-1, -1, 0, 0), (0, 0, 0, 0), (1, 0, 0, 1)])
    report('b5s-Nc', ok_nc and ok_nc2 and ok_nc3 and okE,
           '对照：N^c 取 R 式参数 (c,d,e,f)=(-1,-1,0,0) 时每个 V 系数都在 Q 中：%s；违反 3(d+1)=d-c+f-e 的 %d 组参数都不是：%s；'
           '满足它但 e≠0 的 %d 组参数也不是：%s；N^E、N 在 3 组参数下都不是：%s' % (ok_nc, len(viol), ok_nc2, len(sat_e), ok_nc3, okE))

    # ---- b5s-Rform
    K, Q = 30, 10
    TU = U_fast_table(K, Q)
    TUc = Uc_table(K, Q)
    def ie(tab, k, q):
        if k == 0:
            return 1 if q == 0 else 0       # N(0,q) = [q=0]；T1.4 的 k>=1 形式在 k=0 时不成立
        if q == 0:
            return 0
        return sum((-1) ** (q - i) * comb(q, i) * tab[k][i - 1] for i in range(1, q + 1))
    Nc = [[ie(TUc, k, q) for q in range(Q + 1)] for k in range(K + 1)]
    NE = [[ie(TU, k, q) - Nc[k][q] for q in range(Q + 1)] for k in range(K + 1)]
    S2 = {}
    def stir(n, k):
        if (n, k) in S2:
            return S2[(n, k)]
        if n == k:
            v = 1
        elif k <= 0 or n < k:
            v = 0
        else:
            v = k * stir(n - 1, k) + stir(n - 1, k - 1)
        S2[(n, k)] = v
        return v
    def Rps(p, s):
        tot = (-1) ** p if s == 0 else 0        # i=0 项取 [s=0]
        for i in range(1, p + 1):
            tot += (-1) ** (p - i) * comb(p, i) * stir(i - 1 + s, i - 1)
        return tot
    def bn(n, r):
        return comb(n, r) if 0 <= r <= n else 0
    okR = True
    for q in range(1, Q + 1):
        for k in range(0, K + 1):
            val = sum(comb(q, p) * Rps(p, s) * bn(k - 2 * s + p - 1, s + q - 1)
                      for s in range(0, k + 1) for p in range(0, 2 * s + 1))
            okR &= (val == Nc[k][q])
    report('b5s-Rform', okR, 'R 式 N^c(k,q)=sum C(q,p)R(p,s)C(k-2s+p-1,s+q-1) 对 1<=q<=%d、0<=k<=%d 与按定义的 DP 一致' % (Q, K))

    # ---- b5s-bivar：用 N^c 的 R 式端到端核对 §2 的二元母函数恒等式（含低 p 的修正项，引理 14.2）
    #   R 式参数 (a,b,c,d,e,f) = (-2,1,-1,-1,0,0)，P = 1 + xV，z = V(1-x)/(1+xV)。
    #   若只用 q >= q0 的行：h_p := [V^p] sum_{q>=q0} F^c_q z^q / P = sum_{q=q0}^{p} F^c_q (1-x)^q (-1)^(p-q) C(p,q) x^(p-q)，
    #   预言 h_p = psi_p(u) - sum_{p'<q0} psi_{p'}(u) x^(p-p') sum_{q=p'}^{q0-1} C(q,p') (-1)^(p-q) C(p,q)，psi_p(u) = sum_s R(p,s) u^s。
    KX = 40
    TUc2 = Uc_table(KX, 10)
    def ser_mul(A, B):
        C = [Fr(0)] * (KX + 1)
        for i, a in enumerate(A):
            if a:
                for j in range(KX + 1 - i):
                    if B[j]:
                        C[i + j] += a * B[j]
        return C
    def one_minus_x_pow(n):
        out = [Fr(0)] * (KX + 1)
        for j in range(KX + 1):
            out[j] = Fr((-1) ** j * comb(n, j)) if n >= 0 else Fr(comb(-n + j - 1, j))
        return out
    def psi_series(p):
        out = [Fr(0)] * (KX + 1)
        for s_ in range(0, KX // 3 + 1):
            r = Rps(p, s_)
            if r:
                us = one_minus_x_pow(-s_)
                for kk in range(KX + 1 - 3 * s_):
                    out[kk + 3 * s_] += r * us[kk]
        return out
    Fc = {q: [Fr(ie(TUc2, k, q)) for k in range(KX + 1)] for q in range(1, 11)}
    def check_q0(q0, pmax):
        ok = True
        for p in range(0, pmax + 1):
            h = [Fr(0)] * (KX + 1)
            for q in range(q0, p + 1):
                t = ser_mul(Fc[q], one_minus_x_pow(q))
                cf = Fr((-1) ** (p - q) * comb(p, q))
                for kk in range(KX + 1 - (p - q)):
                    h[kk + p - q] += cf * t[kk]
            pred = psi_series(p)
            for pp in range(0, q0):
                coef = sum(comb(q, pp) * (-1) ** (p - q) * comb(p, q) for q in range(pp, q0))
                if coef:
                    ps = psi_series(pp)
                    for kk in range(KX + 1 - (p - pp)):
                        pred[kk + p - pp] -= coef * ps[kk]
            ok &= (h == pred)
        return ok
    okb1, okb3 = check_q0(1, 7), check_q0(3, 9)
    # 反向检查：去掉修正项（只用 psi_p）时 q0=3 不成立
    def check_q0_nocorr(q0, pmax):
        bad = False
        for p in range(0, pmax + 1):
            h = [Fr(0)] * (KX + 1)
            for q in range(q0, p + 1):
                t = ser_mul(Fc[q], one_minus_x_pow(q))
                cf = Fr((-1) ** (p - q) * comb(p, q))
                for kk in range(KX + 1 - (p - q)):
                    h[kk + p - q] += cf * t[kk]
            bad |= (h != psi_series(p))
        return bad
    okrev = check_q0_nocorr(3, 9)
    report('b5s-bivar', okb1 and okb3 and okrev,
           '§2 的二元母函数恒等式（含低 p 修正，引理 14.2）端到端核对：N^c 的 R 式，只用 q>=1 的行（p<=7）：%s；只用 q>=3 的行'
           '（低 p\'=0,1,2 有修正，p<=9）：%s；x 的阶 <=%d；去掉修正项时不成立：%s' % (okb1, okb3, KX, okrev))

    # ---- b5s-fiber1（数值佐证）
    def roots(coeffs):
        n = len(coeffs) - 1
        lead = coeffs[-1]
        a = [c / lead for c in coeffs]
        z = [complex(0.4, 0.9) ** k for k in range(n)]
        for _ in range(3000):
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
    xi = 0.6823278038280193
    okf, finfo = True, []
    for rr in (2, 4, 5, 6):
        U0 = xi ** rr / (1 - xi)
        co = [complex(-U0), complex(U0)] + [0j] * (rr - 2) + [1 + 0j]      # x^r + U0 x - U0
        rs = roots(co)
        nonroot = 0
        for r in rs:
            if abs(r - xi) < 1e-9:
                continue
            wv = (1 - r) / r ** 3
            if not (abs(wv.imag) < 1e-7 and abs(wv.real - round(wv.real)) < 1e-7 and round(wv.real) >= 1):
                nonroot += 1
        okf &= nonroot >= 1
        finfo.append('r=%d:%d' % (rr, nonroot))
    report('b5s-fiber1', okf, '数值佐证（证明见 A20）：U=x^r/(1-x) 过 ξ 的纤维中不是任何 b_w（w>=1）之根的点数：%s' % ', '.join(finfo))

    # ---- b5s-rev：扰动闭式里的留数元 W~_2（x^8 系数 4 -> 3），相关各条应当不再成立
    WT2_bad = red([1, 0, 0, 0, 0, 2, 0, 0, 3], I)
    n_bad = knorm(WT2_bad, I)
    act_N = [row_res(q, 'N') for q in range(N + 1)]                          # 左边按定义算，不用 WT2
    pred_bad = s_scal(sc(Fr(-1, 8), WT2_bad), s_mul(inv1z, y3e, N))
    sub_bad = lhs_series('N', 1, 0, 1, -2, 1) != rhs_series('N', 1, 0, 1, -2, 1, lam=WT2_bad)
    rv1 = (n_bad != Fr(103, 16)) and (act_N != pred_bad) and sub_bad
    L = lhs_series('E', 1, 0, 0, 0, 0)
    R0 = rhs_series('E', 1, 0, 0, 0, 0, with_exp=False)
    rv2 = (L != R0)
    report('b5s-rev', rv1 and rv2, '反向检查：W~_2 的 x^8 系数 4 改成 3 后范数为 %s（不再是 103/16），b5s-res 的 N 与 b5s-subst 的 N 参数组'
           '都不再成立：%s；去掉 e^(-2τ/(1+τ)) 后 b5s-subst 不成立：%s' % (n_bad, rv1, rv2))


if __name__ == '__main__':
    main()
    n_pass = sum(RESULTS)
    n_fail = len(RESULTS) - n_pass
    print('SUMMARY b5s pass=%d fail=%d' % (n_pass, n_fail))
    sys.exit(0 if n_fail == 0 else 1)
