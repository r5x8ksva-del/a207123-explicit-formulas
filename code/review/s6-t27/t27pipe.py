# -*- coding: utf-8 -*-
"""s6-t27：引理 A → F → (N2) → 引理 S → 拼接 的逐步核对流程（被 t27_good.py、t27_bad.py 调用）。"""
import sys
sys.dont_write_bytecode = True
import itertools
import time
from fractions import Fraction
from math import comb
import t27lib as L


def sub(p, w):
    return tuple(a - b for a, b in zip(p, w))


# ------------------------------------------------------------------ 引理 A：搜索最小规模并严格核对

def search_rec(T, search, maxDk, rep, label=''):
    t0 = time.time()
    tried = []
    for (J, I) in search:
        LA = L.LemmaA(T, I, J)
        for Dk in range(maxDk + 1):
            nul = LA.find(Dk)
            tried.append((J, I, Dk, nul))
            if nul == 0:
                continue
            cols, basis = LA.solve_exact(Dk)
            if not basis:
                continue
            good = []
            nfail = 0
            gridinfo = None
            for v in basis:
                a = LA.coeffs_from_vec(cols, v)
                ok, cnt, deg = LA.grid_verify(a)
                if ok:
                    good.append(a)
                    gridinfo = (cnt, deg)
                else:
                    nfail += 1
            if good:
                rep.info('%s引理 A 搜索：(J,I,deg_k) 依次试 %s' % (label, ' '.join('(%d,%d,%d):%s' % (j_, i_, d_, '有解' if n_ else '无')
                                                                     for j_, i_, d_, n_ in tried)))
                rep.info('%s首个非平凡解：J=%d, I=%d, a_ω 的 k-次数 ≤%d；取样方程组零空间维数 %d，其中 %d 个基向量通过严格网格核对'
                         '（网格 %s，%d 点）%s；用时 %.1f s'
                         % (label, J, I, Dk, len(basis), len(good), gridinfo[1], gridinfo[0],
                            ('，%d 个没通过（取样不足，舍弃）' % nfail) if nfail else '', time.time() - t0))
                return LA, Dk, good
    rep.info('%s引理 A 搜索失败：%s' % (label, tried))
    return None


def rec_str(a, maxterms=40):
    out = []
    for w in sorted(a):
        lst = a[w]
        poly = ' + '.join(('%s' % c) + ('' if e == 0 else ('k' if e == 1 else 'k^%d' % e)) for e, c in enumerate(lst) if c)
        out.append('[%s]·T(p−%s)' % (poly, w))
    s = ' + '.join(out[:maxterms])
    if len(out) > maxterms:
        s += ' + …（共 %d 项）' % len(out)
    return s


def check_degree_bound(T, LA, rep, label=''):
    beta, gamma = T.beta_gamma()
    degP = L.p_totdeg(T.P, range(T.n))
    D = degP + beta * LA.I + gamma * LA.J
    actual = max(LA.totdegQ_mj.values())
    rep.check('%s引理 A 次数界：max_ω deg_{(m,j⃗)} Q_ω = %d ≤ D = deg P + βI + γJ = %d + %d·%d + %d·%d = %d'
              % (label, actual, degP, beta, LA.I, gamma, LA.J, D), actual <= D)
    # 计数：取 J+1 > β^{r+1}/(r+1)!，求使 未知数 > 方程数 的最小 I（只是算术，说明「令 I→∞」可行）
    r1 = T.r + 1
    from math import factorial
    Jc = 0
    while not (Jc + 1) * factorial(r1) > beta ** r1:
        Jc += 1
    Ic = 0
    while True:
        Dd = degP + beta * Ic + gamma * Jc
        if (Jc + 1) * (Ic + 1) ** r1 > comb(Dd + r1, r1):
            break
        Ic += 1
        if Ic > 10 ** 6:
            break
    rep.info('%s引理 A 计数（纯算术）：β=%d、γ=%d、r+1=%d；取 J=%d（最小的 J 使 J+1>β^{r+1}/(r+1)!），'
             '则 I≥%d 时 (J+1)(I+1)^{r+1} > C(D+r+1,r+1)。实际只需 (J,I)=(%d,%d)。'
             % (label, beta, gamma, r1, Jc, Ic, LA.J, LA.I))
    return Jc, Ic


# ------------------------------------------------------------------ 引理 F

def check_lemmaF(T, LA, a, box, rep, label=''):
    cnt = dict(appl=0, skip=0, nonzeroT=0, boundary=0, allzero=0, tstar0=0)
    cases = {1: 0, 2: 0, 3: 0}
    case2_tstar_nonzero = 0
    ok_tstar = ok_fact = ok_rec = True
    first_bad = None
    zero = (0,) * T.n
    for p in itertools.product(*box):
        vals = {}
        bad = False
        for w in LA.Omega:
            v = T.val(sub(p, w))
            if v is None:
                bad = True
                break
            vals[w] = v
        if bad:
            cnt['skip'] += 1
            continue
        cnt['appl'] += 1
        Ts = LA.Tstar(p)
        if Ts is None:
            ok_tstar = False
            first_bad = first_bad or ('T* 不良定义', p)
            continue
        if Ts == 0:
            cnt['tstar0'] += 1
        for w in LA.Omega:
            if vals[w] != Ts * LA.Q(w, p):
                ok_fact = False
                first_bad = first_bad or ('T(p−ω)≠T*Q', p, w)
            for s in range(len(T.den)):
                c = LA.den_case(s, w, p)
                cases[c] += 1
                if c == 2 and Ts != 0:
                    case2_tstar_nonzero += 1
        rec = sum(L.poly_k_eval(a[w], p[0]) * vals[w] for w in a)
        if rec != 0:
            ok_rec = False
            first_bad = first_bad or ('递推不成立', p)
        if vals[zero] != 0:
            cnt['nonzeroT'] += 1
        elif any(vals[w] != 0 for w in LA.Omega):
            cnt['boundary'] += 1
        else:
            cnt['allzero'] += 1
    rep.check('%s引理 F：前提成立的 %d 个格点上 T*(p) 都有限' % (label, cnt['appl']), ok_tstar)
    rep.check('%s引理 F：这些点上对每个 ω 都有 T(p−ω)=T*(p)·Q_ω(p)' % label, ok_fact,
              '（分母三种情形出现次数：普通 %d、「B−e(ω)<0≤B−e^min」%d（其中 T*≠0 的 %d 次靠 Q_ω 含 t=0 给出 0）、'
              '「B−e^min<0」%d；T*(p)=0 的点 %d 个）'
              % (cases[1], cases[2], case2_tstar_nonzero, cases[3], cnt['tstar0']))
    rep.check('%s引理 F：这些点上 Σ a_ω(k)T(p−ω)=0' % label, ok_rec,
              '（T(p)≠0 的点 %d；T(p)=0 但某个 T(p−ω)≠0 的「边界」点 %d；全为 0 的点 %d；前提不成立而跳过 %d）'
              % (cnt['nonzeroT'], cnt['boundary'], cnt['allzero'], cnt['skip']))
    if first_bad:
        rep.info('%s第一个反例：%s' % (label, first_bad))
    return ok_tstar and ok_fact and ok_rec, cnt


# ------------------------------------------------------------------ (N2)

def check_N2(T, R, krange, mrange, win):
    """在 (k,m)∈krange×mrange、j⃗∈win(k,m) 上检查：T 良定义且非零 ⇒ sup 距离 R 内都良定义。"""
    npts = 0
    for k in krange:
        for m in mrange:
            for jv in itertools.product(*[range(lo, hi + 1) for lo, hi in win(k, m)]):
                p = (k, m) + jv
                v = T.val(p)
                if v is None or v == 0:
                    continue
                npts += 1
                for d in itertools.product(range(-R, R + 1), repeat=T.n):
                    q = tuple(x + y for x, y in zip(p, d))
                    if not T.wd(q):
                        return False, npts, (p, q)
    return True, npts, None


# ------------------------------------------------------------------ 和 S(k,m)=Σ_j⃗ T̃

def make_S(T, win, shell=2):
    cache = {}
    shell_bad = []

    def S(k, m):
        key = (k, m)
        if key in cache:
            return cache[key]
        rg = win(k, m)
        tot = Fraction(0)
        for jv in itertools.product(*[range(lo, hi + 1) for lo, hi in rg]):
            tot += T.tt((k, m) + jv)
        for jv in itertools.product(*[range(lo - shell, hi + shell + 1) for lo, hi in rg]):
            if all(lo <= x <= hi for x, (lo, hi) in zip(jv, rg)):
                continue
            if T.tt((k, m) + jv) != 0:
                shell_bad.append((k, m) + jv)
                break
        cache[key] = tot
        return tot
    S.shell_bad = shell_bad
    return S


def jbox(win, k, m, extra_lo, extra_hi):
    return itertools.product(*[range(lo - extra_lo, hi + extra_hi + 1) for lo, hi in win(k, m)])


def rec_failures(T, a, krange, mrange, win, I):
    """(k,m) 取遍给定范围、j⃗ 取遍窗口（向两侧各放宽 I+2）时，(A T̃)(k,m,j⃗)≠0 的点。"""
    fails = []
    npts = 0
    for k in krange:
        for m in mrange:
            for jv in jbox(win, k, m, I + 2, I + 2):
                p = (k, m) + tuple(jv)
                npts += 1
                v = L.apply_rec(T, a, p)
                if v != 0:
                    fails.append((p, v))
    return fails, npts


# ------------------------------------------------------------------ 引理 S

def sigma_minus_one_pow(h, jv, al):
    """[(σ−1)^α h](j⃗)，σ_l: j_l ↦ j_l − 1。"""
    s = Fraction(0)
    for be in itertools.product(*[range(x + 1) for x in al]):
        c = 1
        for x, y in zip(al, be):
            c *= comb(x, y) * (-1) ** (x - y)
        s += c * h(tuple(a - b for a, b in zip(jv, be)))
    return s


def check_lemmaS(T, a, rep, I, S, win, kpts, Qprime_pts, label=''):
    r = T.r
    A, C, minimal = L.lemmaS_ops(a, r, I)
    rep.check('%s引理 S：C_α 不全为 0（{α:C_α≠0} 非空）' % label, len(minimal) > 0)
    if not minimal:
        return None
    alstar = min(minimal)
    lower = [al for al in C if al != alstar and all(x <= y for x, y in zip(al, alstar))]
    rep.check('%s引理 S：取极小元 α*=%s；α<α* 的 C_α 都为 0（共 %d 个）' % (label, alstar, len(lower)),
              all(not C[al] for al in lower))
    # 上三角可逆：由 C 反解 A
    ok_tri = True
    for nu in itertools.product(range(I + 1), repeat=r):
        # A_ν = Σ_{α≥ν} (−1)^{|α−ν|} C(α,ν) C_α
        rec = {}
        for al in C:
            if all(x >= y for x, y in zip(al, nu)):
                c = 1
                for x, y in zip(al, nu):
                    c *= comb(x, y) * (-1) ** (x - y)
                for key, lst in C[al].items():
                    cur = rec.get(key, [])
                    n_ = max(len(cur), len(lst))
                    new = [Fraction(0)] * n_
                    for i_, v_ in enumerate(cur):
                        new[i_] += v_
                    for i_, v_ in enumerate(lst):
                        new[i_] += c * v_
                    while new and new[-1] == 0:
                        new.pop()
                    rec[key] = new
        rec = {k_: v_ for k_, v_ in rec.items() if v_}
        if rec != A.get(nu, {}):
            ok_tri = False
    rep.check('%s引理 S：C_α=Σ_{ν⃗≥α}C(ν⃗,α)A_ν⃗ 可由二项式反演还原 A_ν⃗（上三角、对角为 1）' % label, ok_tri)
    Cst = C[alstar]
    rep.info('%sC_{α*} = %s' % (label, L.op_str(Cst)))
    # 分部求和恒等式（每个 α 单独）：Σ_j⃗ C(j⃗,α*)[(σ−1)^α T̃](k′,m′,j⃗) = Σ_j⃗ C(j⃗,α*−α) T̃(k′,m′,j⃗)
    ok_sbp = True
    nchk = 0
    for (k1, m1) in kpts[:12]:
        for al in C:
            def h(jv, k1=k1, m1=m1):
                return T.tt((k1, m1) + jv)
            lhs = Fraction(0)
            for jv in jbox(win, k1, m1, I + 2, I + 2):
                jv = tuple(jv)
                lhs += L.binom_vec(jv, alstar) * sigma_minus_one_pow(h, jv, al)
            rhs = Fraction(0)
            diff = tuple(x - y for x, y in zip(alstar, al))
            for jv in jbox(win, k1, m1, 2, 2):
                jv = tuple(jv)
                rhs += L.binom_vec(jv, diff) * T.tt((k1, m1) + jv)
            nchk += 1
            if lhs != rhs:
                ok_sbp = False
    rep.check('%s引理 S：分部求和 Σ C(j⃗,α*)·(σ−1)^α T̃ = Σ C(j⃗,α*−α)·T̃（逐个 α，%d 组）' % (label, nchk), ok_sbp)
    # 整体恒等式：Σ_j⃗ C(j⃗,α*)(A T̃)(k,m,j⃗) = (C_{α*} S)(k,m)，对窗口内一切 (k,m) 都应成立（不管递推是否成立）
    ok_whole = True
    resid = {}
    for (k, m) in kpts:
        lhs = Fraction(0)
        for jv in jbox(win, k, m, I + 2, I + 2):
            jv = tuple(jv)
            c = L.binom_vec(jv, alstar)
            if c != 0:
                lhs += c * L.apply_rec(T, a, (k, m) + jv)
        rhs = L.apply_op(Cst, S, k, m)
        resid[(k, m)] = rhs
        if lhs != rhs:
            ok_whole = False
    rep.check('%s引理 S：Σ_j⃗ C(j⃗,α*)(A T̃)(k,m,j⃗) = (C_{α*}S)(k,m) 在 %d 个 (k,m) 上成立（含 Q′ 之外）'
              % (label, len(kpts)), ok_whole)
    zero_on_Qp = all(resid.get(q, L.apply_op(Cst, S, *q)) == 0 for q in Qprime_pts)
    return dict(A=A, C=C, alstar=alstar, Cst=Cst, resid=resid, zero_on_Qp=zero_on_Qp)
