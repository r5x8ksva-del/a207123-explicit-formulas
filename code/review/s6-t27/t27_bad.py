# -*- coding: utf-8 -*-
"""t27_bad：不满足 (N2) 的 proper 项——引理 F/S 在哪里失效，(N2) 对结论是否必要。

例子（p=(k,m,j)）：
  V1  C(m,j)C(k,j)·j!/(j+1)!        （分子 j! 在 j=−1 不良定义，紧挨支撑下端 j=0）
  V1′ 同一函数约去 j! 后的写法 m!k!/((m−j)!j!(k−j)!(j+1)!)（满足 (N2)）
  V3  C(m,j)C(k,j)·C(2j,j)          （中心二项式；分子 (2j)! 在 j=−1 不良定义）
  V2  C(k,j)·(m−j)!/m!              （k>m 时支撑上端 j=m 紧挨 j=m+1；那里 Γ 延拓有真极点）
  V5  C(k,j)·(2m−2j)!/((m−j)!m!)    （WZ 例 B 的机制：j=m+1 处 Γ(2m−2j+1)/Γ(m−j+1) 是可去奇点，极限 −1/2≠0）
每个例子：
  1 引理 A 的递推（网格严格核对）；引理 F 在其前提成立处仍成立（引理 F 不需要 (N2)）；
  2 (N2) 的反例（R=1）；
  3 远离原点处，与非零项同处一个递推的「不良定义点」q，按 Γ 延拓沿一般方向 p+εv 的展开 T≈c·ε^ord 分类：
      ord>0（延拓值为 0）、ord=0（有限非零值，检查与方向无关）、ord<0（极点）；
  4 Σa_ω T̃(p−ω)≠0 的失效点：核对它们恰好是用到了「延拓值非 0」的不良定义点的那些点；
  5 残差 C_{α*}(Σ_jT̃) 在若干个越来越靠里的象限中的情况；残差恰为 Σ_j C(j,α*)(A T̃)(k,m,j)；
  6 结论（和满足系数只依赖 k 的递推）是否仍成立：残差为 0 时直接成立；残差非 0 时搜索零化残差的 k-only 算子 D，
    在拟合盒子之外核对 D 与 D·C_{α*}（数值证据，不是证明）。
"""
import sys
sys.dont_write_bytecode = True
import itertools
import random
import time
from fractions import Fraction
from math import comb, factorial
import t27lib as L
import t27pipe as PP

rep = L.Reporter()
SEARCH = [(1, 1), (2, 1), (1, 2), (2, 2), (3, 1), (3, 2), (2, 3), (4, 1), (3, 3), (4, 2), (2, 4)]


def win1(k, m):
    return [(-2, max(k, m, 0) + 2)]


# ------------------------------------------------------------------ Γ 延拓的方向展开

def eps_poly_P(P, p, v):
    """P(p+εv) 关于 ε 的多项式系数列表。"""
    out = {}
    for e, c in P.items():
        poly = {0: Fraction(c)}
        for i, ei in enumerate(e):
            for _ in range(ei):
                new = {}
                for d, cc in poly.items():
                    new[d] = new.get(d, 0) + cc * p[i]
                    new[d + 1] = new.get(d + 1, 0) + cc * v[i]
                poly = new
        for d, cc in poly.items():
            out[d] = out.get(d, 0) + cc
    n = max(out) + 1 if out else 0
    return [out.get(d, Fraction(0)) for d in range(n)]


def continuation(T, p, v):
    """T(p+εv) = c·ε^ord + …（Γ(x+1+δ) 在 x+1=−n 处 ≈ (−1)^n/(n!·δ)；1/Γ 同理）。返回 (ord, c)。
    方向 v 使某个在极点上的因子沿该方向不变时返回 None（换一个方向）。"""
    order = 0
    coef = Fraction(1)
    for c, d in T.num:
        x = L.dot(c, p) + d
        s = L.dot(c, v)
        if x >= 0:
            coef *= factorial(x)
        else:
            if s == 0:
                return None
            n = -(x + 1)
            order -= 1
            coef *= Fraction((-1) ** n, factorial(n)) / s
    for c, d in T.den:
        x = L.dot(c, p) + d
        s = L.dot(c, v)
        if x >= 0:
            coef /= factorial(x)
        else:
            if s == 0:
                return None
            n = -(x + 1)
            order += 1
            coef *= (-1) ** n * factorial(n) * s
    pe = eps_poly_P(T.P, p, v)
    i0 = next((i for i, c in enumerate(pe) if c != 0), None)
    if i0 is None:
        return (10 ** 6, Fraction(0))
    order += i0
    coef *= pe[i0]
    for zi, pi in zip(T.z, p):
        if zi != 1 and pi != 0:
            coef *= zi ** pi
    return (order, coef)


def classify(T, q, rnd):
    """不良定义点 q 上 Γ 延拓的类型：'zero'、'finite:值'、'pole'；沿两个随机方向核对一致。"""
    res = []
    while len(res) < 2:
        v = tuple(rnd.randint(1, 9) * rnd.choice((1, -1)) for _ in range(T.n))
        r = continuation(T, q, v)
        if r is not None:
            res.append(r)
    (o1, c1), (o2, c2) = res
    if o1 > 0 and o2 > 0:
        return 'zero'
    if o1 < 0 and o2 < 0:
        return 'pole'
    if o1 == 0 and o2 == 0 and c1 == c2:
        return 'finite:%s' % c1
    return 'direction-dependent'


def gamma_order(T, q, rnd):
    """沿一般方向的阶 ord = #{分母参数<0} − #{分子参数<0} + ord_q P（与方向无关，只要各 c·v≠0）。"""
    Z = sum(1 for c, d in T.den if L.dot(c, q) + d < 0)
    N = sum(1 for c, d in T.num if L.dot(c, q) + d < 0)
    v = tuple(rnd.randint(1, 9) * rnd.choice((1, -1)) for _ in range(T.n))
    pe = eps_poly_P(T.P, q, v)
    i0 = next((i for i, c in enumerate(pe) if c != 0), 10 ** 6)
    return Z - N + i0


def check_N2prime(T, R, krange, mrange, win, rnd):
    """(N2′)：Q_R 中非零点的 sup 距离 R 邻域里，每个不良定义点 q 的 Γ 阶 ≥1（Γ 延拓在 q 处为 0）。"""
    npts = nill = 0
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
                        nill += 1
                        if gamma_order(T, q, rnd) < 1:
                            return False, npts, nill, q
    return True, npts, nill, None


# ------------------------------------------------------------------ 算子工具

def shift_poly(lst, a):
    out = [Fraction(0)] * len(lst)
    for e, c in enumerate(lst):
        for t in range(e + 1):
            out[t] += c * comb(e, t) * (-a) ** (e - t)
    while out and out[-1] == 0:
        out.pop()
    return out


def mul_poly(x, y):
    if not x or not y:
        return []
    out = [Fraction(0)] * (len(x) + len(y) - 1)
    for i, a in enumerate(x):
        for j, b in enumerate(y):
            out[i + j] += a * b
    while out and out[-1] == 0:
        out.pop()
    return out


def compose(D, C):
    """(D∘C)：先作用 C 再作用 D；系数都在左边。"""
    out = {}
    for (a, b), d in D.items():
        for (j, mu), c in C.items():
            prod = mul_poly(d, shift_poly(c, a))
            key = (a + j, b + mu)
            cur = out.get(key, [])
            n_ = max(len(cur), len(prod))
            new = [Fraction(0)] * n_
            for i_, v_ in enumerate(cur):
                new[i_] += v_
            for i_, v_ in enumerate(prod):
                new[i_] += v_
            while new and new[-1] == 0:
                new.pop()
            out[key] = new
    return {k_: v_ for k_, v_ in out.items() if v_}


def find_konly(f, kbox, mbox, label, maxA=3, maxB=3, maxD=3, budget=240.0):
    """在 kbox×mbox 上找 Σ_{a≤A,b≤B} p_ab(k) f(k−a,m−b)=0 的非零解（p_ab 次数 ≤D），按未知数个数递增搜索。"""
    t0 = time.time()
    shapes = sorted([(A, B, D) for A in range(maxA + 1) for B in range(maxB + 1) for D in range(maxD + 1)
                     if (A, B) != (0, 0)], key=lambda s: ((s[0] + 1) * (s[1] + 1) * (s[2] + 1), s))
    pts = [(k, m) for k in kbox for m in mbox]
    vals = {}

    def fv(k, m):
        if (k, m) not in vals:
            vals[(k, m)] = f(k, m)
        return vals[(k, m)]
    for (A, B, D) in shapes:
        if time.time() - t0 > budget:
            rep.info('%s搜索超出时间预算（%.0f s），停在形状 (A,B,D)=(%d,%d,%d)' % (label, budget, A, B, D))
            return None
        cols = [(a, b, d) for a in range(A + 1) for b in range(B + 1) for d in range(D + 1)]
        if len(pts) < len(cols) + 10:
            continue
        rows = [[(k ** d) * fv(k - a, m - b) for (a, b, d) in cols] for (k, m) in pts]
        if L.nullity_modp(rows, len(cols)) == 0:
            continue
        basis = L.nullspace_exact(rows, len(cols))
        if not basis:
            continue
        op = {}
        for (a, b, d), x in zip(cols, basis[0]):
            if x != 0:
                lst = op.setdefault((a, b), [])
                while len(lst) <= d:
                    lst.append(Fraction(0))
                lst[d] += x
        op = {k_: v_ for k_, v_ in op.items() if any(v_)}
        rep.info('%s找到零化残差的 k-only 算子：形状 (A,B,deg)=(%d,%d,%d)，拟合盒子 k∈[%d,%d]、m∈[%d,%d]，用时 %.1f s'
                 % (label, A, B, D, kbox[0], kbox[-1], mbox[0], mbox[-1], time.time() - t0))
        return op
    rep.info('%s在 A,B≤%d、deg≤%d 内没有找到' % (label, maxA, maxD))
    return None


# ------------------------------------------------------------------ 主流程

def run_bad(T, note_where, expect_fail, deep=(12, 12), quads=((12, 12), (20, 14), (14, 22), (26, 26)),
            win=win1, maxDk=3, Fbox=None, search=SEARCH, seed=7, required=True):
    print('\n' + '=' * 100)
    print('例子 %s：%s' % (T.name, T.note))
    beta, gamma = T.beta_gamma()
    print('    分子参数 %s；分母参数 %s；β=%d，γ=%d' % (T.num, T.den, beta, gamma))
    t0 = time.time()
    rnd = random.Random(seed)
    res = PP.search_rec(T, search, maxDk, rep, label='[%s] ' % T.name)
    if required or res is not None:
        rep.check('[%s] 引理 A：找到非平凡 k-only 递推（网格严格核对）' % T.name, res is not None)
    if res is None:
        rep.info('[%s] 在给定的小搜索范围内没有找到递推（引理 A 只保证 J、I 足够大时存在）；本例只作记录，到此为止' % T.name)
        return None
    LA, Dk, good = res
    a = good[0]
    I, J = LA.I, LA.J
    rep.info('[%s] 递推：%s = 0' % (T.name, PP.rec_str(a)))
    if Fbox is None:
        Fbox = [range(-2, 12), range(-2, 12), range(-4, 15)]
    PP.check_lemmaF(T, LA, a, Fbox, rep, label='[%s] ' % T.name)
    k0, m0 = deep
    ok, npts, viol = PP.check_N2(T, 1, range(k0, k0 + 7), range(m0, m0 + 7), win)
    rep.check('[%s] (N2) 不成立：R=1 时在 {k≥%d,m≥%d} 中就有反例' % (T.name, k0, m0), not ok,
              ('（T 在 %s 良定义且非零，距离 1 的 %s 不良定义；%s）' % (viol[0], viol[1], note_where)) if viol else '')
    Rw = max(I, J)
    okp, nptp, nill, qbad = check_N2prime(T, Rw, range(k0, k0 + 6), range(m0, m0 + 6), win, rnd)
    rep.check('[%s] 弱化条件 (N2′)（R=%d：邻域里的不良定义点 Γ 阶都 ≥1）%s——预期%s'
              % (T.name, Rw, '成立' if okp else '不成立', '不成立' if expect_fail else '成立'), okp != expect_fail,
              '（%d 个支撑点、%d 个邻域内不良定义点%s）' % (nptp, nill, '' if okp else '；反例 q=%s，阶 %d'
                                                       % (qbad, gamma_order(T, qbad, rnd))))
    # 与非零项同处一个递推的不良定义点，按 Γ 延拓分类；并用「沿同一方向 v 的 Γ 延拓满足同一递推」精确解释失效量
    kr, mr = range(k0, k0 + 5), range(m0, m0 + 5)
    cls_count = {}
    n_mixed = n_pole = n_expl = 0
    ok_expl = True
    pole_pts = set()
    for k in kr:
        for m in mr:
            for jv in PP.jbox(win, k, m, I + 2, I + 2):
                p = (k, m) + tuple(jv)
                vs = {w: T.val(PP.sub(p, w)) for w in a}
                ill = [w for w, v in vs.items() if v is None]
                if not ill or all(v in (None, 0) for v in vs.values()):
                    continue
                n_mixed += 1
                for w in ill:
                    c = classify(T, PP.sub(p, w), rnd)
                    cls_count[c] = cls_count.get(c, 0) + 1
                # 同一方向 v 上的延拓值
                while True:
                    v = tuple(rnd.randint(1, 9) * rnd.choice((1, -1)) for _ in range(T.n))
                    conts = {w: continuation(T, PP.sub(p, w), v) for w in a}
                    if all(c is not None for c in conts.values()):
                        break
                if any(o < 0 for o, _ in conts.values()):
                    n_pole += 1
                    pole_pts.add(p)
                    continue
                cv = {w: (c if o == 0 else Fraction(0)) for w, (o, c) in conts.items()}
                kk = p[0]
                total = sum(L.poly_k_eval(a[w], kk) * cv[w] for w in a)
                defect = L.apply_rec(T, a, p)
                pred = -sum(L.poly_k_eval(a[w], kk) * cv[w] for w in ill)
                n_expl += 1
                if total != 0 or defect != pred:
                    ok_expl = False
    rep.info('[%s] 递推里同时出现「不良定义项」与「非零项」的点 %d 个；其中不良定义点按 Γ 延拓分类（计重数）：%s'
             % (T.name, n_mixed, cls_count))
    rep.check('[%s] 这些点上（无极点的 %d 个）：Γ 延拓值满足同一递推 Σa_ω(k)·T^cont(p−ω)=0，'
              '且 Σa_ω T̃(p−ω) 恰等于 −Σ_{不良定义 ω} a_ω(k)·T^cont(p−ω)' % (T.name, n_expl), ok_expl,
              '（有极点的点 %d 个，单列）' % n_pole)
    fails, nf = PP.rec_failures(T, a, kr, mr, win, I)
    fail_set = set(p for p, _ in fails)
    rep.info('[%s] Σa_ω T̃(p−ω)≠0 的失效点：%d/%d；其中用到极点的 %d 个' % (T.name, len(fails), nf, len(fail_set & pole_pts)))
    if pole_pts:
        rep.info('[%s] 用到极点的点 %d 个，其中失效 %d 个（极点项的留数在递推里互相抵消，ε^0 项要看次一阶，这里不预测）'
                 % (T.name, len(pole_pts), len(pole_pts & fail_set)))
    rep.info('[%s] 不用极点的失效点 %d 个（都由上面的「−Σ_{不良定义} a·T^cont」精确给出）'
             % (T.name, len(fail_set - pole_pts)))
    rep.check('[%s] 失效与否与预期一致（预期：%s）' % (T.name, '有失效点' if expect_fail else '没有失效点'),
              (len(fails) > 0) == expect_fail)
    if fails:
        offs_low = sorted(set(p[2] for p in fail_set))
        offs_m = sorted(set(p[2] - p[1] for p in fail_set))
        offs_km = sorted(set(p[0] - p[1] for p in fail_set))
        rep.info('[%s] 失效点的 j = %s；j−m = %s；k−m = %s' % (T.name, offs_low[:12], offs_m[:12], offs_km[:12]))
    # 残差
    S = PP.make_S(T, win)
    kpts = [(k, m) for k in range(k0, k0 + 5) for m in range(m0, m0 + 5)]
    out = PP.check_lemmaS(T, a, rep, I, S, win, kpts, kpts, label='[%s] ' % T.name)
    Cst = out['Cst']
    nzq = []
    for (kq, mq) in quads:
        nz = sum(1 for k in range(kq, kq + 4) for m in range(mq, mq + 4) if L.apply_op(Cst, S, k, m) != 0)
        nzq.append(nz)
        rep.info('[%s] 象限 {k≥%d,m≥%d} 的 4×4 角上残差 C_{α*}S≠0 的点：%d/16' % (T.name, kq, mq, nz))
    if expect_fail:
        rep.check('[%s] 残差在所查的每个象限里都不全为 0（引理 S 的结论在这些象限都失效）' % T.name, all(n > 0 for n in nzq))
    else:
        rep.check('[%s] 残差在所查的象限里都为 0：虽然 (N2) 不成立，C_{α*}(Σ_jT̃)=0 仍成立' % T.name, all(n == 0 for n in nzq))
    rep.check('[%s] 窗口外的 T̃ 都为 0' % T.name, not S.shell_bad, str(S.shell_bad[:3]))
    rep.info('[%s] 用时 %.1f s' % (T.name, time.time() - t0))
    return dict(T=T, LA=LA, a=a, S=S, Cst=Cst, I=I, J=J)


def necessity_search(ctx, k0, m0, fit=13, check=(10, 40), budget=300.0):
    T, S, Cst = ctx['T'], ctx['S'], ctx['Cst']

    def Rf(k, m):
        return L.apply_op(Cst, S, k, m)
    D = find_konly(Rf, list(range(k0, k0 + fit)), list(range(m0, m0 + fit)), '[%s] ' % T.name, budget=budget)
    if D is None:
        rep.info('[%s] 没有找到零化残差的 k-only 算子（在搜索范围内）；这只说明范围不够，不说明不存在' % T.name)
        return
    rep.info('[%s] D = %s' % (T.name, L.op_str(D)))
    comp = compose(D, Cst)
    rep.info('[%s] D·C_{α*} = %s' % (T.name, L.op_str(comp)))
    lo, hi = check
    Amax = max(a for a, b in comp)
    Bmax = max(b for a, b in comp)
    pts = [(k, m) for k in range(max(lo, Amax), hi) for m in range(max(lo, Bmax), hi)][::3]
    regions = (sum(1 for k, m in pts if k < m), sum(1 for k, m in pts if k == m), sum(1 for k, m in pts if k > m))
    okR = all(L.apply_op(D, Rf, k, m) == 0 for (k, m) in pts)
    rep.check('[%s] D 在拟合盒子之外也零化残差（%d 个点：k<m %d、k=m %d、k>m %d）' % ((T.name, len(pts)) + regions), okR)
    okS = all(L.apply_op(comp, S, k, m) == 0 for (k, m) in pts)
    rep.check('[%s] 系数只依赖 k 的非零算子 D·C_{α*} 零化 Σ_jT̃（同一批点；数值证据）' % T.name, okS and bool(comp))


# ---------------------------------------------------------------- 例子
V1 = L.Term('V1', 1, num=[((1, 0, 0), 0), ((0, 1, 0), 0), ((0, 0, 1), 0)],
            den=[((0, 0, 1), 0), ((0, 1, -1), 0), ((0, 0, 1), 0), ((1, 0, -1), 0), ((0, 0, 1), 1)],
            note='C(m,j)C(k,j)·j!/(j+1)!')
run_bad(V1, '支撑下端 j=0 紧挨 j=−1', expect_fail=False)

V1c = L.Term('V1′', 1, num=[((1, 0, 0), 0), ((0, 1, 0), 0)],
             den=[((0, 1, -1), 0), ((0, 0, 1), 0), ((1, 0, -1), 0), ((0, 0, 1), 1)],
             note='m!k!/((m−j)! j! (k−j)! (j+1)!)：V1 约去一个 j! 后的写法')
okeq = all(V1.tt((k, m, j)) == V1c.tt((k, m, j)) for k in range(-2, 12) for m in range(-2, 12) for j in range(-5, 15))
rep.check('[V1′] 与 V1 的 T̃ 处处相等（k,m∈[−2,11]、j∈[−5,14]）', okeq)
ok, npts, viol = PP.check_N2(V1c, 3, range(3, 12), range(3, 12), win1)
rep.check('[V1′] 换一种写法后 (N2) 成立：R=3、Q_R={k≥3,m≥3}，%d 个支撑点' % npts, ok, str(viol or ''))

V3 = L.Term('V3', 1, num=[((1, 0, 0), 0), ((0, 1, 0), 0), ((0, 0, 2), 0)],
            den=[((0, 0, 1), 0), ((0, 1, -1), 0), ((0, 0, 1), 0), ((1, 0, -1), 0), ((0, 0, 1), 0), ((0, 0, 1), 0)],
            note='C(m,j)C(k,j)·C(2j,j)')
run_bad(V3, '支撑下端 j=0 紧挨 j=−1', expect_fail=False)

V2 = L.Term('V2', 1, num=[((1, 0, 0), 0), ((0, 1, -1), 0)],
            den=[((0, 0, 1), 0), ((1, 0, -1), 0), ((0, 1, 0), 0)],
            note='C(k,j)·(m−j)!/m!（k>m 时支撑上端 j=m 紧挨 j=m+1）')
c2 = run_bad(V2, 'k>m 时支撑上端 j=m 紧挨 j=m+1', expect_fail=True, deep=(14, 10),
             quads=((14, 10), (24, 12), (30, 26), (40, 30)))
if c2:
    necessity_search(c2, 12, 12)

V5 = L.Term('V5', 1, num=[((1, 0, 0), 0), ((0, 2, -2), 0)],
            den=[((0, 0, 1), 0), ((1, 0, -1), 0), ((0, 1, -1), 0), ((0, 1, 0), 0)],
            note='C(k,j)·(2m−2j)!/((m−j)! m!)（WZ 例 B 的机制）')
c5 = run_bad(V5, 'k>m 时支撑上端 j=m 紧挨 j=m+1', expect_fail=True, deep=(14, 10),
             quads=((14, 10), (24, 12), (30, 26), (40, 30)))
if c5:
    necessity_search(c5, 12, 12)


def win2b(k, m):
    return [(-2, max(m, 0) + 2)]


V2b = L.Term('V2b', 1, num=[((1, 0, 1), 0), ((0, 1, 0), 0), ((0, 2, -2), 0)],
             den=[((1, 0, 0), 0), ((0, 0, 1), 0), ((0, 0, 1), 0), ((0, 1, -1), 0), ((0, 2, 2), 0)],
             note='C(k+j,j)C(m,j)·(2m−2j)!/(2m+2j)!（照搬 WZ 例 B 的因子；只作记录）')
run_bad(V2b, '支撑上端 j=m 紧挨 j=m+1', expect_fail=True, deep=(12, 12), win=win2b, maxDk=2,
        search=[(1, 1), (2, 1), (1, 2), (2, 2), (3, 1), (3, 2), (2, 3)], required=False)

sys.exit(rep.done())
