# -*- coding: utf-8 -*-
"""t27_alpha：引理 S 中 α*≠0 的情形（t27_good 的六个例子里都碰巧 α*=0）。

做法：取引理 A 求出的递推 A，右乘 (σ_l−1)（σ_l: j_l↦j_l−1），得到仍然零化 T 的递推 A′=A(σ_l−1)。
A′ 在 σ=1 处为 0（C_0=0），所以「直接对 j⃗ 求和」只给出平凡关系，必须用二项式矩 C(j⃗,α*)。
  α1  E1：A(σ−1)                  ⇒ 期望 α*=(1,)
  α2  E3：A(σ_2−1)                ⇒ 期望 α*=(0,1)
  α3  E3：A(σ_1−1)+A(σ_2−1)        ⇒ 两个不可比的极小元 (1,0)、(0,1)，两种取法都要成立
  α4  E3：A(σ_1−1)(σ_2−1)          ⇒ 期望 α*=(1,1)
每种情形：Ω′=Ω_{I+1,J} 上网格严格核对 Σa′_ωQ′_ω≡0（引理 A 的恒等式随 Ω 变化，要重核）；引理 F；
(N2) 取 R′=max(I+1,J)；Q′ 上对一切 j⃗ 递推成立；引理 S 的 C_α、α*、分部求和、C_{α*}S=0。
"""
import sys
sys.dont_write_bytecode = True
import itertools
import time
from fractions import Fraction
from math import comb
import t27lib as L
import t27pipe as PP

rep = L.Reporter()


def addp(x, y):
    n = max(len(x), len(y))
    z = [Fraction(0)] * n
    for i, c in enumerate(x):
        z[i] += c
    for i, c in enumerate(y):
        z[i] += c
    while z and z[-1] == 0:
        z.pop()
    return z


def times_sigma_minus_one(a, l):
    """a ∘ (σ_l − 1)：(A(σ_l−1)f)(p)=Σ a_ω(k)[f(p−ω−e_l)−f(p−ω)]。"""
    out = {}
    for w, lst in a.items():
        w2 = list(w)
        w2[2 + l] += 1
        w2 = tuple(w2)
        out[w2] = addp(out.get(w2, []), lst)
        out[w] = addp(out.get(w, []), [-c for c in lst])
    return {w: v for w, v in out.items() if v}


def add_rec(a, b):
    out = dict(a)
    for w, lst in b.items():
        out[w] = addp(out.get(w, []), lst)
    return {w: v for w, v in out.items() if v}


def run_variant(name, T, a, I, J, kR, mR, win, expect, Fbox):
    print('\n' + '-' * 100)
    print('%s：例子 %s，Ω′=Ω_{I=%d,J=%d}' % (name, T.name, I, J))
    LA = L.LemmaA(T, I, J)
    assert all(w in set(LA.Omega) for w in a), '递推的位移超出 Ω′'
    ok, cnt, deg = LA.grid_verify(a)
    rep.check('[%s] 引理 A 的恒等式 Σa′_ω(k)Q′_ω≡0 在 Ω′ 上成立（网格 %s，%d 点）' % (name, deg, cnt), ok)
    PP.check_lemmaF(T, LA, a, Fbox, rep, label='[%s] ' % name)
    R = max(I, J)
    k1, m1 = kR(R), mR(R)
    okn, npts, viol = PP.check_N2(T, R, range(k1, k1 + 7), range(m1, m1 + 7), win)
    rep.check('[%s] (N2)：R=%d，Q_R={k≥%d,m≥%d}，%d 个支撑点' % (name, R, k1, m1, npts), okn, str(viol or ''))
    kq, mq = k1 + J, m1 + I
    Qk, Qm = range(kq, kq + 6), range(mq, mq + 6)
    fails, npf = PP.rec_failures(T, a, Qk, Qm, win, I)
    rep.check('[%s] 拼接：Q′={k≥%d,m≥%d} 上对一切 j⃗ 递推成立（%d 点）' % (name, kq, mq, npf), not fails, str(fails[:2]))
    A_, C, minimal = L.lemmaS_ops(a, T.r, I)
    zero = tuple([0] * T.r)
    rep.check('[%s] C_0=Σ_ν⃗A_ν⃗=0（直接对 j⃗ 求和只得到平凡关系）' % name, not C[zero])
    rep.check('[%s] 极小元集合 = %s（期望 %s）' % (name, sorted(minimal), sorted(expect)), sorted(minimal) == sorted(expect))
    S = PP.make_S(T, win)
    for alstar in sorted(minimal):
        Cst = C[alstar]
        lower = [al for al in C if al != alstar and all(x <= y for x, y in zip(al, alstar))]
        rep.check('[%s] α*=%s：α<α* 的 C_α 都为 0；C_{α*}≠0' % (name, alstar),
                  all(not C[al] for al in lower) and bool(Cst))
        rep.info('[%s] C_{α*} = %s' % (name, L.op_str(Cst)))
        # 用这个 α* 的二项式矩做分部求和；在 Q′ 上残差为 0
        kpts = [(k, m) for k in range(kq - 3, kq + 6) for m in range(mq - 3, mq + 6)]
        okw = True
        for (k, m) in kpts:
            lhs = Fraction(0)
            for jv in PP.jbox(win, k, m, I + 2, I + 2):
                jv = tuple(jv)
                c = L.binom_vec(jv, alstar)
                if c != 0:
                    lhs += c * L.apply_rec(T, a, (k, m) + jv)
            if lhs != L.apply_op(Cst, S, k, m):
                okw = False
        rep.check('[%s] α*=%s：Σ_j⃗ C(j⃗,α*)(A′T̃) = C_{α*}S（%d 个 (k,m)，含 Q′ 之外）' % (name, alstar, len(kpts)), okw)
        okz = all(L.apply_op(Cst, S, k, m) == 0 for k in Qk for m in Qm)
        rep.check('[%s] α*=%s：C_{α*}S=0 在 Q′ 的 6×6 个点上成立' % (name, alstar), okz)
    return C, minimal


t0 = time.time()
# ---------------------------------------------------------------- E1
E1 = L.Term('E1', 1, num=[((1, 0, 0), 0), ((0, 1, 0), 0)],
            den=[((0, 0, 1), 0), ((0, 1, -1), 0), ((0, 0, 1), 0), ((1, 0, -1), 0)], note='C(m,j)C(k,j)')
LA1, Dk1, good1 = PP.search_rec(E1, [(1, 1)], 0, rep, label='[E1] ')
a1 = good1[0]
_, C1, _ = L.lemmaS_ops(a1, 1, 1)
Cvar, _ = run_variant('α1', E1, times_sigma_minus_one(a1, 0), 2, 1, lambda R: R, lambda R: R,
                      lambda k, m: [(-2, max(k, m, 0) + 2)], [(1,)],
                      [range(-1, 10), range(-1, 10), range(-4, 13)])
rep.check('[α1] C_{(1)}(A(σ−1)) 与原递推的 C_0(A) 相同', Cvar[(1,)] == C1[(0,)])


# ---------------------------------------------------------------- E3（r=2）
def win3(k, m):
    return [(-2, max(k, m, 0) + 2), (-2, max(m, 0) + 2)]


E3 = L.Term('E3', 2, num=[((0, 1, 0, 0), 0), ((1, 0, 0, 0), 0)],
            den=[((0, 0, 1, 0), 0), ((0, 0, 0, 1), 0), ((0, 1, -1, -1), 0), ((0, 0, 1, 0), 0), ((1, 0, -1, 0), 0)],
            z=(1, 1, 1, -1), note='m!/(j1! j2! (m−j1−j2)!)·C(k,j1)·(−1)^{j2}')
LA3, Dk3, good3 = PP.search_rec(E3, [(1, 1)], 0, rep, label='[E3] ')
a3 = good3[0]
_, C3, _ = L.lemmaS_ops(a3, 2, 1)
Fbox3 = [range(-1, 6), range(-1, 6), range(-3, 8), range(-3, 8)]
kR3 = lambda R: R
Cv, _ = run_variant('α2', E3, times_sigma_minus_one(a3, 1), 2, 1, kR3, kR3, win3, [(0, 1)], Fbox3)
rep.check('[α2] C_{(0,1)}(A(σ_2−1)) 与原递推的 C_0(A) 相同', Cv[(0, 1)] == C3[(0, 0)])
Cv, _ = run_variant('α3', E3, add_rec(times_sigma_minus_one(a3, 0), times_sigma_minus_one(a3, 1)), 2, 1,
                    kR3, kR3, win3, [(1, 0), (0, 1)], Fbox3)
Cv, _ = run_variant('α4', E3, times_sigma_minus_one(times_sigma_minus_one(a3, 0), 1), 2, 1,
                    kR3, kR3, win3, [(1, 1)], Fbox3)
rep.check('[α4] C_{(1,1)}(A(σ_1−1)(σ_2−1)) 与原递推的 C_0(A) 相同', Cv[(1, 1)] == C3[(0, 0)])
print('\n用时 %.1f s' % (time.time() - t0))
sys.exit(rep.done())
