# -*- coding: utf-8 -*-
"""s9-b2 复核 r2：纤维条件 D_i(n,b)=0 的小范围精确解（独立实现，不导入项目代码）。

D_i(n,b) := pi(eta^b) ∧ pi(W eta^n)，pi = 基 (1,eta,eta^2) 下后两个坐标；W = Wt_i（U）或 Wt_i - 1（E）。
另外直接按定义核对「D_i(n,b)=0 ⇔ 1, eta^b, W eta^n 的 3x3 坐标行列式为 0 ⇔ 三个共轭根上的 3x3 行列式为 0」（浮点抽查）。

  r2-small40   |n|,|b|<=40（b≠0）的全部解，与 notes/08 / check_b2 的计数比较（U1 28、U2 4、E1 185、E2 16、E3 2）
  r2-m1        m=1 的 F3 型：U_k(1) = sum_s C(k+2-2s,1+s) - sum_s C(k-2s,s)（自写 DP 核对 k<=60），(g1,g2)=(-7,-3)，
               (n,b)=(1,4)、(-3,-4) 满足 D_1=0；D_2 的值
  r2-E2pair    E_2 的真两族表示对应的 (n,b)=(-5,3)、(-8,-3) 确实满足 E 的纤维 1、2 条件（m=2 的纤维条件只到 i=2）
  r2-conj      det[(1),(eta_j^b),(W(eta_j) eta_j^n)]（复根上浮点）与 det V * D_i(n,b) 一致（推论 6 的 V·C 分解）
  r2-small150  |n|,|b|<=150 的全部解：U 纤维 1∧2、E 纤维 1∧2∧3 无公共解；列出各纤维的解数
"""
import sys
import time
from fractions import Fraction as Fr
from math import comb
import numpy as np

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def C(a, b):
    if b < 0 or a < 0 or b > a:
        return 0
    return comb(a, b)


def good(a, b, c):
    return b == c or a >= max(b, c)


def dpU(K, m):
    U = [0] * (K + 1)
    U[0] = 1
    if K >= 1:
        U[1] = m + 1
    st = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    if K >= 2:
        U[2] = len(st)
    for k in range(3, K + 1):
        new = {}
        for (a, b), v in st.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
        st = new
        U[k] = sum(st.values())
    return U


def Wt(i, kind):
    w = [0] * (3 * i + 3)
    w[0] = 1 if kind == 'U' else 0
    for j in range(1, i + 1):
        ff = 1
        for t in range(j):
            ff *= i - t
        w[3 * j + 2] += j * ff
    return w


class Alg:
    """Q[x]/(b_i)，b_i = 1 - x - i x^3；基 (1,x,x^2)。"""

    def __init__(self, i):
        self.i = Fr(i)

    def mulx(self, v):
        q = 1 / self.i
        return [v[2] * q, v[0] - v[2] * q, v[1]]

    def mul(self, a, b):
        acc = [Fr(0)] * 3
        v = list(b)
        for t in range(3):
            if a[t]:
                acc = [acc[r] + a[t] * v[r] for r in range(3)]
            v = self.mulx(v)
        return acc

    def ev(self, poly):
        acc = [Fr(0)] * 3
        for cf in reversed(poly):
            acc = self.mulx(acc)
            acc[0] += cf
        return acc


def powers(A, i, R):
    """eta^e，e = -R..R。eta^{-1} = 1 + i eta^2。"""
    pos = {0: [Fr(1), Fr(0), Fr(0)]}
    for e in range(1, R + 1):
        pos[e] = A.mulx(pos[e - 1])
    inv = [Fr(1), Fr(0), Fr(i)]
    for e in range(1, R + 1):
        pos[-e] = A.mul(pos[-e + 1], inv)
    return pos


def solutions(i, kind, R):
    A = Alg(i)
    pw = powers(A, i, R)
    W = A.ev(Wt(i, kind))
    WE = {n: A.mul(W, pw[n]) for n in range(-R, R + 1)}
    sols = set()
    for n in range(-R, R + 1):
        w = WE[n]
        for b in range(-R, R + 1):
            if b == 0:
                continue
            v = pw[b]
            if v[1] * w[2] - v[2] * w[1] == 0:
                sols.add((n, b))
    return sols, A, pw, W


def Dval(A, pw, W, n, b):
    w = A.mul(W, pw[n])
    v = pw[b]
    return v[1] * w[2] - v[2] * w[1]


def main():
    t0 = time.time()
    # ---- |n|,|b|<=40 ----
    S = {}
    ctx = {}
    for kind, fibers in (('U', (1, 2)), ('E', (1, 2, 3))):
        for i in fibers:
            s, A, pw, W = solutions(i, kind, 40)
            S[(kind, i)] = s
            ctx[(kind, i)] = (A, pw, W)
    expect = {('U', 1): 28, ('U', 2): 4, ('E', 1): 185, ('E', 2): 16, ('E', 3): 2}
    counts = {k: len(v) for k, v in S.items()}
    cu = S[('U', 1)] & S[('U', 2)]
    ce12 = S[('E', 1)] & S[('E', 2)]
    ce = ce12 & S[('E', 3)]
    triv = {(n, b) for (n, b) in S[('E', 1)] if n == -5 or n + 5 == b}
    ok = counts == expect and not cu and not ce
    ok = ok and sorted(S[('U', 2)]) == [(-15, -10), (-8, -5), (-5, 10), (-3, 5)]
    ok = ok and sorted(S[('E', 3)]) == [(-13, -5), (-8, 5)]
    ok = ok and sorted(ce12) == [(-8, -3), (-8, -2), (-6, -1), (-6, 2), (-5, 1), (-5, 3)]
    report('r2-small40', ok, '计数 %s（期望 %s）；U 公共解 %s；E 纤维1∧2 公共解 %s；E 纤维1∧2∧3 公共解 %s；'
           'U 纤维 2 解 %s；E 纤维 3 解 %s；E 纤维 1 的 185 个解中平凡族（n=-5 或 n+5=b）%d 个，非平凡 %d 个；U 纤维 1 的解 %s'
           % (dict(sorted(counts.items())), dict(sorted(expect.items())), sorted(cu), sorted(ce12), sorted(ce),
              sorted(S[('U', 2)]), sorted(S[('E', 3)]), len(triv), len(S[('E', 1)]) - len(triv), sorted(S[('U', 1)])))
    # ---- m=1 F3 ----
    K = 60
    U1 = dpU(K, 1)
    okF3 = all(U1[k] == sum(C(k + 2 - 2 * s, 1 + s) for s in range(k + 3)) - sum(C(k - 2 * s, s) for s in range(k + 1))
               for k in range(K + 1))
    g1, g2 = -2 * (1 + 0) - 2 - 3, -2 * (1 - 1) - 0 - 3
    pairs = [(-3 * 1 - 3 - g1, g2 - g1), (-3 * 1 - 3 - g2, g1 - g2)]
    A1, pw1, W1 = ctx[('U', 1)]
    A2, pw2, W2 = ctx[('U', 2)]
    d1 = [Dval(A1, pw1, W1, n, b) for (n, b) in pairs]
    d2 = [Dval(A2, pw2, W2, n, b) for (n, b) in pairs]
    ok = okF3 and (g1, g2) == (-7, -3) and pairs == [(1, 4), (-3, -4)] and all(v == 0 for v in d1) and d2 == [Fr(3, 8), Fr(-6)]
    report('r2-m1', ok, 'F3 型对 k<=60 成立：%s；(g1,g2)=%s；(n,b)=%s；D_1=%s；D_2=%s' % (okF3, (g1, g2), pairs, [str(v) for v in d1], [str(v) for v in d2]))
    # ---- E_2 的真表示 ----
    ok = all(p in S[('E', 1)] and p in S[('E', 2)] for p in [(-5, 3), (-8, -3)])
    A3, pw3, W3 = ctx[('E', 3)]
    d3 = [Dval(A3, pw3, W3, n, b) for (n, b) in [(-5, 3), (-8, -3)]]
    report('r2-E2pair', ok, 'E_2 的两族表示 (g1,g2)=(-4,-1) 对应 (n,b)=(-5,3)、(-8,-3)，满足 E 纤维 1、2：%s；'
           '它们在纤维 3 上 D_3=%s（m=2 没有纤维 3，所以不矛盾；m>=3 时纤维 3 排除它们）' % (ok, [str(v) for v in d3]))
    # ---- 共轭行列式 vs V*D ----
    okc = True
    worst = 0.0
    rng = np.random.default_rng(20261008)
    for kind, i in (('U', 1), ('U', 2), ('E', 1), ('E', 2), ('E', 3)):
        A, pw, W = ctx[(kind, i)]
        roots = np.roots([-i, 0, -1, 1])
        V = np.array([[1, r, r * r] for r in roots])
        detV = np.linalg.det(V)
        Wp = Wt(i, kind)
        for _ in range(40):
            n = int(rng.integers(-12, 13))
            b = int(rng.integers(-12, 13))
            if b == 0:
                continue
            Mx = np.array([[1, r ** b, sum(c * r ** t for t, c in enumerate(Wp)) * r ** n] for r in roots])
            lhs = np.linalg.det(Mx)
            rhs = detV * float(Dval(A, pw, W, n, b))
            err = abs(lhs - rhs) / max(1.0, abs(rhs))
            worst = max(worst, err)
            if err > 1e-6:
                okc = False
    report('r2-conj', okc, '共轭根上的 3x3 行列式 = det V · D_i(n,b)（浮点抽查 5 个纤维×约 40 组，最大误差 %.1e）' % worst)
    # ---- |n|,|b|<=150 ----
    R = 150
    S2 = {}
    for kind, fibers in (('U', (1, 2)), ('E', (1, 2, 3))):
        for i in fibers:
            S2[(kind, i)] = solutions(i, kind, R)[0]
    cu = S2[('U', 1)] & S2[('U', 2)]
    ce = S2[('E', 1)] & S2[('E', 2)] & S2[('E', 3)]
    triv = {(n, b) for (n, b) in S2[('E', 1)] if n == -5 or n + 5 == b}
    nontriv_E1 = sorted(S2[('E', 1)] - triv)
    report('r2-small150', not cu and not ce,
           '|n|,|b|<=150：计数 %s；U 公共解 %s；E 公共解 %s；U 纤维 1 的解仍为 %d 个（与 |n|,|b|<=40 相同：%s）；'
           'U 纤维 2 的解 %s；E 纤维 2 的解 %s；E 纤维 3 的解 %s；E 纤维 1 非平凡解 %d 个，最大 |n|,|b| = %d'
           % (dict(sorted((k, len(v)) for k, v in S2.items())), sorted(cu), sorted(ce), len(S2[('U', 1)]),
              S2[('U', 1)] == S[('U', 1)], sorted(S2[('U', 2)]), sorted(S2[('E', 2)]), sorted(S2[('E', 3)]),
              len(nontriv_E1), max(max(abs(n), abs(b)) for (n, b) in nontriv_E1)))
    print('time %.1fs' % (time.time() - t0))
    npass = sum(RES)
    print('SUMMARY s9-r2 pass=%d fail=%d' % (npass, len(RES) - npass))
    return 0 if npass == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
