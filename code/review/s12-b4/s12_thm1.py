# -*- coding: utf-8 -*-
"""复核 s12-b4：notes/12 定理 1（情形 A、D、引理 RH）与 §4 表第 4 行。
U 的真值来自 code/core.py；E 用自写 DP（与 (W_m-1)/P_m 对照）；其余自写。"""
import random
import time
from fractions import Fraction as Fr
from math import comb, gcd

import numpy as np

from s12_common import (Checker, C, U_core, tables_UEc, P_poly, W_poly, b_poly, series_div,
                        pmul, padd, reduce_bi, system_status, exact_solve, xi_float)

ck = Checker('s12_thm1')
t0 = time.time()
K = 42
MP = 2147483647  # 2^31-1，numpy 下乘积不溢出 int64


def rank_mod_np(rows, ncols, p=MP):
    if not rows or ncols == 0:
        return 0
    A = np.array([[x % p for x in r] for r in rows], dtype=np.int64)
    nr = A.shape[0]
    rank = 0
    for col in range(ncols):
        if rank == nr:
            break
        nz = np.nonzero(A[rank:, col])[0]
        if nz.size == 0:
            continue
        piv = rank + int(nz[0])
        if piv != rank:
            A[[rank, piv]] = A[[piv, rank]]
        inv = pow(int(A[rank, col]), p - 2, p)
        A[rank] = (A[rank] * inv) % p
        f = A[:, col].copy()
        f[rank] = 0
        nzr = np.nonzero(f)[0]
        if nzr.size:
            A[nzr] = (A[nzr] - (f[nzr, None] * A[rank][None, :]) % p) % p
        rank += 1
    return rank


def status(A, b):
    """模 2^31-1 满列秩且增广秩更大 ⇒ Q 上不相容；否则退回精确消元（s12_common.system_status）。"""
    nc = len(A[0]) if A else 0
    if nc == 0:
        return 'consistent' if all(x == 0 for x in b) else 'inconsistent-exact'
    rA = rank_mod_np(A, nc)
    if rA == nc:
        rAb = rank_mod_np([list(r) + [x] for r, x in zip(A, b)], nc + 1)
        if rAb > rA:
            return 'inconsistent-cert'
    return system_status(A, b)


def shape_rows(f, alpha, beta, c, d, k0, K, s_lo, s_hi):
    sv = list(range(s_lo, s_hi + 1))
    A = [[C(k + c - alpha * s, beta * s + d) for s in sv] for k in range(k0, K + 1)]
    b = [f[k] for k in range(k0, K + 1)]
    return A, b


def s_range_pos(alpha, beta, c, d, K):
    """α+β>=1、β>=1：一切 βs+d>=0 且在 k<=K 内出现（e s+d-c<=K）的 s。"""
    e = alpha + beta
    s_lo = -(d // beta)
    s_hi = (K - d + c) // e
    return s_lo, s_hi


# ------------------------------------------------ 真值
UT = U_core(K, 4)
Uo, Eo, Uco = tables_UEc(K, 4)
ck.check('truth-U-own-vs-core', all(Uo[k][m] == UT[k][m] for k in range(K + 1) for m in range(5)),
         '自写 DP 的 U 与 core.U_fast_table 一致（k<=42，m<=4）')
okE = True
for m in range(0, 5):
    ser = series_div(padd(W_poly(m), [-1]), P_poly(m), K)
    okE &= all(ser[k] == Eo[k][m] for k in range(K + 1))
ck.check('truth-E-vs-gf', okE, 'E（按定义：以上升 a_{k-1}<a_k 结尾）=[x^k](W_m-1)/P_m，m<=4，k<=42')
seqs = {f'U{m}': [UT[k][m] for k in range(K + 1)] for m in (1, 2, 3)}
seqs.update({f'E{m}': [Eo[k][m] for k in range(K + 1)] for m in (2, 3)})

# ------------------------------------------------ 情形 D：α<0、α+β>=2 的截断方程组
shapesD = [(-1, 3), (-1, 4), (-2, 4), (-2, 5), (-3, 5), (-1, 6), (-4, 6), (-3, 7), (-5, 7), (-2, 8)]
for (alpha, beta) in shapesD:
    cnt = 0
    bad = []
    for name, f in seqs.items():
        for c in range(-3, 4):
            for d in range(-2, 4):
                for k0 in (0, 8):
                    s_lo, s_hi = s_range_pos(alpha, beta, c, d, K)
                    A, b = shape_rows(f, alpha, beta, c, d, k0, K, s_lo, s_hi)
                    st = status(A, b)
                    cnt += 1
                    if not st.startswith('inconsistent'):
                        bad.append((name, c, d, k0))
    ck.check(f'D-linsys ({alpha},{beta})', not bad,
             f'{cnt} 个方程组（U m=1,2,3；E m=2,3；c∈[-3,3]，d∈[-2,3]，k0∈{{0,8}}，k<=42，含一切 βs+d>=0 的 s）全部无解'
             + (f'；可解：{bad[:5]}' if bad else ''))

# 对照：α+β=1、α<0 的形状可解（c=d=0，k0=0）
for (alpha, beta) in [(-1, 2), (-2, 3), (-4, 5)]:
    oks = []
    for name, f in seqs.items():
        s_lo, s_hi = s_range_pos(alpha, beta, 0, 0, K)
        A, b = shape_rows(f, alpha, beta, 0, 0, 0, K, s_lo, s_hi)
        oks.append(exact_solve(A, b)[0])
    ck.check(f'D-control ({alpha},{beta})', all(oks), 'α+β=1：对 U、E 均精确可解（基变换）')

# 反向：由真的 (−1,3)、(−2,4) 单族和造出的数列应判为可解
random.seed(12)
for (alpha, beta, c, d) in [(-1, 3, 1, 0), (-2, 4, -2, 1), (-3, 5, 0, 2)]:
    e = alpha + beta
    Asec = {s: random.randint(-9, 9) for s in range(0, 12)}
    f = [sum(Asec[s] * C(k + c - alpha * s, beta * s + d) for s in Asec) for k in range(K + 1)]
    s_lo, s_hi = s_range_pos(alpha, beta, c, d, K)
    A, b = shape_rows(f, alpha, beta, c, d, 0, K, s_lo, s_hi)
    st = status(A, b)
    ck.check(f'D-reverse ({alpha},{beta})', st == 'consistent',
             f'人为构造的 ({alpha},{beta}) 单族和被判为 {st}（方法不会误判真表示为无解）')

# ------------------------------------------------ 情形 A：β<0，或 β>=0 且 α+β<=0
shapesA = [(1, -1), (2, -1), (0, -1), (-1, -1), (3, -2), (-1, 1), (-2, 2), (-1, 0), (0, 0), (-3, 2), (-2, 1)]
for (alpha, beta) in shapesA:
    cnt = 0
    bad = []
    for name in ('U1', 'U2', 'E2'):
        f = seqs[name]
        for c in range(-2, 3):
            for d in range(-2, 3):
                for k0 in (0, 5):
                    for s0 in (-4, 0):
                        if beta < 0:
                            s_hi = d // (-beta)          # βs+d>=0 ⇔ s<=d/|β|
                            svals = (s0, s_hi)
                        else:
                            svals = (s0, s0 + 8)          # 有限性迫使 A 有限支撑；取 9 个 s 的窗口
                        A, b = shape_rows(f, alpha, beta, c, d, k0, K, svals[0], svals[1])
                        if svals[1] < svals[0]:
                            A = [[] for _ in range(k0, K + 1)]
                        st = status(A, b)
                        cnt += 1
                        if not st.startswith('inconsistent'):
                            bad.append((name, c, d, k0, s0))
    ck.check(f'A-linsys ({alpha},{beta})', not bad, f'{cnt} 个方程组全部无解' + (f'；可解：{bad[:4]}' if bad else ''))

# ------------------------------------------------ (H1)(H2) 的一般性：人造有理函数
F1 = series_div([1], pmul(b_poly(1), b_poly(3)), K)                       # 1/(b1 b3)
F2 = series_div([1, 2, 0, 0, -1], pmul(pmul(b_poly(0), b_poly(1)), b_poly(2)), K)
F3 = series_div([1], b_poly(1), K)                                         # 1/b1
synth = {'1/(b1b3)': [int(x) for x in F1], '(1+2x-x^4)/(b0b1b2)': [int(x) for x in F2], '1/b1': [int(x) for x in F3]}
for (alpha, beta) in [(3, 0), (1, 2), (0, 2), (4, 2), (2, 2), (0, 3), (1, 1), (5, 1), (-1, 3), (-2, 4), (-1, 4)]:
    cnt = 0
    bad = []
    for name, f in synth.items():
        for c in range(-3, 4):
            for d in range(-2, 4):
                for k0 in (0, 8):
                    if beta == 0:
                        if d < 0:
                            continue
                        s_lo, s_hi = -6, (K + c - d) // alpha       # β=0：s 下界任取，取 -6
                    else:
                        s_lo, s_hi = s_range_pos(alpha, beta, c, d, K)
                    A, b = shape_rows(f, alpha, beta, c, d, k0, K, s_lo, s_hi)
                    st = status(A, b)
                    cnt += 1
                    if not st.startswith('inconsistent'):
                        bad.append((name, c, d, k0))
    ck.check(f'H-general ({alpha},{beta})', not bad, f'人造 F（满足 (H1)(H2)）{cnt} 个方程组全部无解' + (f'；可解：{bad[:4]}' if bad else ''))
# 例外 (2,1) 对一般 F 确实排除不了：1/b1 与 1/(b1b3) 都有 u 型单族表示
for name in ('1/b1', '1/(b1b3)'):
    f = synth[name]
    found = []
    for c in range(-3, 4):
        for d in range(-2, 4):
            s_lo, s_hi = s_range_pos(2, 1, c, d, K)
            A, b = shape_rows(f, 2, 1, c, d, 0, K, s_lo, s_hi)
            if status(A, b) == 'consistent':
                found.append((c, d))
    ck.check(f'H-general (2,1) {name}', len(found) > 0, f'(2,1) 形状可解的 (c,d)：{found[:6]}（定理 1 的例外是真的例外）')

# ------------------------------------------------ G_m、E_m 满足 (H2)：W_m(ξ)=ξ+ξ²，(W_m-1)(ξ)=ξ^5
okH = True
x5 = reduce_bi([0, 0, 0, 0, 0, 1], 1)
for m in range(1, 13):
    w = reduce_bi(W_poly(m), 1)
    okH &= (w == (Fr(0), Fr(1), Fr(1)))
    w1 = reduce_bi(padd(W_poly(m), [-1]), 1)
    okH &= (w1 == x5)
ck.check('H2-residue', okH and x5 == (Fr(-1), Fr(1), Fr(1)),
         'Q[x]/(b_1) 中 W_m≡ξ+ξ²、W_m-1≡ξ^5=-1+ξ+ξ²（1<=m<=12），均非零')

# ------------------------------------------------ 情形 D 的纤维乘积（数值）
xi = xi_float()
okF = True
details = []
for (alpha, beta) in shapesD:
    e, b = alpha + beta, beta
    v0 = xi ** (e - 3 * b)
    coeffs = [0.0] * (b + 1)
    for j in range(b + 1):
        coeffs[j] -= v0 * comb(b, j) * (-1) ** j
    coeffs[e] += 1.0
    roots = np.roots(coeffs[::-1])
    pe = np.prod(roots)
    p1 = np.prod(1 - roots)
    Wp = np.prod((1 - roots) / roots ** 3)
    pred = (-1) ** (b + 1) * xi ** (3 * b - e)
    ws = (1 - roots) / roots ** 3
    nint = sum(1 for w in ws if abs(w.imag) < 1e-9 and w.real > 0.5 and abs(w.real - round(w.real)) < 1e-9)
    ok = (abs(pe - 1) < 1e-8 and abs(p1 - (-1) ** (b + 1) / v0) < 1e-8 * abs(1 / v0)
          and abs(Wp - pred) < 1e-8 and abs(pred) < 1 and len(roots) == b and min(abs(roots)) > 1e-6
          and min(abs(1 - roots)) > 1e-6)
    okF &= ok
    details.append(f'({alpha},{beta}):∏w={pred:+.4f},整数w点={nint}')
ck.check('D-fiber-product', okF, '∏η=1、∏(1-η)=(-1)^{b+1}/v_0、∏w=(-1)^{b+1}ξ^{3b-e}∈(-1,1)，纤维点无 0、1（数值） '
         + '; '.join(details))
# 反向：(2,1)（v=u，v_0=1）的纤维恰是 b_1 的三个根，w 全为 1 —— 纤维法对它确实无效
r21 = np.roots([1, 0, 1, -1])         # x^3 - (1-x) = 0
w21 = (1 - r21) / r21 ** 3
ck.check('D-fiber-reverse (2,1)', np.allclose(w21, 1), '(2,1) 的纤维点全满足 w=1，乘积论证推不出矛盾（与定理 S 需要另证一致）')

# ------------------------------------------------ 引理 RH：数值单值群 + 块系统
def fiber_roots(t, e, b):
    co = [0j] * (b + 1)
    for j in range(b + 1):
        co[j] -= t * comb(b, j) * (-1) ** j
    co[e] += 1
    return np.roots(co[::-1])


def track_seg(cur, ta, tb, e, b, depth=0):
    new = fiber_roots(tb, e, b)
    n = len(cur)
    D = np.abs(cur[:, None] - new[None, :])
    perm = D.argmin(axis=1)
    if len(set(perm.tolist())) == n:
        S = np.abs(new[:, None] - new[None, :]) + np.eye(n) * 1e300
        sep = S.min(axis=1)[perm]
        if np.all(D[np.arange(n), perm] < 0.25 * sep):
            return new[perm]
    if depth > 40:
        raise RuntimeError('root tracking failed')
    tm = 0.5 * (ta + tb)
    mid = track_seg(cur, ta, tm, e, b, depth + 1)
    return track_seg(mid, tm, tb, e, b, depth + 1)


def track(points, e, b, r0):
    cur = r0.copy()
    for ta, tb in zip(points[:-1], points[1:]):
        cur = track_seg(cur, ta, tb, e, b)
    D = np.abs(cur[:, None] - r0[None, :])
    perm = D.argmin(axis=1)
    assert len(set(perm.tolist())) == len(perm) and D[np.arange(len(perm)), perm].max() < 1e-6
    return [int(x) for x in perm]


def cycles(perm):
    n = len(perm)
    seen = [False] * n
    out = []
    for i in range(n):
        if not seen[i]:
            c = []
            j = i
            while not seen[j]:
                seen[j] = True
                c.append(j)
                j = perm[j]
            out.append(c)
    return out


def minimal_block(gens, n, seed):
    par = list(range(n))

    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a
    q = []
    for s in seed[1:]:
        x, y = find(seed[0]), find(s)
        if x != y:
            par[y] = x
            q.append((x, y))
    while q:
        a, bb = q.pop()
        for g in gens:
            x, y = find(g[a]), find(g[bb])
            if x != y:
                par[y] = x
                q.append((x, y))
    r = find(seed[0])
    return frozenset(j for j in range(n) if find(j) == r)


def monodromy(e, b):
    xc = -e / (b - e)
    tc = xc ** e / (1 - xc) ** b
    r0 = 0.05 * abs(tc)
    ts = 1j * r0
    roots0 = fiber_roots(ts, e, b)
    th = np.linspace(0, 2 * np.pi, 401)
    loop0 = list(ts * np.exp(1j * th))
    loop0[-1] = ts
    ta = tc * (1 - 0.1)
    seg = list(np.linspace(ts, ta, 201))
    circ = list(tc + (ta - tc) * np.exp(1j * th))
    circ[-1] = ta
    loopc = seg + circ[1:] + list(np.linspace(ta, ts, 201))[1:]
    loopc[-1] = ts
    g0 = track(loop0, e, b, roots0)
    gc = track(loopc, e, b, roots0)
    order = np.argsort(np.abs(roots0))
    O0 = [int(j) for j in order[:e]]
    return g0, gc, O0


okRH = True
for (e, b) in [(2, 3), (2, 4), (3, 4), (2, 5), (3, 5), (4, 5), (2, 6), (3, 6), (4, 6), (5, 6),
               (2, 8), (4, 8), (6, 8), (3, 9), (6, 9)]:
    g0, gc, O0 = monodromy(e, b)
    cyc0 = sorted(len(c) for c in cycles(g0))
    cycc = sorted(len(c) for c in cycles(gc))
    prod = [g0[gc[j]] for j in range(b)]
    cycinf = sorted(len(c) for c in cycles(prod))
    o0cyc = [c for c in cycles(g0) if set(c) & set(O0)]
    shape_ok = (cyc0 == sorted([e] + ([b - e] if b - e >= 1 else [])) and cycc == [1] * (b - 2) + [2]
                and cycinf == [b] and len(o0cyc) == 1 and set(o0cyc[0]) == set(O0))
    blk = minimal_block([g0, gc], b, O0)
    blocks = set()
    for j in range(b):
        if j != O0[0]:
            B = minimal_block([g0, gc], b, [O0[0], j])
            if len(B) < b:
                blocks.add(B)
    sizes = sorted(len(B) for B in blocks)
    g = gcd(e, b)
    pred = sorted(b // k for k in range(2, g + 1) if g % k == 0)
    ok = shape_ok and len(blk) == b and sizes == pred and all(not (set(O0) <= B) for B in blocks)
    okRH &= ok
    ck.check(f'RH-monodromy (e,b)=({e},{b})', ok,
             f'g0 型 {cyc0}，g_c 型 {cycc}，g0g_c 型 {cycinf}；含 O_0 的最小块大小 {len(blk)}（=b 即 K=C(v)）；'
             f'非平凡块大小 {sizes}，预测（k|gcd(e,b)，k>=2 ⇒ b/k）{pred}；没有非平凡块包含 O_0')
# 反向：e=1 时 C((v))=C((x))，O_0 只有一点，最小块是单点（K=C(x)），算法不是永远返回全集
for (e, b) in [(1, 3), (1, 4), (1, 6)]:
    g0, gc, O0 = monodromy(e, b)
    blk = minimal_block([g0, gc], b, O0)
    ck.check(f'RH-reverse (e,b)=({e},{b})', len(blk) == 1, f'含 O_0 的最小块大小 {len(blk)}（应为 1）')

# ------------------------------------------------ §4 表第 4 行：系数是 k 的一次式的 u 型单族
okid = True
for k in range(-6, 31):
    for c in range(-4, 5):
        for s in range(-4, 11):
            for dp in range(-4, 5):
                n, r = k + c - 2 * s, s + dp
                if k * C(n, r) != (r + 1) * C(n + 1, r + 1) - (1 + c - 2 * s) * C(n, r):
                    okid = False
ck.check('row4-identity', okid, 'k·C(n,r)=(r+1)C(n+1,r+1)-(1+c-2s)C(n,r)（n=k+c-2s，r=s+d\'），在报告的二项式约定下逐项成立（含负指标）')


def lin_k_rows(f, c, dp, k0, K):
    s_lo = -dp
    s_hi = (K - dp + c) // 3
    sv = list(range(s_lo, s_hi + 1))
    A = [[C(k + c - 2 * s, s + dp) for s in sv] + [k * C(k + c - 2 * s, s + dp) for s in sv] for k in range(k0, K + 1)]
    b = [f[k] for k in range(k0, K + 1)]
    return A, b


for m in (2, 3):
    f = seqs[f'U{m}']
    cnt = 0
    bad = []
    for c in range(-3, 4):
        for dp in range(-2, 5):
            for k0 in (0, 6):
                A, b = lin_k_rows(f, c, dp, k0, K)
                st = status(A, b)
                cnt += 1
                if not st.startswith('inconsistent'):
                    bad.append((c, dp, k0))
    ck.check(f'row4-linsys U m={m}', not bad, f'{cnt} 个「Σ_s(A(s)+kB(s))C(k+c-2s,s+d\')」方程组全部无解' + (f'；可解 {bad[:4]}' if bad else ''))
random.seed(5)
coef ={s: (random.randint(-6, 6), random.randint(-6, 6)) for s in range(0, 12)}
f = [sum((a + k * bb) * C(k + 1 - 2 * s, s + 2) for s, (a, bb) in coef.items()) for k in range(K + 1)]
A, b = lin_k_rows(f, 1, 2, 0, K)
ck.check('row4-reverse', status(A, b) == 'consistent', '人为构造的一次式系数 u 型单族被判为可解')

print(f'time {time.time() - t0:.1f}s')
import sys
sys.exit(0 if ck.summary() else 1)
