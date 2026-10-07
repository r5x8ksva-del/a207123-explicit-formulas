# -*- coding: utf-8 -*-
"""s8-b3 独立核对 3：截断线性方程组（精确判定），佐证「单族表示不存在」。

不导入 code/tableB 下的任何脚本；U 的真值取自 code/core.py 的 U_fast_table。

表示 U_k = sum_{s>=s0} A(s) C(k+c-alpha s, beta s+d)（组合约定：除非 0<=下<=上，否则为 0）对 k>=k0 成立，
则对每个 K，方程 k=k_lo..K（k_lo=max(k0,0)）只涉及 e_s=(alpha+beta)s+d-c<=K 的有限个 A(s)，必须有解。
所以「截断方程组无解」是「这组 (c,d,k0) 下表示不存在」的精确证明（对更小的 k0 也成立）。

归一化（不失一般性）：
  beta>=1：s -> s+t 把 (c,d) 变成 (c-alpha t, d+beta t)，所以取 d in [0,beta-1]、s>=0（就是全部 beta s+d>=0 的 s）；
  beta=0 ：下指标 d>=0 固定（d<0 时全为 0），s0 的平移并入 c，所以取 s>=0、c 任意。
判定方法：模 p=2^61-1 消元。若 M 模 p 列满秩且 [M|b] 模 p 不相容，则在 Q 上也是列满秩且不相容
（整数矩阵的秩在 Q 上不小于模 p 的秩）——这是严格的「无解」证书。其余情形改用 Fraction 精确消元。
beta=0 时在全部行上 k+c-alpha s>=0 的「旧列」都是 k 的 d 次多项式，只保留 d+1 个（列空间不变），避免假的秩亏。
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_table  # noqa: E402

PR = (1 << 61) - 1
FAILS = []


def check(name, ok, info=''):
    print(('PASS ' if ok else 'FAIL ') + name + ((' | ' + info) if info else ''))
    sys.stdout.flush()
    if not ok:
        FAILS.append(name)


def C(n, k):
    if k < 0 or n < 0 or k > n:
        return 0
    return comb(n, k)


def build(alpha, beta, c, d, k_lo, K):
    n = alpha + beta
    if beta >= 1:
        s_min = -(d // beta)                 # ceil(-d/beta)
    else:
        if d < 0:
            return None, None
        s_min = 0
    s_max = (K + c - d) // n                 # 最大的 s 使 e_s<=K
    cols = list(range(s_min, s_max + 1))
    if beta == 0:
        # 在全部行上都处于多项式区（k_lo+c-alpha*s>=0）的列都是 k 的 d 次多项式，只保留 d+1 个
        old = [s for s in cols if k_lo + c - alpha * s >= 0]
        if len(old) > d + 1:
            keep = set(old[-(d + 1):])
            cols = [s for s in cols if (s not in old) or (s in keep)]
    rows = list(range(k_lo, K + 1))
    M = [[C(k + c - alpha * s, beta * s + d) for s in cols] for k in rows]
    return M, cols


def elim(M, b, p=None):
    """返回 (rank(M), inconsistent)。p=None 时用 Fraction 精确运算。"""
    nrows = len(M)
    ncols = len(M[0]) if nrows else 0
    if p is None:
        A = [[Fr(x) for x in row] + [Fr(bb)] for row, bb in zip(M, b)]
    else:
        A = [[x % p for x in row] + [bb % p] for row, bb in zip(M, b)]
    r = 0
    for col in range(ncols):
        piv = None
        for i in range(r, nrows):
            if A[i][col]:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pr = A[r]
        if p is None:
            invp = 1 / pr[col]
        else:
            invp = pow(pr[col], p - 2, p)
        for i in range(r + 1, nrows):
            f = A[i][col]
            if f:
                Ai = A[i]
                if p is None:
                    f = f * invp
                    for j in range(col, ncols + 1):
                        Ai[j] -= f * pr[j]
                else:
                    f = f * invp % p
                    for j in range(col, ncols + 1):
                        Ai[j] = (Ai[j] - f * pr[j]) % p
        r += 1
        if r == nrows:
            break
    inconsistent = any(A[i][ncols] for i in range(r, nrows))
    return r, inconsistent


def decide(alpha, beta, seq, c, d, k0, extra=15, K_cap=170):
    """返回 ('NO-cert' | 'NO-exact' | 'YES-exact' | 'YES-modp' , info)。"""
    k_lo = max(k0, 0)
    K = k_lo + 40
    while True:
        M, cols = build(alpha, beta, c, d, k_lo, K)
        if M is None:
            return 'NO-trivial', 'all terms vanish (beta=0,d<0)'
        nc = len(cols)
        if alpha + beta == 1 or len(M) >= nc + extra or K >= K_cap:
            break
        K += 10
    b = [seq[k] for k in range(k_lo, K + 1)]
    if nc == 0:
        bad = any(b)
        return ('NO-cert' if bad else 'YES-exact'), 'no unknowns'
    r, inc = elim(M, b, PR)
    if r == nc and inc:
        return 'NO-cert', 'rows=%d cols=%d K=%d' % (len(M), nc, K)
    if inc:
        r2, inc2 = elim(M, b, None)
        return ('NO-exact' if inc2 else 'YES-exact'), 'fallback rows=%d cols=%d rank=%d K=%d' % (len(M), nc, r2, K)
    return 'YES-modp', 'rows=%d cols=%d rank_p=%d K=%d' % (len(M), nc, r, K)


def d_range(beta):
    return range(0, beta) if beta >= 1 else range(0, 6)


def main():
    t0 = time.time()
    KMAX = 190
    T = U_fast_table(KMAX, 3)
    U = {m: [T[k][m] for k in range(KMAX + 1)] for m in range(4)}

    caseI = [(1, 1), (1, 2), (2, 2), (1, 3), (3, 1), (2, 3), (3, 2), (1, 4), (4, 1), (3, 3),
             (1, 5), (5, 1), (2, 5), (5, 2), (3, 4), (4, 3)]
    caseII = [(2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0)]
    caseIII = [(4, 2), (6, 3)]
    caseIV = [(0, 2), (0, 3), (0, 4), (0, 5)]
    thmS = [(2, 1)]

    # ---------- 1. 正对照：已知有表示的合成数列，求解器必须判为相容 ----------
    def seq_from(alpha, beta, c, d, A, K):
        return [sum(a * C(k + c - alpha * s, beta * s + d) for s, a in A.items()) for k in range(K + 1)]

    fib = seq_from(1, 1, 0, 0, {s: 1 for s in range(0, 120)}, KMAX)
    pos = []
    pos.append(('Fibonacci (1,1) c=0 d=0', 1, 1, fib, 0, 0, 0))
    for m in (1, 2, 3):
        # 1/P_m = sum_s S(m+s,m) x^{3s}(1-x)^{-(s+m+1)}：形状 (2,1)，归一化后 c=3m、d=0
        Pm = [1]
        for i in range(m + 1):
            nxt = [0] * (len(Pm) + 3)
            for j, x in enumerate(Pm):
                nxt[j] += x
                nxt[j + 1] -= x
                nxt[j + 3] -= i * x
            Pm = nxt
        inv = []
        for k in range(KMAX + 1):
            v = 1 if k == 0 else 0
            for j in range(1, min(k, len(Pm) - 1) + 1):
                v -= Pm[j] * inv[k - j]
            inv.append(v)
        pos.append(('[x^k]1/P_%d (2,1) c=%d d=0' % (m, 3 * m), 2, 1, inv, 3 * m, 0, 0))
    pos.append(('2^(k-1) (0,2) c=0 d=0 k0=1', 0, 2, [0] + [2 ** (k - 1) for k in range(1, KMAX + 1)], 0, 0, 1))
    pos.append(('floor(k/3)+1 (3,0) c=0 d=0', 3, 0, [k // 3 + 1 for k in range(KMAX + 1)], 0, 0, 0))
    pos.append(('sum C(k-s,2s) (1,2) c=0 d=0', 1, 2, seq_from(1, 2, 0, 0, {s: 1 for s in range(0, 80)}, KMAX), 0, 0, 0))
    pos.append(('sum C(k-4s,2s) (4,2) c=0 d=1', 4, 2, seq_from(4, 2, 0, 1, {s: (s + 1) for s in range(0, 40)}, KMAX), 0, 1, 0))
    pos.append(('sum (-1)^s C(k+2,3s+1) (0,3) c=2 d=1', 0, 3, seq_from(0, 3, 2, 1, {s: (-1) ** s for s in range(0, 70)}, KMAX), 2, 1, 0))
    for (name, a, bb, seq, c, d, k0) in pos:
        res, info = decide(a, bb, seq, c, d, k0)
        check('pos-' + name, res.startswith('YES'), res + ' ' + info)
        # 同一数列在错开一位的 c 上一般无解（说明求解器不是总说「有解」）
        res2, info2 = decide(a, bb, seq, c + 1, d, k0)
        print('   (same sequence, c+1: %s %s)' % (res2, info2))

    # ---------- 2. 对照组 (1,0)、(0,1)：理论上 k_lo+c-d>=0 时可解，否则首行全零而 U_k>0，无解 ----------
    ctrl_ok = True
    ctrl_cnt = 0
    for m in (1, 2, 3):
        for (a, bb) in [(1, 0), (0, 1)]:
            for c in range(-15, 16):
                for d in d_range(bb):
                    for k0 in (0, 10, 25):
                        k_lo = max(k0, 0)
                        res, info = decide(a, bb, U[m], c, d, k0)
                        expect_yes = (k_lo + c - d >= 0)
                        got_yes = res.startswith('YES')
                        ctrl_cnt += 1
                        if expect_yes != got_yes:
                            ctrl_ok = False
                            print('   control mismatch', (a, bb, m, c, d, k0, res, info))
    check('ctrl-(1,0),(0,1)-solvable-iff-k_lo+c-d>=0', ctrl_ok, '%d systems, m=1..3, c in [-15,15], k0 in {0,10,25}' % ctrl_cnt)
    # 可解的对照组再做一次精确构造：逐行解出新未知数并核对所有方程（(1,0) 取 d=0..5，(0,1) 取 d=0）
    exact_ok = True
    for m in (1, 2):
        for (a, bb, d) in [(1, 0, 0), (1, 0, 3), (0, 1, 0)]:
            for c in (0, 4, 9):
                k_lo = 0
                K = 60
                M, cols = build(a, bb, c, d, k_lo, K)
                b = [U[m][k] for k in range(k_lo, K + 1)]
                r, inc = elim(M, b, None)
                expect_yes = (k_lo + c - d >= 0)
                if inc == expect_yes:
                    exact_ok = False
                    print('   exact control mismatch', (a, bb, d, m, c), 'rank=%d inconsistent=%s' % (r, inc))
    check('ctrl-exact-Fraction-consistency', exact_ok, 'exact Fraction rank test on 18 control systems (k<=60): consistent iff k_lo+c-d>=0')

    # ---------- 3. 不存在性：所有非平凡形状 ----------
    groups = [('caseI', caseI), ('caseII', caseII), ('caseIII', caseIII), ('caseIV', caseIV), ('thmS(2,1)', thmS)]
    tot = {}
    for gname, shapes in groups:
        for (a, bb) in shapes:
            for m in (1, 2, 3):
                crange = range(-15, 16)
                k0s = (0, 10, 25)
                stats = {}
                for c in crange:
                    for d in d_range(bb):
                        for k0 in k0s:
                            res, info = decide(a, bb, U[m], c, d, k0)
                            stats[res] = stats.get(res, 0) + 1
                            if res.startswith('YES'):
                                print('   UNEXPECTED solvable:', (a, bb), 'm=%d c=%d d=%d k0=%d' % (m, c, d, k0), res, info)
                n_yes = sum(v for k, v in stats.items() if k.startswith('YES'))
                tot[(gname, a, bb, m)] = stats
                check('no-rep-%s-(%d,%d)-m=%d' % (gname, a, bb, m), n_yes == 0, str(stats))
    print('elapsed %.1fs' % (time.time() - t0))
    print('SUMMARY: %d FAIL' % len(FAILS), FAILS)
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
