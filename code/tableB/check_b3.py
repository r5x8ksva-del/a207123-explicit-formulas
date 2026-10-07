# -*- coding: utf-8 -*-
"""表 B 的 B3（单族「二项式形状」单和的完整分类）的核对脚本（2026-10-07）。证明见 notes/06-主Agent-表B-B3单族形状分类.md。

逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b3 pass=<n> fail=<n>」。
  b3-xi      Q(xi)=Q[x]/(x^3+x-1) 中的精确事实：b_1 无有理根；N(xi)=1；判别式 -31；b_1 | P_m 且 W_m(xi)=xi+xi^2（1<=m<=20）；
             xi^N（1<=|N|<=300）在基 1, xi, xi^2 下不是有理数
  b3-case4   情形 (IV)：a_beta=(1-xi)^beta-(-xi)^beta 在 1<=beta<=12 中只有 beta=1 是有理数
  b3-fiber   浮点示意（不是证明的一部分）：alpha>=1、alpha+beta<=12 的全部形状中，纤维上 w=(1-eta)/eta^3 为正整数的点
             都少于 alpha+beta 个，例外只有 (1,0)（alpha+beta=1，平凡存在）与 (2,1)（定理 S）；beta>=1、e!=0 时纤维点乘积 = (-1)^(alpha+beta+1) xi^e
  b3-linsys  精确佐证：U_k(m) = sum_s A(s) C(k+c-alpha s, beta s+d)（k0<=k<=40）对 13 种形状、m=1,2、k0 in {0,6}、
             c in [-2,2]、d in [-2,3]（beta=0 时 s0 in {-2,0}）全部无解；判据：系数矩阵模素数满列秩且增广系统模该素数不相容
             （这蕴含有理数上不相容），列秩不满时退回分数精确消元；对照组 (1,0)、(0,1) 用分数精确求解，可解
  b3-rev     反向检查：把 U 换成某个 (2,0) 形状单和本身生成的序列，b3-linsys 的判据判为「有解」（不会误报无解）
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_table  # noqa: E402

try:
    import numpy as np
except ImportError:
    np = None

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def binom(n, k):
    if k < 0 or n < 0 or k > n:
        return 0
    return comb(n, k)


# ---------------------------------------------------------------- Q(xi)，xi^3 = 1 - xi
def qmul(a, b):
    """a, b 为长度 3 的 Fraction 列表（基 1, xi, xi^2）。"""
    c = [Fr(0)] * 5
    for i in range(3):
        for j in range(3):
            c[i + j] += a[i] * b[j]
    # xi^4 = xi - xi^2, xi^3 = 1 - xi
    c[1] += c[4]
    c[2] -= c[4]
    c[0] += c[3]
    c[1] -= c[3]
    return c[:3]


def qpow(a, e):
    if e < 0:
        a = qinv(a)
        e = -e
    r = [Fr(1), Fr(0), Fr(0)]
    while e:
        if e & 1:
            r = qmul(r, a)
        a = qmul(a, a)
        e >>= 1
    return r


def mulmat(a):
    """乘以 a 的矩阵（列为 a*1, a*xi, a*xi^2 的坐标）。"""
    cols = [qmul(a, [Fr(1), Fr(0), Fr(0)]), qmul(a, [Fr(0), Fr(1), Fr(0)]), qmul(a, [Fr(0), Fr(0), Fr(1)])]
    return [[cols[j][i] for j in range(3)] for i in range(3)]


def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def qnorm(a):
    return det3(mulmat(a))


def qinv(a):
    # 解 M x = e_0
    M = mulmat(a)
    A = [row[:] + [Fr(1 if i == 0 else 0)] for i, row in enumerate(M)]
    for col in range(3):
        p = next(i for i in range(col, 3) if A[i][col] != 0)
        A[col], A[p] = A[p], A[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        for i in range(3):
            if i != col and A[i][col] != 0:
                f = A[i][col]
                A[i] = [x - f * y for x, y in zip(A[i], A[col])]
    return [A[i][3] for i in range(3)]


def is_rational(a):
    return a[1] == 0 and a[2] == 0


def poly_eval_q(p, a):
    """整数多项式 p（低次在前）在 Q(xi) 元素 a 处的值。"""
    r = [Fr(0)] * 3
    for c in reversed(p):
        r = qmul(r, a)
        r[0] += c
    return r


def P_poly(m):
    out = [1]
    for i in range(m + 1):
        b = [1, -1, 0, -i]
        new = [0] * (len(out) + 3)
        for x, u in enumerate(out):
            for y, v in enumerate(b):
                new[x + y] += u * v
        out = new
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def W_poly(m):
    W = [1]
    for j in range(1, m + 1):
        t = [0, 0] + [j * c for c in P_poly(j - 1)]
        n = max(len(W), len(t))
        W = [(W[i] if i < len(W) else 0) + (t[i] if i < len(t) else 0) for i in range(n)]
    return W


def main():
    t0 = time.time()
    XI = [Fr(0), Fr(1), Fr(0)]
    ONE = [Fr(1), Fr(0), Fr(0)]
    # b3-xi
    ok = all(1 - x - x ** 3 != 0 for x in (1, -1))
    ok = ok and qnorm(XI) == 1
    a, b, c = 0, 1, -1   # X^3 + aX^2 + bX + c
    disc = a * a * b * b - 4 * b ** 3 - 4 * a ** 3 * c - 27 * c * c + 18 * a * b * c
    ok = ok and disc == -31
    for m in range(1, 21):
        ok = ok and poly_eval_q(P_poly(m), XI) == [0, 0, 0]
        ok = ok and poly_eval_q(W_poly(m), XI) == [Fr(0), Fr(1), Fr(1)]
    ok = ok and all(not is_rational(qpow(XI, N)) for N in range(-300, 301) if N != 0)
    report('b3-xi', ok, 'b_1 无有理根；N(xi)=1；判别式=-31；b_1|P_m 且 W_m(xi)=xi+xi^2（1<=m<=20）；xi^N 非有理（1<=|N|<=300）')
    # b3-case4
    rat = []
    for beta in range(1, 13):
        aa = [x - y for x, y in zip(qpow([Fr(1), Fr(-1), Fr(0)], beta), qpow([Fr(0), Fr(-1), Fr(0)], beta))]
        if is_rational(aa):
            rat.append((beta, aa[0]))
    report('b3-case4', rat == [(1, Fr(1))], '情形 (IV)：(1-xi)^beta-(-xi)^beta 在 1<=beta<=12 中只有 beta=1 为有理数（=1）')
    # b3-fiber（浮点示意）
    if np is None:
        report('b3-fiber', False, '缺 numpy')
    else:
        xi = float(np.real([r for r in np.roots([1, 0, 1, -1]) if abs(r.imag) < 1e-12][0]))
        bad, excep = [], []
        for n_ in range(1, 13):
            for alpha in range(1, n_ + 1):
                beta = n_ - alpha
                e = alpha - 2 * beta
                # F(x) = x^n - xi^e (1-x)^beta
                F = [0.0] * (n_ + 1)
                F[n_] += 1.0
                for i in range(beta + 1):
                    F[i] -= xi ** e * comb(beta, i) * (-1) ** i
                roots = np.roots(list(reversed(F)))
                cnt = 0
                for eta in roots:
                    w = (1 - eta) / eta ** 3
                    if abs(w.imag) < 1e-9 and w.real > 0.5 and abs(w.real - round(w.real)) < 1e-9:
                        cnt += 1
                if cnt >= n_:
                    excep.append((alpha, beta))
                if beta >= 1 and e != 0:
                    prod = np.prod(roots)
                    if abs(prod - (-1) ** (n_ + 1) * xi ** e) > 1e-8:
                        bad.append((alpha, beta))
        report('b3-fiber', excep == [(1, 0), (2, 1)] and not bad,
               '浮点示意：alpha+beta<=12 中纤维点全为 b_w 根的形状只有 (1,0)（平凡存在）与 (2,1)（定理 S）；乘积关系在 beta>=1, e!=0 时成立%s'
               % ('' if not bad else '；不符：%s' % bad))
    # b3-linsys
    K = 40
    Tab = U_fast_table(K, 2)
    P = (1 << 61) - 1
    shapes = [(1, 2), (2, 3), (1, 4), (4, 1), (3, 0), (2, 0), (2, 2), (6, 3), (0, 2), (0, 3), (3, 2), (1, 1), (2, 1)]
    found, undecided, nsys = [], [], 0
    for (al, be) in shapes:
        for m in (1, 2):
            seq = [Tab[k][m] for k in range(K + 1)]
            for k0 in (0, 6):
                for c in range(-2, 3):
                    for d in range(-2, 4):
                        for s0 in ((-2, 0) if be == 0 else (None,)):
                            nsys += 1
                            res = sys_status(seq, al, be, c, d, s0, k0, K, P)
                            if res == 'solvable':
                                found.append((al, be, m, k0, c, d, s0))
    ctrl = all(solve_exact([Tab[k][m] for k in range(K + 1)], al, be, c, d, s0, 0, K)
               for (al, be, c, d, s0) in [(1, 0, 0, 0, 0), (1, 0, 1, 1, 0), (0, 1, 0, 0, None), (0, 1, 2, 0, None)]
               for m in (1, 2))
    report('b3-linsys', not found and not undecided and ctrl,
           '%d 个方程组（13 种形状，m=1,2）全部无解（模 2^61-1 满列秩且不相容；列秩不满的退回分数精确消元）；对照组 (1,0)、(0,1) 精确可解%s'
           % (nsys, '' if not (found or undecided) else '；有解或未定：%s %s' % (found[:3], undecided[:3])))
    # b3-rev：用一个真的 (2,0) 形状单和造序列，判据不能判为无解
    Afake = {s: (s * s - 3 * s + 7) for s in range(0, 30)}
    fake = [sum(Afake[s] * binom(k + 1 - 2 * s, 1) for s in Afake) for k in range(K + 1)]
    st = sys_status(fake, 2, 0, 1, 1, 0, 0, K, P)
    report('b3-rev', st != 'inconsistent' and solve_exact(fake, 2, 0, 1, 1, 0, 0, K),
           '反向检查：由 (2,0) 形状单和造出的序列，判据不报「无解」，精确求解有解')
    print('time %.1fs' % (time.time() - t0))


def unknowns(al, be, c, d, s0, K):
    if be > 0:
        lo = -(d // be)          # ceil(-d/be)：更小的 s 使下指标为负，二项式为 0
    else:
        lo = s0
    hi = (K + c - d) // (al + be)
    return list(range(lo, hi + 1))


def rows_for(seq, al, be, c, d, s0, k0, K):
    us = unknowns(al, be, c, d, s0, K)
    rows = []
    for k in range(k0, K + 1):
        rows.append([binom(k + c - al * s, be * s + d) for s in us] + [seq[k]])
    return us, rows


def sys_status(seq, al, be, c, d, s0, k0, K, P):
    us, rows = rows_for(seq, al, be, c, d, s0, k0, K)
    if not us:
        return 'inconsistent' if any(r[-1] for r in rows) else 'solvable'
    A = [[x % P for x in r] for r in rows]
    ncol = len(us)
    r_ = 0
    for col in range(ncol):
        p = next((i for i in range(r_, len(A)) if A[i][col]), None)
        if p is None:
            continue
        A[r_], A[p] = A[p], A[r_]
        inv = pow(A[r_][col], P - 2, P)
        A[r_] = [x * inv % P for x in A[r_]]
        for i in range(len(A)):
            if i != r_ and A[i][col]:
                f = A[i][col]
                A[i] = [(x - f * y) % P for x, y in zip(A[i], A[r_])]
        r_ += 1
    full = (r_ == ncol)
    incons = any(A[i][-1] for i in range(r_, len(A)))
    if full and incons:
        return 'inconsistent'
    # 模 P 判据不适用（列秩不满，例如 beta=0 时多列相关或整列为零）：退回分数精确消元
    return 'solvable' if solve_exact(seq, al, be, c, d, s0, k0, K) else 'inconsistent'


def solve_exact(seq, al, be, c, d, s0, k0, K):
    us, rows = rows_for(seq, al, be, c, d, s0, k0, K)
    A = [[Fr(x) for x in r] for r in rows]
    r_ = 0
    for col in range(len(us)):
        p = next((i for i in range(r_, len(A)) if A[i][col] != 0), None)
        if p is None:
            continue
        A[r_], A[p] = A[p], A[r_]
        pv = A[r_][col]
        A[r_] = [x / pv for x in A[r_]]
        for i in range(len(A)):
            if i != r_ and A[i][col] != 0:
                f = A[i][col]
                A[i] = [x - f * y for x, y in zip(A[i], A[r_])]
        r_ += 1
    return all(A[i][-1] == 0 for i in range(r_, len(A)))


if __name__ == '__main__':
    main()
    n_pass = sum(RESULTS)
    n_fail = len(RESULTS) - n_pass
    print('SUMMARY b3 pass=%d fail=%d' % (n_pass, n_fail))
    sys.exit(0 if n_fail == 0 else 1)
