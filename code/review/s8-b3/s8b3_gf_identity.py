# -*- coding: utf-8 -*-
"""s8-b3 独立核对 4：§2(1) 的母函数化（整数精确运算）与适用范围的两个旁证。

不导入 code/tableB 下的任何脚本。
  g1  组合约定（除非 0<=下<=上，否则为 0）下，对随机的有限支撑 A(s)、负的 c、d、s0，以及 alpha=0 或 beta=0：
      sum_s A(s) C(k+c-alpha s, beta s+d) 的逐项（含负的 k）与 Laurent 级数
      Phi = sum_{beta s+d>=0} A(s) x^{e_s}(1-x)^{-(beta s+d+1)} 的系数一致，且 Phi = x^{d-c}(1-x)^{-(d+1)} A(v)
  g2  若把 beta s+d<0 的项也放进 A(v)（beta>=1），差是 Laurent 多项式，支撑在 k<=max(alpha s-c-1) 内
      （所以 §2(1) 写法上的含糊不影响论证）
  g3  适用范围旁证（不在定理范围内）：alpha<0 时，形状 (-1,2)（alpha+beta=1）对 U 的截断方程组有解（v 是单值化子，平凡存在）；
      (-1,3)、(-2,4)、(-1,4) 等 alpha+beta>=2 的形状只做数值观察
"""
import os
import random
import sys
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))
sys.path.insert(0, HERE)
from core import U_fast_table  # noqa: E402
import s8b3_linsys as LS  # noqa: E402  （本目录自己的脚本）

FAILS = []
KMAX = 45


def check(name, ok, info=''):
    print(('PASS ' if ok else 'FAIL ') + name + ((' | ' + info) if info else ''))
    sys.stdout.flush()
    if not ok:
        FAILS.append(name)


def C(n, k):
    if k < 0 or n < 0 or k > n:
        return 0
    return comb(n, k)


# Laurent 级数：dict 指数 -> 整数系数。内部截断到 TR=KMAX+400（各级数最低次 >= -150），只比较 k<=KMAX 的系数，
# 所以截断不影响被比较的系数。
TR = KMAX + 400


def one_minus_x_pow(r):
    """(1-x)^r，r 为任意整数，截断到 x^TR。"""
    if r >= 0:
        return {j: comb(r, j) * (-1) ** j for j in range(0, min(r, TR) + 1)}
    q = -r
    return {j: comb(j + q - 1, q - 1) for j in range(0, TR + 1)}


def lmul(a, b, lo=None):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            if i + j <= TR:
                out[i + j] = out.get(i + j, 0) + x * y
    return {k: v for k, v in out.items() if v != 0}


def shift(a, e):
    return {k + e: v for k, v in a.items()}


def ladd(a, b, coef=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + coef * v
    return {k: v for k, v in out.items() if v != 0}


def cut(a, lo):
    return {k: v for k, v in a.items() if lo <= k <= KMAX and v != 0}


def main():
    rng = random.Random(20261007)
    shapes = [(1, 0), (0, 1), (2, 1), (1, 1), (1, 2), (3, 0), (0, 2), (0, 3), (2, 3), (4, 2), (5, 0), (2, 5)]
    ok1 = True
    ok2 = True
    ntest = 0
    for trial in range(400):
        al, be = shapes[trial % len(shapes)]
        n = al + be
        c = rng.randint(-6, 6)
        d = rng.randint(-6, 6)
        s0 = rng.randint(-5, 3)
        A = {s: rng.randint(-9, 9) for s in range(s0, s0 + 8)}
        es = {s: n * s + d - c for s in A}
        lo = min(es.values()) - 2
        # 直接和（含负的 k）
        direct = {k: sum(a * C(k + c - al * s, be * s + d) for s, a in A.items()) for k in range(lo, KMAX + 1)}
        direct = {k: v for k, v in direct.items() if v != 0}
        # Phi：只取 beta s+d>=0 的项
        Phi = {}
        for s, a in A.items():
            ns = be * s + d
            if ns < 0:
                continue
            Phi = ladd(Phi, shift(one_minus_x_pow(-(ns + 1)), es[s]), a)
        Phi = cut(Phi, lo)
        # 前因子 * A(v)：v^s = x^{n s} (1-x)^{-beta s}
        pre = shift(one_minus_x_pow(-(d + 1)), d - c)

        def Av(include_removed):
            out = {}
            for s, a in A.items():
                if (be * s + d < 0) and not include_removed:
                    continue
                out = ladd(out, shift(one_minus_x_pow(-be * s), n * s), a)
            return out
        fac = cut(lmul(pre, Av(False)), lo)
        ntest += 1
        if not (direct == Phi == fac):
            ok1 = False
            print('   mismatch', (al, be, c, d, s0))
        if be >= 1:
            full = cut(lmul(pre, Av(True)), -10 ** 6)
            diff = ladd(full, cut(lmul(pre, Av(False)), -10 ** 6), -1)
            removed = [s for s in A if be * s + d < 0]
            bound = max((al * s - c - 1 for s in removed), default=None)
            if removed:
                if any(k > bound for k in diff):
                    ok2 = False
                    print('   g2 support problem', (al, be, c, d, s0), bound, sorted(diff)[-3:])
            elif diff:
                ok2 = False
    check('g1-gf-identity-and-factorization', ok1, '%d random cases, k in [min e_s-2, %d]' % (ntest, KMAX))
    check('g2-removed-terms-give-Laurent-polynomial', ok2, 'support of difference within k<=max(alpha s-c-1)')

    # g3 适用范围旁证
    T = U_fast_table(190, 2)
    U = {m: [T[k][m] for k in range(191)] for m in (1, 2)}
    res = {}
    for (al, be) in [(-1, 2), (-2, 3), (-1, 3), (-2, 4), (-1, 4), (-3, 5)]:
        for m in (1, 2):
            st = {}
            for c in range(-6, 7):
                for d in range(0, be):
                    for k0 in (0, 10):
                        r, info = LS.decide(al, be, U[m], c, d, k0)
                        st[r] = st.get(r, 0) + 1
            res[(al, be, m)] = st
            print('   scope (alpha,beta)=(%d,%d) m=%d: %s' % (al, be, m, st))
    yes12 = all(all(k.startswith('YES') or k == 'NO-cert' for k in res[(-1, 2, m)]) for m in (1, 2))
    # (-1,2)：k_lo+c-d>=0 时（首行有新未知数）应可解
    ok3 = True
    for m in (1, 2):
        for c in range(0, 7):
            r, info = LS.decide(-1, 2, U[m], c, 0, 0)
            if not r.startswith('YES'):
                ok3 = False
    check('g3-alpha<0,alpha+beta=1-(-1,2)-solvable', ok3 and yes12, 'trivial existence also for alpha<0 when alpha+beta=1')
    print('SUMMARY: %d FAIL' % len(FAILS), FAILS)
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
