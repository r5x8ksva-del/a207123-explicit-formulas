# -*- coding: utf-8 -*-
"""s9-b2 复核 r5：E_2 的三种两族 u 型表示（对应 notes/08 §3 列出的 6 个公共解，即 3 个无序指数对），独立实现。

E_2 = x^{-4} u^2/((1-u)(1-2u)) + 2 x^{-1} u/(1-2u)                                 {g1,g2} = {-4,-1}
    = x^{-4} [u^2/((1-u)(1-2u)) + 2u^2/(1-2u)] - x^{-3} 2u^2/(1-2u)                 {g1,g2} = {-4,-3}
    = x^{-3} u^2/((1-u)(1-2u)) + x^{-1} [u/((1-u)(1-2u)) + 2u/(1-2u)]               {g1,g2} = {-3,-1}
（用 x^{-1} = u x^{-4} - u x^{-3} 与 x^{-4} = x^{-3} + x^{-1}/u 互相改写；三种都不需要 Laurent 多项式 L。）
notes/08 记号 n = -3m-3-g1 = -9-g1，b = g2-g1：
  {-4,-1} ↔ (-5,3)、(-8,-3)；{-4,-3} ↔ (-5,1)、(-6,-1)；{-3,-1} ↔ (-6,2)、(-8,-2)。
逐项与自写 DP 的 E(k,2) 比较（k<=60）。
"""
import sys
from math import comb

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

K = 60
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def good(a, b, c):
    return b == c or a >= max(b, c)


def dpE(K, m):
    E = [0] * (K + 1)
    st = {(a, b): 1 for a in range(m + 1) for b in range(m + 1)}
    if K >= 2:
        E[2] = sum(1 for (a, b) in st if a < b)
    for k in range(3, K + 1):
        new = {}
        for (a, b), v in st.items():
            for c in range(m + 1):
                if good(a, b, c):
                    new[(b, c)] = new.get((b, c), 0) + v
        st = new
        E[k] = sum(v for (a, b), v in st.items() if a < b)
    return E


def useries(f, N):
    """f: s -> 系数，返回 [a_0..a_N]。"""
    return [f(s) for s in range(N + 1)]


def term(g, A):
    """x^g * sum_s A[s] u^s 的 x^0..x^K 系数（A[0] 必须为 0）。x^g u^s = x^{g+3s} (1-x)^{-s}。"""
    assert A[0] == 0
    out = [0] * (K + 1)
    for s in range(1, len(A)):
        if A[s] == 0:
            continue
        base = g + 3 * s
        for k in range(max(base, 0), K + 1):
            out[k] += A[s] * comb(k - base + s - 1, s - 1)
    return out


def add(*xs):
    return [sum(t) for t in zip(*xs)]


def main():
    E2 = dpE(K, 2)
    N = K
    # 1/((1-u)(1-2u)) = sum (2^{s+1}-1) u^s ；1/(1-2u) = sum 2^s u^s
    h = lambda s: 2 ** (s + 1) - 1
    g2 = lambda s: 2 ** s
    A_q2 = useries(lambda s: h(s - 2) if s >= 2 else 0, N)          # u^2/((1-u)(1-2u))
    A_q1 = useries(lambda s: h(s - 1) if s >= 1 else 0, N)          # u/((1-u)(1-2u))
    B_1 = useries(lambda s: 2 * g2(s - 1) if s >= 1 else 0, N)      # 2u/(1-2u)
    B_2 = useries(lambda s: 2 * g2(s - 2) if s >= 2 else 0, N)      # 2u^2/(1-2u)
    rep1 = add(term(-4, A_q2), term(-1, B_1))
    rep2 = add(term(-4, [a + b for a, b in zip(A_q2, B_2)]), term(-3, [-b for b in B_2]))
    rep3 = add(term(-3, A_q2), term(-1, [a + b for a, b in zip(A_q1, B_1)]))
    report('r5-E2-{-4,-1}', rep1 == E2, 'E_2 = x^{-4}u^2/((1-u)(1-2u)) + 2x^{-1}u/(1-2u)，k<=60')
    report('r5-E2-{-4,-3}', rep2 == E2, 'E_2 = x^{-4}[u^2/((1-u)(1-2u)) + 2u^2/(1-2u)] - x^{-3}2u^2/(1-2u)，k<=60')
    report('r5-E2-{-3,-1}', rep3 == E2, 'E_2 = x^{-3}u^2/((1-u)(1-2u)) + x^{-1}[u/((1-u)(1-2u)) + 2u/(1-2u)]，k<=60')
    pairs = {}
    for (g1, g2_) in [(-4, -1), (-1, -4), (-4, -3), (-3, -4), (-3, -1), (-1, -3)]:
        pairs[(g1, g2_)] = (-9 - g1, g2_ - g1)
    expect = {(-8, -3), (-8, -2), (-6, -1), (-6, 2), (-5, 1), (-5, 3)}
    report('r5-E2-map', set(pairs.values()) == expect, '三对 {g1,g2} 的 6 个有序 (n,b) = %s，恰为 notes/08 §3 的 6 个公共解' % sorted(pairs.values()))
    npass = sum(RES)
    print('SUMMARY s9-r5 pass=%d fail=%d' % (npass, len(RES) - npass))
    return 0 if npass == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
