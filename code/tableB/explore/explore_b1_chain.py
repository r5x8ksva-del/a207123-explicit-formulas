# -*- coding: utf-8 -*-
"""B1 探索（续二）：找一组在 n_k = (1+z) n_{k-1} + Phi n_{k-3} 下封闭的交错关系。

Phi n := (1+z) T n，T n := z(1+z) n' + 2 z n。
g <= f 的定义同 explore_b1_dir.py（根含重数；-1 与 0 处的重根精确处理）。只做观察。
"""
import sys
sys.path.insert(0, __file__.rsplit('code', 1)[0] + 'code')
from tableB.explore.explore_b1_interlace import N_table, real_roots  # noqa: E402
from tableB.explore.explore_b1_dir import leq, padd, pmul_1z  # noqa: E402


def peval(c, x):
    s = 0
    for a in reversed(c):
        s = s * x + a
    return s


def divide_root(c, r):
    """c 除以 (z - r)，要求整除。高次在前做综合除法。"""
    hi = list(reversed(c))
    out = [hi[0]]
    for a in hi[1:]:
        out.append(a + r * out[-1])
    rem = out.pop()
    assert rem == 0
    return list(reversed(out))


def roots_full(c):
    c = list(c)
    while len(c) > 1 and c[-1] == 0:
        c.pop()
    z0 = 0
    while len(c) > 1 and c[0] == 0:
        c = c[1:]
        z0 += 1
    m1 = 0
    while len(c) > 1 and peval(c, -1) == 0:
        c = divide_root(c, -1)
        m1 += 1
    r = real_roots(c)
    if r is None:
        return None
    return sorted(list(r) + [-1.0] * m1 + [0.0] * z0)


def T(n):
    d = [i * n[i] for i in range(1, len(n))]
    t = padd(pmul_1z(d) if d else [0], [2 * x for x in n])
    return [0] + t


def Phi(n):
    return pmul_1z(T(n))


def check(name, g, f, store, k):
    rg, rf = roots_full(g), roots_full(f)
    ok = rg is not None and rf is not None and leq(rg, rf)
    store.setdefault(name, {})[k] = ok


if __name__ == '__main__':
    K = 45
    N = N_table(K)
    n = {k: [N[k][q] for q in range(1, k + 1)] for k in range(1, K + 1)}
    # n_k = (1+z)n_{k-1} + Phi n_{k-3}，k>=4
    for k in range(4, K + 1):
        assert padd(pmul_1z(n[k - 1]), Phi(n[k - 3])) == n[k]
    S = {}
    for k in range(6, K + 1):
        check('I: n[k-1]<=n[k]', n[k - 1], n[k], S, k)
        check('J: n[k-1]<=Phi n[k-3]', n[k - 1], Phi(n[k - 3]), S, k)
        check('K: n[k-2]<=T n[k-3]', n[k - 2], T(n[k - 3]), S, k)
        check('L: Phi n[k-5]<=T n[k-3]', Phi(n[k - 5]), T(n[k - 3]), S, k)
        check('M: n[k-3]<=T n[k-3] trivial?', n[k - 3], T(n[k - 3]), S, k)
        check('P: (1+z)n[k-2]<=n[k]', pmul_1z(n[k - 2]), n[k], S, k)
        check('Q: n[k-2]<=n[k]', n[k - 2], n[k], S, k)
        check('R: n[k-3]<=n[k]', n[k - 3], n[k], S, k)
        check('S: (1+z)n[k-3]<=n[k-1]', pmul_1z(n[k - 3]), n[k - 1], S, k)
        check('U: T n[k-3]<=n[k]', T(n[k - 3]), n[k], S, k)
        check('V: Phi n[k-3]<=n[k]...', Phi(n[k - 3]), n[k], S, k)
        check('W: n[k]<=T n[k-2]', n[k], T(n[k - 2]), S, k)
        check('X: n[k]<=Phi n[k-2]', n[k], Phi(n[k - 2]), S, k)
        check('Y: T n[k-1]... n[k]<=T n[k-1]', n[k], T(n[k - 1]), S, k)
        check('Z: Phi n[k-4]<=n[k-1]?', Phi(n[k - 4]), n[k - 1], S, k)
    for name in S:
        fails = [k for k, v in S[name].items() if not v]
        print('%-34s fails at: %s' % (name, fails if fails else 'none (6..%d)' % K))
