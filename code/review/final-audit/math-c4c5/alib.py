# -*- coding: utf-8 -*-
"""final-audit math-c4c5：自写小工具（不依赖 polylib；只在交叉核对时调用 core）。"""
import os
import sys
from fractions import Fraction
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))

OUT = []


def say(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    OUT.append(s)


def check(tag, ok, desc):
    say(('PASS' if ok else 'FAIL'), tag, '::', desc)
    return ok


# ---------------------------------------------------------------- 自写高度 DP（原始定义 (b)）
def U_col(m, K):
    """[U_0(m),...,U_K(m)]：长 k、值在 {0..m}、每个相邻三元组 (a,b,c) 满足 b==c 或 a>=max(b,c) 的序列数。
    状态 f[(b,c)] = 以 (b,c) 结尾的合法前缀数；转移逐个三元组字面判断（写法与 core 不同：不用后缀和）。"""
    vals = range(m + 1)
    out = [1]
    if K >= 1:
        out.append(m + 1)
    if K >= 2:
        f = {(b, c): 1 for b in vals for c in vals}
        out.append(len(f))
        for _ in range(3, K + 1):
            g = {}
            for (a, b), v in f.items():
                for c in vals:
                    if b == c or (a >= b and a >= c):
                        g[(b, c)] = g.get((b, c), 0) + v
            f = g
            out.append(sum(f.values()))
    return out[:K + 1]


def N_tri(K):
    """自写 N 三角：N[k][q]。k<=2 三行直接写（N(0,0)=1；N(1,1)=1；N(2,1)=1,N(2,2)=2），k>=3 用三角递推。"""
    N = [[0] * (K + 3) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1] = 1
        N[2][2] = 2

    def g(k, q):
        if k < 0 or q < 0 or q > k:
            return 0
        return N[k][q]
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            N[k][q] = (g(k - 1, q - 1) + g(k - 1, q)
                       + (q - 1) * (g(k - 3, q - 2) + 2 * g(k - 3, q - 1) + g(k - 3, q)))
    return N


# ---------------------------------------------------------------- 有理多项式（升幂列表）
def ptrim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return ptrim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def pscale(p, c):
    return ptrim([c * a for a in p])


def pmul(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return ptrim(r)


def peval(p, x):
    r = 0
    for a in reversed(p):
        r = r * x + a
    return r


def pshiftarg(p, s):
    """p(x+s)。"""
    r = []
    for a in reversed(p):
        r = padd(pmul(r, [s, 1]), [a])
    return r


def pdivmod(p, q):
    p = [Fraction(a) for a in ptrim(p)]
    q = [Fraction(a) for a in ptrim(q)]
    out = [Fraction(0)] * max(len(p) - len(q) + 1, 0)
    while len(p) >= len(q) and p:
        c = p[-1] / q[-1]
        dd = len(p) - len(q)
        out[dd] = c
        for i, b in enumerate(q):
            p[i + dd] -= c * b
        p = ptrim(p)
    return ptrim(out), p


def interp_newton(xs, ys):
    """Newton 插值 -> 升幂 Fraction 系数。"""
    n = len(xs)
    c = [Fraction(y) for y in ys]
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            c[i] = (c[i] - c[i - 1]) / (xs[i] - xs[i - j])
    poly = []
    for i in range(n - 1, -1, -1):
        poly = padd(pmul(poly, [-xs[i], 1]), [c[i]])
    return poly


def falling_poly(shift, i):
    """(x+shift)(x+shift-1)...(x+shift-i+1) 作为 x 的整系数多项式。"""
    p = [1]
    for r in range(i):
        p = pmul(p, [shift - r, 1])
    return p


def fwd_diffs(vals):
    d = []
    row = list(vals)
    while row:
        d.append(row[0])
        row = [row[j + 1] - row[j] for j in range(len(row) - 1)]
    return d


def stirling1_unsigned(nmax):
    c = [[0] * (nmax + 2) for _ in range(nmax + 2)]
    c[0][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            c[n][k] = c[n - 1][k - 1] + (n - 1) * c[n - 1][k]
    return c


def H(n):
    return sum((Fraction(1, i) for i in range(1, n + 1)), Fraction(0))


def dfact(n):
    """n!!（n<=0 时为 1）。"""
    r = 1
    while n > 1:
        r *= n
        n -= 2
    return r


def write_log(name):
    """各脚本的单独输出放在本目录 out/ 下；汇总日志由 run_all.py 写到 logs/final_audit_math-c4c5.log。"""
    d = os.path.join(HERE, 'out')
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, name), 'w', encoding='utf-8') as f:
        f.write('\n'.join(OUT) + '\n')
