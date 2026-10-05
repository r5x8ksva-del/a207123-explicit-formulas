# -*- coding: utf-8 -*-
"""c5a 探索 5：h_k 补充结构。
(a) G_{-j}(x) := sum_k U_k(-j) x^k 的多项式递推 G_{-1}=1, G_{-j-1}=(1-x+j x^3)G_{-j}+j x^2；与 DP 多项式在负整数处的值对照
(b) h_k 第二首项系数的闭式
(c) h_k^{(d)}(1), d<=3 的多项式公式
(d) h_k(-1) 是否满足低阶常系数 / 多项式系数递推（精确线性代数猜测）
(e) Moebius：U_k(-2) = mu_{P_k}(0,1)（直接在允许行偏序集上算 Moebius 函数）
(f) N(k,.) 行多项式实根性（Sturm，独立于 h_k）、对数凹性
(g) H(z,t)=sum h_k z^k 的 PDE：(1-z)H - t(1-t)z^3[(1-t)H_t + H + z H_z] = 1 + t z^2
(h) 固定 i，[t^i]h_k 何时转正（数据）
"""
import os, sys, time
from fractions import Fraction
from math import factorial, comb, gcd
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from core import U_fast_table, N_from_U, allowed_rows
from explore_h import h_from_U, ev, sturm_real_roots


def stir1_unsigned(nmax):
    c = [[0] * (nmax + 2) for _ in range(nmax + 2)]
    c[0][0] = 1
    for n in range(1, nmax + 1):
        for k in range(1, n + 1):
            c[n][k] = (n - 1) * c[n - 1][k] + c[n - 1][k - 1]
    return c


def nullspace(rows, ncols):
    """有理矩阵零空间（高斯消元）。"""
    A = [list(map(Fraction, r)) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = 1 / A[r][c]
        A[r] = [x * inv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [Fraction(0)] * ncols
        v[f] = Fraction(1)
        for i, c in enumerate(piv):
            v[c] = -A[i][f]
        basis.append(v)
    return basis


def guess_P_rec(seq, start, order, deg):
    """找 sum_{i=0}^{order} p_i(k) a_{k-i} = 0（k 从 start+order 起），p_i 次数<=deg。返回解空间维数与可用方程数。"""
    rows = []
    for k in range(start + order, len(seq)):
        row = []
        for i in range(order + 1):
            for d in range(deg + 1):
                row.append(Fraction(k) ** d * seq[k - i])
        rows.append(row)
    ncols = (order + 1) * (deg + 1)
    if len(rows) < ncols + 5:
        return None, len(rows)
    ns = nullspace(rows, ncols)
    return len(ns), len(rows)


def main():
    t0 = time.time()
    K = 60
    T = U_fast_table(K, K)
    out = []
    H = {k: h_from_U(T, k) for k in range(0, K + 1)}
    N = {(k, q): N_from_U(T, k, q) for k in range(0, K + 1) for q in range(0, k + 1)}

    def U_poly_at(k, m):
        # U_k(m) = sum_q N(k,q) C(m+1,q)，广义二项式
        s = Fraction(0)
        for q in range(0, k + 1):
            num = Fraction(1)
            for i in range(q):
                num *= (m + 1 - i)
            s += N[(k, q)] * num / factorial(q)
        return s

    # (a)
    G = {1: [Fraction(1)]}
    for j in range(1, 21):
        g = G[j]
        new = [Fraction(0)] * (len(g) + 3)
        for i, c in enumerate(g):
            new[i] += c
            new[i + 1] -= c
            new[i + 3] += j * c
        new[2] += j
        while new and new[-1] == 0:
            new.pop()
        G[j + 1] = new
    oka = True
    for j in range(1, 22):
        for k in range(0, K + 1):
            val = U_poly_at(k, -j)
            g = G[j][k] if k < len(G[j]) else 0
            if val != g:
                oka = False
    out.append('(a) G_{-j} polynomial recursion vs U_k(-j) from DP polynomials, j<=21, k<=60: %s' % oka)
    c1 = stir1_unsigned(40)
    okb = True
    for j in range(2, 22):
        g = G[j]
        d = len(g) - 1
        exp = {3 * j - 3: factorial(j - 1), 3 * j - 4: factorial(j - 1), 3 * j - 5: -c1[j][2],
               3 * j - 6: factorial(j - 1), 3 * j - 7: c1[j][2] + c1[j][3],
               3 * j - 8: factorial(j - 1) - c1[j][2] - c1[j][3]}
        if d != 3 * j - 3:
            okb = False
        for e, v in exp.items():
            if e >= 0 and g[e] != v:
                okb = False
                out.append('   boundary mismatch j=%d e=%d got %s want %s' % (j, e, g[e], v))
    out.append('(a2) deg G_{-j}=3j-3 and top-6 coefficients closed forms, 2<=j<=21: %s' % okb)
    for j in range(1, 6):
        out.append('   G_{-%d} = %s' % (j, [int(c) for c in G[j]]))
    # (b) second-top coefficient of h_k
    def second_pred(k):
        a, r = divmod(k, 3)
        if r == 0:
            return (-1) ** (a + 1) * 2 * a * factorial(a)
        if r == 2:
            return (-1) ** a * (c1[a + 3][2] + c1[a + 3][3] - 3 * (a + 1) * factorial(a + 1))
        return (-1) ** a * (c1[a + 3][3] + c1[a + 3][2] - factorial(a + 2) - (3 * a + 2) * c1[a + 2][2])
    okb2 = all(len(H[k]) >= 2 and H[k][-2] == second_pred(k) for k in range(3, K + 1))
    out.append('(b) second-top coefficient of h_k closed form, 3<=k<=60: %s ; k=2: h_2=%s pred=%s' % (okb2, H[2], second_pred(2)))
    # (c) derivatives at t=1
    def hder(h, d):
        p = list(h)
        for _ in range(d):
            p = [i * p[i] for i in range(1, len(p))]
        return ev(p, 1) if p else 0
    D = lambda k, e: N.get((k, k - e), 0)
    okc = True
    for k in range(1, K + 1):
        for d in range(0, 4):
            lhs = hder(H[k], d)
            rhs = factorial(d) * sum((-1) ** e * comb(k - 1 - e, d - e) * D(k, e) for e in range(0, d + 1) if k - 1 - e >= 0)
            if lhs != rhs:
                okc = False
    out.append('(c) h_k^{(d)}(1) = d! sum_e (-1)^e C(k-1-e,d-e) N(k,k-e), d<=3, 1<=k<=60: %s' % okc)
    out.append('    h_k\'(1) = -(k^2-3k-2) for 4<=k<=60: %s' % all(hder(H[k], 1) == -(k * k - 3 * k - 2) for k in range(4, K + 1)))
    out.append('    h_k\'\'(1) data k=1..12: %s' % [hder(H[k], 2) for k in range(1, 13)])
    out.append('    h_k\'\'\'(1) data k=1..12: %s' % [hder(H[k], 3) for k in range(1, 13)])
    # (d) h_k(-1)
    hm1 = [ev(H[k], -1) for k in range(0, K + 1)]
    out.append('(d) h_k(-1), k=0..20: %s' % hm1[:21])
    for order in range(1, 16):
        dim, neq = guess_P_rec(hm1, 2, order, 0)
        if dim:
            out.append('    C-finite order %d: nullspace dim %s (eqs %d)' % (order, dim, neq))
    found = []
    for order in range(1, 6):
        for deg in range(0, 7):
            dim, neq = guess_P_rec(hm1, 2, order, deg)
            if dim is None:
                continue
            if dim > 0:
                found.append((order, deg, dim, neq))
    out.append('    P-recursive guesses (order<=5, deg<=6) with nonzero nullspace: %s' % found)
    import math
    out.append('    log|h_k(-1)|/k at k=20,30,40,50,60: %s' % [round(math.log(abs(hm1[k])) / k, 4) for k in (20, 30, 40, 50, 60)])
    # also h_k(2), h_k(-2) quick look
    out.append('    h_k(2), k<=12: %s' % [ev(H[k], 2) for k in range(13)])
    out.append('    h_k(1/2)*2^deg, k<=12: %s' % [ev(H[k], Fraction(1, 2)) * 2 ** (len(H[k]) - 1) for k in range(13)])
    # (e) Moebius
    oke = True
    for k in range(1, 11):
        rows = allowed_rows(k)
        idx = {r: i for i, r in enumerate(rows)}
        zero = tuple([0] * k)
        one = tuple([1] * k)
        # order elements by number of ones
        order = sorted(rows, key=sum)
        mu = {}
        for r in order:
            if r == zero:
                mu[r] = 1
                continue
            s = 0
            for q in order:
                if q != r and all(a <= b for a, b in zip(q, r)) and q in mu:
                    s += mu[q]
            mu[r] = -s
        u2 = U_poly_at(k, -2)
        if mu[one] != u2:
            oke = False
        out.append('   k=%d: mu(0,1)=%d  U_k(-2)=%s' % (k, mu[one], u2))
    out.append('(e) Moebius mu_{P_k}(0^,1^) == U_k(-2), k<=10: %s' % oke)
    # (f) N row real-rootedness + log-concavity
    okf = True
    oklc = True
    for k in range(2, K + 1):
        row = [N[(k, q)] for q in range(1, k + 1)]
        nreal, sqf, _ = sturm_real_roots(row)
        # distinct real roots count; multiplicity of -1 is ceil(k/3)-1
        mult = -(-k // 3) - 1
        if nreal + (mult - 1 if mult >= 1 else 0) != k - 1:
            okf = False
            out.append('   N-row k=%d: distinct real=%d, mult(-1)=%d, deg=%d, sqf=%s' % (k, nreal, mult, k - 1, sqf))
        for q in range(2, k):
            if N[(k, q)] ** 2 < N[(k, q - 1)] * N[(k, q + 1)]:
                oklc = False
    out.append('(f) N(k,.) row polynomial real-rooted (distinct real roots + extra multiplicity of -1 = k-1), 2<=k<=60: %s ; log-concave: %s' % (okf, oklc))
    # multiplicity of -1 in N-row polynomial
    def mult_at_minus1(p):
        p = [Fraction(c) for c in p]
        m = 0
        while p and ev(p, -1) == 0:
            # divide by (z+1)
            q = [Fraction(0)] * (len(p) - 1)
            rem = Fraction(0)
            # synthetic division by (z - (-1))
            acc = Fraction(0)
            coeffs = list(reversed(p))
            outc = []
            for c in coeffs:
                acc = acc * (-1) + c
                outc.append(acc)
            rem = outc.pop()
            p = list(reversed(outc))
            m += 1
        return m
    okm = all(mult_at_minus1([N[(k, q)] for q in range(1, k + 1)]) == -(-k // 3) - 1 for k in range(1, K + 1))
    out.append('    multiplicity of z=-1 in sum_q N(k,q) z^(q-1) equals ceil(k/3)-1, 1<=k<=60: %s' % okm)
    # (g) PDE for H, truncated: check coefficient of z^k for k<=60 as polynomials in t
    from polylib import padd, psub, pmul, pscale, pderiv, trim
    def hp(k):
        return [Fraction(c) for c in H[k]] if k >= 0 else []
    okg = True
    for k in range(0, K + 1):
        # (1-z)H: h_k - h_{k-1}
        lhs = psub(hp(k), hp(k - 1)) if k >= 1 else hp(0)
        if k >= 3:
            n = k - 3
            inner = padd(padd(pmul([1, -1], pderiv(hp(n))), hp(n)), pscale(hp(n), n))
            lhs = psub(lhs, pmul([0, 1, -1], inner))
        rhs = [1] if k == 0 else ([0, 1] if k == 2 else [])
        if trim(lhs) != trim([Fraction(c) for c in rhs]):
            okg = False
            out.append('   PDE mismatch at z^%d: %s' % (k, lhs))
    out.append('(g) PDE for H(z,t) coefficientwise, k<=60: %s' % okg)
    # (h) thresholds for fixed i
    for i in range(2, 9):
        ks = [k for k in range(i, K + 1) if len(H[k]) > i and H[k][i] <= 0]
        thr = (max(ks) + 1) if ks else i
        out.append('(h) [t^%d]h_k > 0 for %d<=k<=60 ; nonpositive at k in %s' % (i, thr, ks[-6:]))
    # Descartes: sign changes == number of roots > 1
    out.append('elapsed %.1fs' % (time.time() - t0))
    print('\n'.join(out))


if __name__ == '__main__':
    main()
