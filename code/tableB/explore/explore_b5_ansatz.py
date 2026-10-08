# -*- coding: utf-8 -*-
"""B5 探索：N^E(k,q)（以及 N、N^c）是否有「骨架型」双和
    X(k,q) = sum_{s,p} A(p,s) * C(q+e, p) * C(k + a*s + p + c, s + q + d)
其中 A(p,s) 是与 k、q 无关的未知数。对每组整数偏移 (a,c,d,e) 解精确线性方程组（Fraction 高斯消元），
先在小范围拟合，再在更大范围检验。真值来自 core 的原始定义（容斥 + 高度 DP）。
"""
import os, sys
from fractions import Fraction
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from core import U_fast_table, binom


def bin_(n, k):
    if k < 0 or n < 0 or k > n:
        return 0
    return binom(n, k)


def build_tables(K, Q):
    T = U_fast_table(K, Q + 1)
    # E 部分：U = U^c + E，U^c_k(m) = [x^k] 1/P_m（用递推算），E = U - U^c
    # U^c 用块分解：U^c_k(m) = sum_s S(m+s,m) C(k+m-2s, k-3s)
    from core import stirling2_table
    S = stirling2_table(K + Q + 5)
    def Uc(k, m):
        tot = 0
        for s in range(0, k // 3 + 1):
            tot += S[m + s][m] * bin_(k + m - 2 * s, k - 3 * s)
        return tot
    Ucn = [[Uc(k, m) for m in range(Q + 1)] for k in range(K + 1)]
    def ie(tab, k, q):
        s = 0
        for i in range(q + 1):
            if i == 0:
                u = 1 if k == 0 else 0
            else:
                u = tab[k][i - 1]
            s += (-1) ** (q - i) * bin_(q, i) * u
        return s
    N = [[ie(T, k, q) for q in range(Q + 1)] for k in range(K + 1)]
    Nc = [[ie(Ucn, k, q) if not (k == 0) else (1 if q == 0 else 0) for q in range(Q + 1)] for k in range(K + 1)]
    NE = [[N[k][q] - Nc[k][q] for q in range(Q + 1)] for k in range(K + 1)]
    return N, Nc, NE


def solve(rows, rhs, nvar):
    """精确高斯消元；返回 (是否相容, 解(自由变量取0), 秩)。"""
    M = [list(map(Fraction, r)) + [Fraction(b)] for r, b in zip(rows, rhs)]
    piv_cols = []
    r = 0
    ncol = nvar
    for c in range(ncol):
        p = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                p = i; break
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        pv = M[r][c]
        M[r] = [v / pv for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv_cols.append(c)
        r += 1
        if r == len(M):
            break
    for i in range(r, len(M)):
        if M[i][ncol] != 0:
            return False, None, r
    sol = [Fraction(0)] * nvar
    for i, c in enumerate(piv_cols):
        sol[c] = M[i][ncol]
    return True, sol, r


def try_ansatz(X, a, c, d, e, kfit, kchk, Smax, Pmax, qmin=1):
    vars_ = [(p, s) for s in range(Smax + 1) for p in range(Pmax + 1)]
    idx = {v: i for i, v in enumerate(vars_)}
    rows, rhs = [], []
    pts = [(k, q) for k in range(1, kfit + 1) for q in range(qmin, k + 1)]
    for (k, q) in pts:
        row = [0] * len(vars_)
        for (p, s) in vars_:
            row[idx[(p, s)]] = bin_(q + e, p) * bin_(k + a * s + p + c, s + q + d)
        rows.append(row); rhs.append(X[k][q])
    ok, sol, rk = solve(rows, rhs, len(vars_))
    if not ok:
        return False, None
    # 检验
    for k in range(1, kchk + 1):
        for q in range(qmin, k + 1):
            v = sum(sol[idx[(p, s)]] * bin_(q + e, p) * bin_(k + a * s + p + c, s + q + d) for (p, s) in vars_)
            if v != X[k][q]:
                return False, (k, q)
    return True, {vs: sol[idx[vs]] for vs in vars_ if sol[idx[vs]] != 0}


if __name__ == '__main__':
    K, Q = 24, 24
    N, Nc, NE = build_tables(K, Q)
    # 先确认 N^c 的已知公式能被这个程序找回（a=-2, c=-1, d=-1, e=0）
    ok, sol = try_ansatz(Nc, -2, -1, -1, 0, 14, 22, 7, 14)
    print('Nc known ansatz (a=-2,c=-1,d=-1,e=0):', ok, (sorted(sol.items())[:8] if isinstance(sol, dict) else sol))
    found = []
    for name, X in (('NE', NE), ('N', N)):
        for a in (-2, -1, 0, 1):
            for c in range(-4, 3):
                for d in range(-3, 3):
                    for e in range(-1, 2):
                        ok, sol = try_ansatz(X, a, c, d, e, 13, 20, 6, 13)
                        if ok:
                            found.append((name, a, c, d, e))
                            print('FOUND', name, a, c, d, e, sorted(sol.items())[:10], flush=True)
    print('done; found', len(found))
