# -*- coding: utf-8 -*-
"""探索 5：计算比较 —— 算全部 U_k(m)（0<=k<=K, 0<=m<=M），各方法实测耗时，并互相核对 + 对照定义 DP。"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c2a_lib import *  # noqa
from core import U_fast_table
from polylib import P_poly, series_inv, series_mul, pmul, padd, pshift, pscale

K = int(sys.argv[1]) if len(sys.argv) > 1 else 200
M = int(sys.argv[2]) if len(sys.argv) > 2 else 30
res = {}
tim = {}


def run(name, fn):
    t0 = time.perf_counter()
    T = fn()
    tim[name] = time.perf_counter() - t0
    res[name] = T


def tab(f):
    return [[f(k, m) for m in range(M + 1)] for k in range(K + 1)]


B = None


def bt(a, b):
    if b < 0 or a < 0 or b > a:
        return 0
    return B[a][b]


# --- 递推类
run('DP(core.U_fast_table, definition)', lambda: U_fast_table(K, M))
run('Lemma1 recurrence', lambda: U_rec_table(K, M))


def linrec():
    T = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        P = P_poly(m)
        W = [1]
        for j in range(1, m + 1):
            W = padd(W, pshift(pscale(P_poly(j - 1), j), 2))
        n0 = min(K + 1, 3 * m + 1)
        init = series_mul(W, series_inv(P, n0), n0)
        col = [int(v) for v in init]
        L = len(P) - 1
        for k in range(n0, K + 1):
            col.append(-sum(P[l] * col[k - l] for l in range(1, L + 1)))
        for k in range(K + 1):
            T[k][m] = col[k]
    return T


run('fixed-m linear recurrence (order 3m+1)', linrec)


def ntri():
    global B
    N = N_triangle(K)
    BB = binom_table(K + M + 5)
    return [[sum(N[k][q] * BB[m + 1][q] for q in range(0, min(k, m + 1) + 1)) for m in range(M + 1)] for k in range(K + 1)]


run('N triangle + sum_q N C(m+1,q)', ntri)

# --- 显式公式类（原子数表预计算计入耗时）
def H_form():
    global B
    B = binom_table(K + M + 5)
    S = K // 3 + 2
    H = hgrid(M, S)
    T = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        Hm = H[m]
        for k in range(K + 1):
            row0 = Hm[0]
            tot = 0
            for s in range(k // 3 + 1):
                tot += row0[s] * bt(k + m - 2 * s, m + s)
            n = k - 2
            if n >= 0:
                for j in range(1, m + 1):
                    row = Hm[j]
                    sub = 0
                    for s in range(n // 3 + 1):
                        sub += row[s] * bt(n + m - j - 2 * s, m - j + s)
                    tot += j * sub
            T[k][m] = tot
    return T


run('H form (r-Stirling atoms by recurrence)', H_form)


def H_form_explicit_atoms():
    """同 H 型，但 r-Stirling 原子用显式交错式 rstirling_explicit 计算（完全显式）。"""
    global B
    B = binom_table(K + M + 5)
    S = K // 3 + 2
    T = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        Hm = [[rstirling_explicit(m + s, m, j) for s in range(S + 1)] for j in range(m + 1)]
        for k in range(K + 1):
            tot = sum(Hm[0][s] * bt(k + m - 2 * s, m + s) for s in range(k // 3 + 1))
            n = k - 2
            if n >= 0:
                for j in range(1, m + 1):
                    tot += j * sum(Hm[j][s] * bt(n + m - j - 2 * s, m - j + s) for s in range(n // 3 + 1))
            T[k][m] = tot
    return T


run('H form (r-Stirling atoms by explicit alternating sum)', H_form_explicit_atoms)


def F3_form():
    global B
    B = binom_table(K + M + 5)
    H = hgrid(M, K // 3 + 2)
    T = [[0] * (M + 1) for _ in range(K + 1)]
    for m in range(M + 1):
        Hm = H[m]
        for k in range(K + 1):
            tot = sum(Hm[0][s] * bt(k + 1 + m - 2 * s, m + s) for s in range((k + 1) // 3 + 1))
            for j in range(1, m + 1):
                row = Hm[j]
                tot -= sum(row[s] * bt(k + m - j - 2 * s, m - j + s) for s in range(k // 3 + 1))
            T[k][m] = tot
    return T


run('F3 form', F3_form)


def theta_form():
    C = ctable(M, K + 3 * M + 4)
    return tab(lambda k, m: U_Theta(k, m, C))


run('Theta form (prompt C4; c_i atoms explicit)', theta_form)


def thetaH_form():
    C = ctable(M, K + 3 * M + 4)
    return tab(lambda k, m: U_ThetaH(k, m, C))


run('H-outer + c_i inner', thetaH_form)


def F4_form():
    C = ctable(M, K + 3 * M + 4)
    return tab(lambda k, m: U_F4(k, m, C))


run('F4 c_i partial fractions', F4_form)


def gamma_rec():
    """Gamma_m(n;j) 三角递推：Gamma_m(n;j) = Gamma_{m-1}(n;j) + Gamma_m(n-1;j) + m Gamma_m(n-3;j)，Gamma_{j-1}(n;j)=[n=0]。"""
    T = [[0] * (M + 1) for _ in range(K + 1)]
    # G[j] = 当前 m 的 [Gamma_m(n;j)]_n
    G = {}
    for m in range(M + 1):
        G[m] = [1] + [0] * K          # Gamma_{m-1}(n; m) = [n=0]，下面再乘 1/b_m
        for j in range(m + 1):
            old = G[j]
            new = [0] * (K + 1)
            for n in range(K + 1):
                new[n] = old[n] + (new[n - 1] if n >= 1 else 0) + (m * new[n - 3] if n >= 3 else 0)
            G[j] = new
        for k in range(K + 1):
            tot = G[0][k]
            if k >= 2:
                tot += sum(j * G[j][k - 2] for j in range(1, m + 1))
            T[k][m] = tot
    return T


run('Gamma (cubic-Stirling) triangle recurrence + single j-sum', gamma_rec)

ref = res['DP(core.U_fast_table, definition)']
print('K=%d, M=%d (all U_k(m), 0<=k<=K, 0<=m<=M)' % (K, M))
for name in res:
    print('  %-55s %8.3fs   equal_to_DP=%s' % (name, tim[name], res[name] == ref))
