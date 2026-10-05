# -*- coding: utf-8 -*-
"""探索 2：
(a) 一般原理：对任意右端 gamma(x,t)，Y = (1/A) L_s[Phi_A gamma(x, t e^{vs})] 满足 (A - t)Y - x^3 t Y_t = gamma；
    用若干随机整数 gamma、A = 1-x 与 A = 1-x+x^3 检查。
(b) 关键恒等式 (1-x-t)Psi - x^3 t dPsi/dt = (1-x)(Psi - dPsi/ds)（三元级数逐项）。
(c) 更大范围的 Laplace 展开 vs DP。
"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c3a_lib import *


def build_psi(gamma_cols, A, K, M):
    """返回 Psi_m 的 EGF（dict N->poly），Psi = Phi_A(s) * gamma(x, t e^{vs})。"""
    Ainv = sinv_int(pad(A, K), K)
    Nmax = K // 3 + M + 2
    Ainv_pow = [one(K)]
    for N in range(1, Nmax + 2):
        Ainv_pow.append(smul(Ainv_pow[-1], Ainv, K))
    E = {}
    for N in range(1, Nmax + 1):
        if 3 * N - 3 <= K:
            E[N] = [0] * (3 * N - 3) + Ainv_pow[N][:K + 1 - (3 * N - 3)]
    Pw = [{0: one(K)}]
    for n in range(1, M + 1):
        prod = egf_mul(E, Pw[-1], K, Nmax)
        Pw.append({N: [c // n for c in p] for N, p in prod.items()})
    Gam = []
    for m in range(M + 1):
        gm = pad(gamma_cols[m], K)
        d = {}
        if any(gm):
            for N in range(0, Nmax + 1):
                if 3 * N > K or (m == 0 and N > 0):
                    break
                base = [0] * (3 * N) + Ainv_pow[N][:K + 1 - 3 * N]
                d[N] = [(m ** N) * c for c in smul(base, gm, K)]
        Gam.append(d)
    Psi = []
    for m in range(M + 1):
        acc = {}
        for n in range(m + 1):
            for N, p in egf_mul(Pw[n], Gam[m - n], K, Nmax).items():
                acc[N] = sadd(acc[N], p) if N in acc else p
        Psi.append(acc)
    return Psi, Nmax


def check_operator_identity(gamma_cols, A, K, M):
    """(A - t)Psi - x^3 t Psi_t == A (Psi - Psi_s)，逐 (m, N) 比较。"""
    Psi, Nmax = build_psi(gamma_cols, A, K, M)
    Ap = pad(A, K)
    x3 = zero(K); x3[3] = 1
    for m in range(M + 1):
        for N in range(Nmax):
            P = Psi[m].get(N, zero(K))
            Pm1 = Psi[m - 1].get(N, zero(K)) if m >= 1 else zero(K)
            Pn1 = Psi[m].get(N + 1, zero(K))
            lhs = [a - b - m * c for a, b, c in zip(smul(Ap, P, K), Pm1, smul(x3, P, K))]
            rhs = smul(Ap, [a - b for a, b in zip(P, Pn1)], K)
            if lhs != rhs:
                return False, (m, N)
    return True, None


def apply_L(Y, Acoef, K, M):
    """(A - t)Y - x^3 t Y_t 的系数表（Y 为 Fraction/int 表）。"""
    out = [[0] * (M + 1) for _ in range(K + 1)]
    for k in range(K + 1):
        for m in range(M + 1):
            s = 0
            for i, a in enumerate(Acoef):
                if a and k - i >= 0:
                    s += a * Y[k - i][m]
            if m >= 1:
                s -= Y[k][m - 1]
            if k >= 3:
                s -= m * Y[k - 3][m]
            out[k][m] = s
    return out


random.seed(20261004)
t0 = time.time()
for A in ([1, -1], [1, -1, 0, 1]):
    for trial in range(3):
        K, M = 18, 9
        gcols = [[random.randint(-3, 3) for _ in range(K + 1)] for _ in range(M + 1)]
        gcols[0][0] = random.choice([1, -1, 2])
        Y = laplace_solve(gcols, A, K, M)
        LY = apply_L(Y, A, K, M)
        okL = all(LY[k][m] == gcols[m][k] for k in range(K + 1) for m in range(M + 1))
        okI, where = check_operator_identity(gcols, A, K, M)
        print('A=%s trial %d: L[Y]==gamma: %s ; operator identity: %s %s' % (A, trial, okL, okI, where or ''))
print('(a)(b) %.1fs' % (time.time() - t0))

# 对 F 本身的 Psi 检查算子恒等式
K, M = 30, 16
okI, where = check_operator_identity(gamma_F_cols(K, M), [1, -1], K, M)
print('operator identity for F-Psi (K=30,M=16):', okI, where or '')

T = U_fast_table(60, 30)
for (K, M) in [(45, 24), (60, 30)]:
    t1 = time.time()
    L = laplace_F(K, M)
    ok = all(L[k][m] == T[k][m] for k in range(K + 1) for m in range(M + 1))
    print('Laplace vs DP K=%d M=%d: %s  %.1fs' % (K, M, ok, time.time() - t1))
