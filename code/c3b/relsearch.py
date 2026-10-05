# -*- coding: utf-8 -*-
"""c3b 的线性代数工具：在 U / N 表上搜索带多项式系数的线性递推。

  关系形如  sum_{0<=a<=A, 0<=b<=B} p_ab(k, m) * X(k-a, m-b) = 0   对所有 k0<=k<=K, m0<=m<=M,
  其中 p_ab 属于给定的单项式空间（只含 k 的幂，或 k^i m^j 总次数 <= D）。

秩用大素数 p (< 2^31) 上的 Gauss 消元（numpy int64，乘积 < 2^62，不溢出，全是精确整数运算）。
  - 模 p 列满秩  ==>  有理数域上列满秩  ==>  该参数下没有任何非零关系（严格结论）。
  - 有理核维数 <= 模 p 核维数；若再给出同样多个线性无关的精确有理关系，则两者相等。
"""
import numpy as np
from fractions import Fraction as Fr

PRIMES = [2147483647, 2147483629, 2147483587, 2147483579]


def is_prime(n):
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


assert all(is_prime(p) and p < 2 ** 31 for p in PRIMES)


def monos_konly(D):
    return [(i, 0) for i in range(D + 1)]


def monos_total(D):
    return [(i, j) for i in range(D + 1) for j in range(D + 1 - i)]


def monos_sep(Dk, Dm):
    return [(i, j) for i in range(Dk + 1) for j in range(Dm + 1)]


def unknowns(A, B, monos):
    return [(a, b, i, j) for a in range(A + 1) for b in range(B + 1) for (i, j) in monos]


def build_rows_mod(tab, unk, k0, K, m0, M, p):
    """返回 numpy int64 矩阵（模 p）：行 = (k,m)，列 = unknown (a,b,i,j)。"""
    rows = []
    tabp = {}
    for k in range(0, K + 1):
        for m in range(0, M + 1):
            tabp[(k, m)] = tab[k][m] % p
    emax = 1 + max(max(i, j) for (_, _, i, j) in unk)
    for k in range(k0, K + 1):
        kp = [pow(k, e, p) for e in range(emax)]
        for m in range(m0, M + 1):
            mp = [pow(m, e, p) for e in range(emax)]
            rows.append([tabp[(k - a, m - b)] * kp[i] % p * mp[j] % p for (a, b, i, j) in unk])
    return np.array(rows, dtype=np.int64)


def rref_mod(Ain, p, want_rref=False):
    """模 p 行化简。返回 (rank, pivot_cols, R)；want_rref=True 时 R 为约化行阶梯形（前 rank 行）。"""
    A = Ain.copy() % p
    nr, nc = A.shape
    r = 0
    piv = []
    for c in range(nc):
        if r == nr:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        i = r + int(nz[0])
        if i != r:
            A[[r, i]] = A[[i, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r, c:] = (A[r, c:] * inv) % p
        if want_rref:
            col = A[:, c].copy()
            col[r] = 0
        else:
            col = np.zeros(nr, dtype=np.int64)
            col[r + 1:] = A[r + 1:, c]
        idx = np.nonzero(col)[0]
        if len(idx):
            upd = (A[idx, c:] - (col[idx, None] * A[r, c:][None, :]) % p) % p
            A[idx, c:] = upd
        piv.append(c)
        r += 1
    return r, piv, A[:r]


def kernel_mod(Ain, p):
    """模 p 核的 RREF 基（每个基向量在一个自由列上为 1，其余自由列为 0）。"""
    r, piv, R = rref_mod(Ain, p, want_rref=True)
    nc = Ain.shape[1]
    free = [c for c in range(nc) if c not in set(piv)]
    basis = []
    for f in free:
        v = [0] * nc
        v[f] = 1
        for row, c in enumerate(piv):
            v[c] = (-int(R[row, f])) % p
        basis.append(v)
    return r, piv, free, basis


def ratrec(a, m):
    """有理重构：找 n/d ≡ a (mod m)，|n|,|d| <= sqrt(m/2)。失败返回 None。"""
    a %= m
    bound = int((m // 2) ** 0.5)
    r0, r1 = m, a
    s0, s1 = 0, 1
    while r1 > bound:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound:
        return None
    return Fr(r1, s1) if s1 > 0 else Fr(-r1, -s1)


def crt(residues, moduli):
    x, M = 0, 1
    for r, m in zip(residues, moduli):
        # x ≡ r (mod m)
        t = ((r - x) * pow(M, -1, m)) % m
        x += M * t
        M *= m
    return x % M, M


def exact_check(tab, unk, coeffs, k0, K, m0, M):
    """精确整数核对：sum_u coeffs[u] * k^i m^j * tab[k-a][m-b] == 0 对整个象限。coeffs 为 Fraction/int。"""
    for k in range(k0, K + 1):
        for m in range(m0, M + 1):
            s = 0
            for c, (a, b, i, j) in zip(coeffs, unk):
                if c:
                    s += c * (k ** i) * (m ** j) * tab[k - a][m - b]
            if s != 0:
                return False
    return True


def operator_to_vector(op_terms, unk):
    """op_terms: dict (a,b,i,j)->coef（系数多项式按单项式展开）。返回与 unk 对齐的列表；若有项不在 unk 里抛错。"""
    idx = {u: t for t, u in enumerate(unk)}
    v = [0] * len(unk)
    for key, c in op_terms.items():
        if c == 0:
            continue
        if key not in idx:
            raise KeyError(key)
        v[idx[key]] += c
    return v


def poly_times_mono(poly, i, j):
    """poly: dict (i,j)->c 表示 sum c k^i m^j；乘 k^i m^j。"""
    return {(a + i, b + j): c for (a, b), c in poly.items()}


def left_multiple(gen, alpha, beta, i, j, second_var_shift=True):
    """k^i m^j S_k^{-alpha} S_m^{-beta} * gen，gen: dict (a,b)->poly(dict (ii,jj)->c)，系数多项式里的 m 被移位 m->m-beta。
    返回 dict (a,b,ii,jj)->c。"""
    out = {}
    for (a, b), poly in gen.items():
        # S^{(alpha,beta)} c(k,m) = c(k-alpha, m-beta) S^{(alpha,beta)}
        shifted = {}
        for (ii, jj), c in poly.items():
            # c * (k-alpha)^ii (m-beta)^jj 展开
            from math import comb
            for s in range(ii + 1):
                for t in range(jj + 1):
                    coef = c * comb(ii, s) * ((-alpha) ** (ii - s)) * comb(jj, t) * ((-beta) ** (jj - t))
                    if coef:
                        shifted[(s, t)] = shifted.get((s, t), 0) + coef
        for (s, t), c in shifted.items():
            key = (a + alpha, b + beta, s + i, t + j)
            out[key] = out.get(key, 0) + c
    return {k: v for k, v in out.items() if v != 0}


# 引理 1 的算子 L1 = 1 - S_m^{-1} - S_k^{-1} - m S_k^{-3}
L1 = {(0, 0): {(0, 0): 1}, (0, 1): {(0, 0): -1}, (1, 0): {(0, 0): -1}, (3, 0): {(0, 1): -1}}
# N 的三角递推算子 L_N = 1 - S_k^{-1} - S_k^{-1}S_q^{-1} - (q-1) S_k^{-3} (1 + 2 S_q^{-1} + S_q^{-2})
LN = {(0, 0): {(0, 0): 1}, (1, 0): {(0, 0): -1}, (1, 1): {(0, 0): -1},
      (3, 0): {(0, 1): -1, (0, 0): 1}, (3, 1): {(0, 1): -2, (0, 0): 2}, (3, 2): {(0, 1): -1, (0, 0): 1}}


def gen_multiples(gen, gen_box, A, B, monos_D, Dtot=None, Dk=None, Dm=None):
    """所有 k^i m^j S^{(alpha,beta)} gen 中支撑落在 [0..A]x[0..B] 且系数次数满足约束的乘子。"""
    ga, gb = gen_box
    res = []
    for alpha in range(0, A - ga + 1):
        for beta in range(0, B - gb + 1):
            for (i, j) in monos_D:
                op = left_multiple(gen, alpha, beta, i, j)
                ok = True
                for (a, b, ii, jj) in op:
                    if a > A or b > B:
                        ok = False
                    if Dtot is not None and ii + jj > Dtot:
                        ok = False
                    if Dk is not None and ii > Dk:
                        ok = False
                    if Dm is not None and jj > Dm:
                        ok = False
                if ok:
                    res.append(op)
    return res
