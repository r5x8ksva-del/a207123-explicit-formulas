# -*- coding: utf-8 -*-
"""B8 大范围核对（探索版）：对 k<=K0，检查 U_k(-j)!=0 对一切 j>s_k。

用到三条（都在 notes/15 里证明）：
 (1) 根界：j > J_k := max_q [(q+1)N(k,q)/N(k,q+1) - q + 1] 时 (-1)^k U_k(-j) > 0；
 (2) 同余：p^e > k 且 p^e | j 时 U_k(-j) ≡ 1 (mod p)；所以只需检查 j | lcm(1..k)；
 (3) 剩下的 j 用 U_k(-j) = sum_q (-1)^q N(k,q) C(j+q-2,q) 模两个大素数求值，两个都为 0 再精确算。
"""
import sys
import time
import numpy as np
from math import comb

P1 = 2147483629   # < 2^31，素数
P2 = 2147483587


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b'\x00\x00'
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def N_table(K):
    N = [[0] * (K + 2) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1], N[2][2] = 1, 2
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            t = (N[k - 3][q - 2] if q >= 2 else 0) + 2 * N[k - 3][q - 1] + N[k - 3][q]
            N[k][q] = N[k - 1][q - 1] + N[k - 1][q] + (q - 1) * t
    return N


def root_bound(Nk, k):
    """J_k 的上取整：j > J 时 T_q 严格增。"""
    best = 0
    for q in range(1, k):
        # (q+1)N(k,q)/N(k,q+1) - q + 1，上取整
        num = (q + 1) * Nk[q]
        den = Nk[q + 1]
        v = -(-num // den) - q + 1
        best = max(best, v)
    return best


def smooth_divisors(k, J):
    """lcm(1..k) 的全部 <= J 的因子（即每个素数幂因子都 <= k 的 j）。"""
    ps = primes_upto(k)
    out = [1]
    for p in ps:
        pe = [1]
        while pe[-1] * p <= k:
            pe.append(pe[-1] * p)
        new = []
        for d in out:
            for f in pe:
                if d * f <= J:
                    new.append(d * f)
                else:
                    break
        out = new
    return sorted(out)


def eval_mod(Nk, k, js, P):
    """U_k(-j) mod P，向量化于 js（numpy int64）。"""
    j = np.array(js, dtype=np.int64) % P
    tot = np.zeros(len(js), dtype=np.int64)
    B = np.ones(len(js), dtype=np.int64)       # C(j+q-2, q)，q=0 时 1
    for q in range(1, k + 1):
        # C(j+q-2,q) = C(j+q-3,q-1)*(j+q-2)/q
        B = (B * ((j + (q - 2)) % P)) % P
        B = (B * pow(q, P - 2, P)) % P
        c = Nk[q] % P
        if q % 2:
            c = (P - c) % P
        tot = (tot + B * c) % P
    return tot


def exact(Nk, k, j):
    return sum((-1) ** q * Nk[q] * comb(j + q - 2, q) for q in range(1, k + 1))


def main(K0, K1=1):
    N = N_table(K0)
    t0 = time.time()
    total_c = 0
    found = []
    for k in range(max(K1, 1), K0 + 1):
        s = (k + 2) // 3
        J = root_bound(N[k], k) if k >= 2 else 1
        cand = [j for j in smooth_divisors(k, J) if j > s]
        total_c += len(cand)
        if cand:
            r1 = eval_mod(N[k], k, cand, P1)
            zero_idx = np.nonzero(r1 == 0)[0]
            if len(zero_idx):
                sub = [cand[i] for i in zero_idx]
                r2 = eval_mod(N[k], k, sub, P2)
                for jj, v in zip(sub, r2):
                    if v == 0:
                        ex = exact(N[k], k, jj)
                        print('  both residues 0 at k=%d j=%d, exact=%s' % (k, jj, ex))
                        if ex == 0:
                            found.append((k, jj))
        if k % 25 == 0 or k == K0:
            print('k=%d s_k=%d J_k=%d candidates=%d  (cum %d, %.1fs)' % (k, s, J, len(cand), total_c, time.time() - t0), flush=True)
    print('counterexamples:', found)


if __name__ == '__main__':
    K0 = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    K1 = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    main(K0, K1)
