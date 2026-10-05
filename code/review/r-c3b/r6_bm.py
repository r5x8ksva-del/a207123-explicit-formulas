# -*- coding: utf-8 -*-
"""r-c3b 复核脚本 6：在例外 m=n^2(n-1)（b_m 在 Q 上可约）处，直接对高度 DP 数据做模 p 的 Berlekamp-Massey，
核对 k 方向线性复杂度恰为 3m+1（与闭式无关的旁证）。
严格性：U_.(m) 在 Q 上满足以 P_m（整系数、常数项 1）为特征多项式的递推，故模 p 线性复杂度 LC_p <= LC_Q <= 3m+1；
若 BM 给出 LC_p = 3m+1，则 LC_Q = 3m+1，即 gcd(W_m,P_m)=1（不发生约分）。连接多项式应为 P_m mod p。
数据：core.U_fast_column（高度 DP，r1 已在 40x40 上与参考实现逐项相等；它是第 1 节 (b) 定义的直接实现）。
"""
import sys, os, time
T0 = time.time()
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, os.path.join(ROOT, 'code'))
from core import U_fast_column

p = 1000000007


def bm(seq, p):
    C, B = [1], [1]
    L, m, b = 0, 1, 1
    for n in range(len(seq)):
        d = seq[n]
        for i in range(1, L + 1):
            d = (d + C[i] * seq[n - i]) % p
        if d == 0:
            m += 1
            continue
        coef = d * pow(b, -1, p) % p
        T = C[:]
        if len(C) < len(B) + m:
            C += [0] * (len(B) + m - len(C))
        for i in range(len(B)):
            C[i + m] = (C[i + m] - coef * B[i]) % p
        if 2 * L <= n:
            L, B, b, m = n + 1 - L, T, d, 1
        else:
            m += 1
    return L, C[:L + 1]


def Pm_modp(m, p):
    P = [1]
    for i in range(m + 1):
        b = [1, -1, 0, -i]
        r = [0] * (len(P) + 3)
        for a, x in enumerate(P):
            for c, y in enumerate(b):
                r[a + c] = (r[a + c] + x * y) % p
        P = r
    while P and P[-1] == 0:
        P.pop()
    return P


allok = True
for m in [1, 2, 3, 4, 5, 18, 48, 100]:
    L0 = 3 * m + 1
    col = U_fast_column(m, 2 * L0 + 20)
    L, C = bm([x % p for x in col], p)
    ok = (L == L0) and (C + [0] * (len(Pm_modp(m, p)) - len(C)) == Pm_modp(m, p))
    allok &= ok
    print('%s m=%d: BM mod p on U_0..U_%d(m): linear complexity %d (3m+1=%d), connection poly == P_m mod p: %s  (%.1fs)'
          % ('PASS' if ok else 'FAIL', m, 2 * L0 + 20, L, L0, C == Pm_modp(m, p)[:len(C)], time.time() - T0))
print('OVERALL', 'PASS' if allok else 'FAIL')
