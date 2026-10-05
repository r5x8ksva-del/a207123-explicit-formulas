# -*- coding: utf-8 -*-
"""r-c2a 复核脚本 6：c2a 失败方向里可核对的小断言。
  - §6.4：(1-x)^{-1} = 1 + u + x + x^2；m=4 的三族系数 G_4 = (a + b x + c x^2)/prod_{i=1}^4 (1 - i u)
    其中 a = 1+55u+64u^2+102u^3-6u^4+u^5, b = 5+50u+29u^2+16u^3+u^4, c = 25+42u+87u^2-7u^3+u^4；
  - §6.7：以 b_m 为中心的展开 Q_j = sum_t (-1)^t S(m-j+t, m-j) x^{3t} b_m^{-(m-j+1+t)}（m<=8 截断级数核对）。
全部用整数截断幂级数，对照自写 DP。
"""
from math import comb

N = 61


def smul(a, b):
    r = [0] * N
    for i, x in enumerate(a[:N]):
        if x:
            for j in range(0, N - i):
                if j < len(b):
                    r[i + j] += x * b[j]
    return r


def sinv(a):
    r = [0] * N
    assert a[0] in (1, -1)
    r[0] = a[0]
    for n in range(1, N):
        s = sum(a[i] * r[n - i] for i in range(1, min(n, len(a) - 1) + 1))
        r[n] = -s * a[0]
    return r


def spow(a, e):
    r = [1] + [0] * (N - 1)
    for _ in range(e):
        r = smul(r, a)
    return r


def U_col(m, K):
    out = [1, m + 1]
    n = m + 1
    cnt = [[1] * n for _ in range(n)]
    out.append(n * n)
    for _ in range(3, K + 1):
        new = [[0] * n for _ in range(n)]
        for b in range(n):
            suf = [0] * (n + 1)
            for a in range(n - 1, -1, -1):
                suf[a] = suf[a + 1] + cnt[a][b]
            for c in range(n):
                new[b][c] = suf[0] if b == c else suf[max(b, c)]
        cnt = new
        out.append(sum(map(sum, cnt)))
    return out


one_minus_x = [1, -1] + [0] * (N - 2)
inv1mx = sinv(one_minus_x)
u = smul([0, 0, 0, 1] + [0] * (N - 4), inv1mx)          # x^3/(1-x)
x = [0, 1] + [0] * (N - 2)
x2 = smul(x, x)
lhs = inv1mx
rhs = [(1 if i == 0 else 0) + u[i] + x[i] + x2[i] for i in range(N)]
print('(1-x)^{-1} == 1 + u + x + x^2 :', lhs == rhs)


def poly_u(coeffs):
    r = [0] * N
    up = [1] + [0] * (N - 1)
    for c in coeffs:
        r = [r[i] + c * up[i] for i in range(N)]
        up = smul(up, u)
    return r


a = poly_u([1, 55, 64, 102, -6, 1])
b = poly_u([5, 50, 29, 16, 1])
c = poly_u([25, 42, 87, -7, 1])
D = [1] + [0] * (N - 1)
for i in range(1, 5):
    D = smul(D, [(1 if k == 0 else 0) - i * u[k] for k in range(N)])
num = [a[k] for k in range(N)]
bx = smul(b, x)
cx2 = smul(c, x2)
num = [num[k] + bx[k] + cx2[k] for k in range(N)]
G = smul(num, sinv(D))
print('m=4 three-family coefficients reproduce G_4 up to x^60 :', G == U_col(4, N - 1))

# §6.7 以 b_m 为中心展开
S = [[0] * 40 for _ in range(40)]
S[0][0] = 1
for n in range(1, 40):
    for k in range(1, n + 1):
        S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
ok = True
for m in range(0, 9):
    bm = [1, -1, 0, -m] + [0] * (N - 4)
    ibm = sinv(bm)
    for j in range(0, m + 1):
        Q = [1] + [0] * (N - 1)
        for v in range(j, m + 1):
            Q = smul(Q, sinv([1, -1, 0, -v] + [0] * (N - 4)))
        M = m - j
        tot = [0] * N
        for t in range(0, N // 3 + 1):
            term = smul([0] * (3 * t) + [1] + [0] * N, spow(ibm, M + 1 + t))
            term = [(-1) ** t * S[M + t][M] * term[k] for k in range(N)]
            tot = [tot[k] + term[k] for k in range(N)]
        ok = ok and tot == Q
print('Q_j = sum_t (-1)^t S(m-j+t,m-j) x^{3t} b_m^{-(m-j+1+t)} (m<=8, up to x^60) :', ok)
