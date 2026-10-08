# -*- coding: utf-8 -*-
"""B9 探索：h_k 次高项系数 h_{k,d-1} 的符号（c5a 定理 4.4(d) 的闭式），找 k=3a+1 时的翻转点。"""
import sys
from fractions import Fraction as Fr
from math import factorial
sys.path.insert(0, __file__.rsplit('explore', 1)[0] + 'explore')
from explore_b9_signs import h_table


def stirling1_table(n):
    c = [[0] * (n + 2) for _ in range(n + 2)]
    c[0][0] = 1
    for i in range(1, n + 1):
        for k in range(1, i + 1):
            c[i][k] = (i - 1) * c[i - 1][k] + c[i - 1][k - 1]
    return c


def second(k, c):
    a = k // 3
    if k % 3 == 0:
        return (-1) ** (a + 1) * 2 * a * factorial(a)
    if k % 3 == 1:
        return (-1) ** a * (c[a + 3][2] + c[a + 3][3] - factorial(a + 2) - (3 * a + 2) * c[a + 2][2])
    return (-1) ** a * (c[a + 3][2] + c[a + 3][3] - 3 * (a + 1) * factorial(a + 1))


if __name__ == '__main__':
    A = 400
    c = stirling1_table(A + 5)
    H = h_table(330)
    bad = 0
    for k in range(3, 331):
        d = len(H[k]) - 1
        if H[k][d - 1] != second(k, c):
            bad += 1
    print('closed form vs h_table (3<=k<=330) mismatches:', bad)
    # B1(a) 的符号随 a
    signs = []
    for a in range(1, A):
        v = c[a + 3][2] + c[a + 3][3] - factorial(a + 2) - (3 * a + 2) * c[a + 2][2]
        signs.append('+' if v > 0 else ('-' if v < 0 else '0'))
    s = ''.join(signs)
    print('sign B1(a), a=1..: first + at a =', s.index('+') + 1, ' last - at a =', s.rindex('-') + 1)
    print(s[:120])
    signs2 = ''.join('+' if (c[a + 3][2] + c[a + 3][3] - 3 * (a + 1) * factorial(a + 1)) > 0 else '-' for a in range(1, A))
    print('sign B2(a): all + ?', set(signs2))
    # 次高项与首项同号/异号
    for k in [255, 256, 257, 258, 259, 260, 261, 262, 300, 301, 302]:
        if k <= 330:
            d = len(H[k]) - 1
            print(k, k % 3, 'lead', '+' if H[k][d] > 0 else '-', 'second', '+' if H[k][d - 1] > 0 else '-')
