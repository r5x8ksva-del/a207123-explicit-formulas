# -*- coding: utf-8 -*-
"""c5b 探索脚本：用 core 的高度 DP（原始定义 (b) 的直接实现）算出所有要拿去 OEIS 搜索的片段。
只用整数 / Fraction。输出写到 stdout（由调用者重定向到 logs/c5b_terms.log）。"""
import os
import sys
import json

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.dirname(HERE)
sys.path.insert(0, CODE)
from core import U_fast_table, N_from_U, binom, U_multichain, a_direct, PROMPT_TABLE  # noqa: E402
from polylib import P_poly, series_mul, trim  # noqa: E402

K, M = 40, 40
T = U_fast_table(K, M)

# 小范围对照多重链定义（独立方法）
for k in range(1, 8):
    for m in range(0, 5):
        assert U_multichain(k, m) == T[k][m], (k, m)
for k, row in PROMPT_TABLE.items():
    assert T[k][:7] == row

out = {}


def show(name, seq):
    out[name] = seq
    print(name, ':', ','.join(str(v) for v in seq))


# U_k(m) 作为 m 的函数（k 固定）
for k in range(1, 11):
    show('U_%d(m),m=0..20' % k, [T[k][m] for m in range(21)])

# U_k(m) 作为 k 的函数（m 固定）
for m in range(1, 7):
    show('U_k(%d),k=0..25' % m, [T[k][m] for k in range(26)])

# 对角线 U_k(k)
show('U_k(k),k=0..20', [T[k][k] for k in range(21)])

# N 三角形
NN = {k: [N_from_U(T, k, q) for q in range(0, k + 1)] for k in range(0, 21)}
flat = []
flat_rev = []
for k in range(1, 12):
    row = NN[k][1:]
    flat += row
    flat_rev += row[::-1]
show('N_flat_rows_q=1..k,k=1..11', flat)
show('N_flat_rows_reversed,k=1..11', flat_rev)
show('N_rowsum,k=0..20', [sum(NN[k]) for k in range(21)])
show('N(k,k-1),k=2..20', [NN[k][k - 1] for k in range(2, 21)])
show('N(k,k-2),k=3..20', [NN[k][k - 2] for k in range(3, 21)])
show('N(k,k-3),k=4..20', [NN[k][k - 3] for k in range(4, 21)])
show('N(k,2),k=2..20', [NN[k][2] for k in range(2, 21)])
show('N(k,3),k=3..20', [NN[k][3] for k in range(3, 21)])

# h_k(t) = (1-t)^{k+1} * sum_m U_k(m) t^m（截断到 M 项，检查 deg>k 的系数为 0）
H = {}
for k in range(0, 13):
    ser = [T[k][m] for m in range(M + 1)]
    fac = [1]
    for _ in range(k + 1):
        fac = series_mul(fac, [1, -1], M + 1)
    prod = series_mul(ser, fac, M + 1)
    assert all(c == 0 for c in prod[k + 1:M + 1 - (k + 1)]), k   # 截断边缘之前全为 0
    H[k] = trim(prod[:k + 1])
    print('h_%d =' % k, H[k])
hflat = []
for k in range(0, 9):
    hflat += H[k]
show('h_flat,k=0..8', hflat)

# (C7) 分子：P_{q-1}(x) * sum_k N(k,q) x^k
NUM = {}
for q in range(1, 9):
    ser = [N_from_U(T, k, q) for k in range(K + 1)]
    prod = series_mul(ser, P_poly(q - 1), K + 1)
    assert all(c == 0 for c in prod[3 * q - 1:K + 1]), q
    NUM[q] = trim(prod)
    print('Num_%d =' % q, NUM[q])
numflat = []
for q in range(1, 7):
    numflat += NUM[q][q:3 * q - 1]
show('Num_flat_x^q..x^(3q-2),q=1..6', numflat)

# c_i(n) = [x^n] 1/(1-x-i x^3)
for i in range(1, 5):
    c = []
    for n in range(30):
        v = (c[n - 1] if n >= 1 else 1) if n >= 1 else 1
        if n == 0:
            v = 1
        else:
            v = c[n - 1] + (i * c[n - 3] if n >= 3 else 0)
        c.append(v)
    show('c_%d(n),n=0..29' % i, c)

# a_k(n)：原题定义直接数（小范围）与 U 乘积
for k in range(1, 8):
    seq = [T[k][(n + 1) // 2] * T[k][n // 2] for n in range(1, 31)]
    show('a_%d(n),n=1..30' % k, seq)
    for n in range(1, 10 if k <= 5 else 7):
        assert a_direct(n, k) == seq[n - 1], (k, n)

with open(os.path.join(HERE, 'terms.json'), 'w', encoding='utf-8') as f:
    json.dump(out, f, ensure_ascii=False, indent=0)
print('OK')
