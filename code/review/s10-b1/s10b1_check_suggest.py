# -*- coding: utf-8 -*-
"""s10-b1 核对 5：审查报告里建议的「不用 G_{−j} 与互反引理」的自足论证的数值核对。

记 n_k = (1+z)^{a_k} m_k，m_k(−1) ≠ 0，λ_k := m_k(−1)。由引理 0（k≥4）
  n_k = (1+z)(n_{k−1} + T n_{k−3})，T((1+z)^a m) = z(1+z)^a[(a+2)m + (1+z)m']，
得：k≢1 (mod 3) 时（a_{k−1} = a_{k−3}+1）a_k = a_{k−3}+1，λ_k = −(a_{k−3}+2)λ_{k−3}；
    k≡1 (mod 3) 时（a_{k−1} = a_{k−3}）λ_{k−1} 与 −(a_{k−3}+2)λ_{k−3} 同号，不会相消，
    a_k = a_{k−1}+1，λ_k = λ_{k−1} − (a_{k−1}+2)λ_{k−3}。
于是 a_k = ⌈k/3⌉−1、sign λ_k 的周期模式、lc(h_k) = (−1)^{deg h_k} λ_k、sign lc(h_k) = (−1)^{⌊k/3⌋}。
这里逐条精确核对（k≤150）。
"""
import os
import sys
import time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from s10b1_poly import mult_at, ev_int, deg, mul, add, scal, T, mul1z, deriv, mulz
from s10b1_data import N_tri, nrow

K = 150
t0 = time.time()
N = N_tri(K)
PASS = 0
FAIL = 0


def check(name, ok, detail=''):
    global PASS, FAIL
    if ok:
        PASS += 1
    else:
        FAIL += 1
        print('FAIL', name, detail, flush=True)


a = {}
lam = {}
core = {}
for k in range(1, K + 1):
    a[k], core[k] = mult_at(nrow(N, k), -1)
    lam[k] = ev_int(core[k], -1)
    check('lambda_k != 0 k=%d' % k, lam[k] != 0)
    check('a_k = ceil(k/3)-1 k=%d' % k, a[k] == -(-k // 3) - 1)
check('base a_1..a_3 = 0, lambda = 1,-1,-1', [a[1], a[2], a[3]] == [0, 0, 0] and [lam[1], lam[2], lam[3]] == [1, -1, -1])

# 关键恒等式：T((1+z)^e m) = z(1+z)^e[(e+2)m + (1+z)m']
for k in range(1, 60):
    e, m = a[k], core[k]
    lhs = T(nrow(N, k))
    br = add(scal(e + 2, m), mul1z(deriv(m)))
    pw = [1]
    for _ in range(e):
        pw = mul1z(pw)
    check('T((1+z)^a m) identity k=%d' % k, lhs == mulz(mul(pw, br)))

for k in range(4, K + 1):
    if k % 3 != 1:
        check('a_{k-1} = a_{k-3}+1 (k!=1 mod 3) k=%d' % k, a[k - 1] == a[k - 3] + 1)
        check('a_k = a_{k-3}+1 k=%d' % k, a[k] == a[k - 3] + 1)
        check('lambda_k = -(a_{k-3}+2) lambda_{k-3} k=%d' % k, lam[k] == -(a[k - 3] + 2) * lam[k - 3])
    else:
        check('a_{k-1} = a_{k-3} (k=1 mod 3) k=%d' % k, a[k - 1] == a[k - 3])
        x, y = lam[k - 1], -(a[k - 3] + 2) * lam[k - 3]
        check('no cancellation: same sign k=%d' % k, (x > 0) == (y > 0))
        check('a_k = a_{k-1}+1 k=%d' % k, a[k] == a[k - 1] + 1)
        check('lambda_k = lambda_{k-1} - (a+2) lambda_{k-3} k=%d' % k, lam[k] == x + y)
for k in range(1, K + 1):
    b = k // 3
    expect = (-1) ** (b + (1 if k % 3 == 2 else 0))
    check('sign lambda_k pattern k=%d' % k, (lam[k] > 0) == (expect > 0))

# lc(h_k) = (−1)^{deg h_k} λ_k，deg h_k = k−1−a_k = ⌊2k/3⌋，符号 (−1)^{⌊k/3⌋}
def powpoly(p, e):
    r = [1]
    for _ in range(e):
        r = mul(r, p)
    return r


for k in range(1, 81):
    h = []
    for q in range(1, k + 1):
        h = add(h, scal(N[k][q], mul([0] * (q - 1) + [1], powpoly([1, -1], k - q))))
    check('deg h_k = k-1-a_k k=%d' % k, deg(h) == k - 1 - a[k] == (2 * k) // 3)
    check('lc h_k = (-1)^deg * lambda_k k=%d' % k, h[-1] == (-1) ** deg(h) * lam[k])
    check('sign lc h_k = (-1)^floor(k/3) k=%d' % k, (h[-1] > 0) == ((k // 3) % 2 == 0))
print('lambda_k for k=1..15:', [lam[k] for k in range(1, 16)])
print('elapsed %.1fs' % (time.time() - t0))
print('TOTAL PASS=%d FAIL=%d' % (PASS, FAIL))
