# -*- coding: utf-8 -*-
"""T5.3(1)(4)(6)：n_k(z)=(1+z)^{k-1}h_k(z/(1+z))、z=-1 的重数 ceil(k/3)-1、N(k,.) 对数凹（final-audit math-c4c5）。"""
from fractions import Fraction
from math import comb
from alib import say, check, N_tri, ptrim, padd, pmul, pscale, peval, pdivmod, write_log

NT = N_tri(80)
ok1 = ok2 = ok3 = True
for k in range(1, 61):
    nk = ptrim([NT[k][q] for q in range(1, k + 1)])          # Σ_q N(k,q) z^{q-1}
    # h_k(t) = Σ_q N(k,q) t^{q-1}(1-t)^{k-q}
    hk = []
    for q in range(1, k + 1):
        term = [0] * (q - 1) + [1]
        for _ in range(k - q):
            term = pmul(term, [1, -1])
        hk = padd(hk, pscale(term, NT[k][q]))
    # (1+z)^{k-1} h_k(z/(1+z)) = Σ_i h_i z^i (1+z)^{k-1-i}
    rhs = []
    for i, hi in enumerate(hk):
        term = [0] * i + [1]
        for _ in range(k - 1 - i):
            term = pmul(term, [1, 1])
        rhs = padd(rhs, pscale(term, hi))
    if k <= 30 and ptrim(rhs) != nk:
        ok1 = False
    # z=-1 的重数
    mult, p = 0, nk
    while p and peval(p, -1) == 0:
        p, r = pdivmod(p, [1, 1])
        assert not r
        mult += 1
    if mult != -(-k // 3) - 1:
        ok2 = False
    # 对数凹
    row = [NT[k][q] for q in range(1, k + 1)]
    if any(row[i] * row[i] < row[i - 1] * row[i + 1] for i in range(1, len(row) - 1)):
        ok3 = False
check('T5.3-nk', ok1 and ok2 and ok3, 'n_k(z)=(1+z)^{k-1}h_k(z/(1+z))（k<=30）；z=-1 为 n_k 的 ceil(k/3)-1 重根（1<=k<=60）；N(k,.) 对数凹（k<=60）')
write_log('final_audit_math-c4c5_s10.log')
