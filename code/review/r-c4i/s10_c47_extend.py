# -*- coding: utf-8 -*-
"""s10：把 C4-7（门槛下 d+1<=k<=2d+1 全是例外）推到大 d。
用已证明的缺陷递推 (‡)（由三角递推与 p_d 的差分恒等式相减得到，适用于 k>=3、k-d>=1），
记 E[d][q] := e_d(d+q) = D(d+q,d) - p_d(d+q)，q>=0。由 (‡) 在 k=d+q（q>=1）：
  E[d][q-1] = E[d][q] - E[d-1][q] - (q-1)*(E[d-1][q-2] + 2E[d-2][q-1] + E[d-3][q])，
起点 E[d][q]=0（q>=d+2），E[d'][*]=0（d'<0）；d<=2 的 E 用直接值（D 与 p_d，来自 s2/表 2）。
先对 d<=35 与 s2 的独立结果（插值 p_d + 高度 DP）比对，再推到 d<=DM，检查 E[d][q]!=0 (1<=q<=d+1)，
并核对闭式 E[d][d+1]=(-1)^{d+1}(d+1)!、E[d][d]=(-1)^{d+1}(d+2)!/2。
用法：py -3.14 s10_c47_extend.py [DM] [K]
"""
import sys, os, time, pickle
from fractions import Fraction
from math import factorial
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rlib import interp, peval

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
DM = int(sys.argv[1]) if len(sys.argv) > 1 else 400
K = int(sys.argv[2]) if len(sys.argv) > 2 else 150
t0 = time.time()
E = {}
E[0] = {0: -1, 1: -1}          # e_0(0)=1-2, e_0(1)=1-2
E[1] = {0: 4, 1: 3, 2: 2}      # e_1(1)=0-(-4), e_1(2)=1-(-2), e_1(3)=4-2
E[2] = {0: -19, 1: -16, 2: -12, 3: -6}   # e_2(2..5)


def Ev(d, q):
    if d < 0 or q < 0:
        return 0
    return E[d].get(q, 0)


for d in range(3, DM + 1):
    row = {}
    for q in range(d + 1, -1, -1):
        # 计算 E[d][q]，用 (‡) 在 q+1 处
        Q = q + 1
        nxt = row.get(Q, 0)
        val = nxt - Ev(d - 1, Q) - (Q - 1) * (Ev(d - 1, Q - 2) + 2 * Ev(d - 2, Q - 1) + Ev(d - 3, Q))
        if val:
            row[q] = val
    E[d] = row

# 与 s2 的独立结果比对（d<=35）
with open(os.path.join(HERE, 'N_K%d.pkl' % K), 'rb') as fh:
    N = pickle.load(fh)['N']


def D(k, d):
    q = k - d
    if k < 0 or q < 0 or q > k:
        return 0
    return N[k][q]


dchk = (K - 8) // 4
okx = True
for d in range(0, dchk + 1):
    xs = list(range(2 * d + 2, 4 * d + 3))
    p = interp(xs, [D(k, d) for k in xs])
    for q in range(0, d + 3):
        if Ev(d, q) != D(d + q, d) - peval(p, d + q):
            okx = False
print(('OK  ' if okx else 'BAD ') + 'E 递推 == 独立插值 p_d 与高度 DP 的缺陷，d<=%d, 0<=q<=d+2' % dchk)
ok7 = True
zeros = []
okc = True
for d in range(1, DM + 1):
    for q in range(1, d + 2):
        if Ev(d, q) == 0:
            ok7 = False
            zeros.append((d, d + q))
    if Ev(d, d + 1) != (-1) ** (d + 1) * factorial(d + 1) or Fraction(Ev(d, d)) != Fraction((-1) ** (d + 1) * factorial(d + 2), 2):
        okc = False
print(('OK  ' if ok7 else 'BAD ') + 'C4-7：d+1<=k<=2d+1 全部 e_d(k)!=0，1<=d<=%d；零点：%s' % (DM, zeros[:10]))
print(('OK  ' if okc else 'BAD ') + '缺陷闭式（k=2d+1, 2d）对 d<=%d 成立' % DM)
print('runtime %.1fs' % (time.time() - t0))
