# -*- coding: utf-8 -*-
"""只读核对 01_summary 新句「基点 2d+1 的 Newton 正性在 d=69 首次失效」：
对 1<=d<=DMAX 计算 p_d 在基点 2d+1 的全部 Newton 系数 Δ^i p_d(2d+1)（i=0..2d），看 d<69 时是否有负值。
N 用三角递推（T1.4(2)，初值 N(0,0)=1,N(1,1)=1,N(2,1)=1,N(2,2)=2），先与 core.N_from_U 对照 k<=30。"""
import sys, time
from math import factorial
ROOT = r'C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数'
sys.path.insert(0, ROOT + r'\code')
DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 72
K = 4 * DMAX + 4
t0 = time.time()
N = [[0] * (K + 2) for _ in range(K + 1)]
N[0][0] = 1; N[1][1] = 1; N[2][1] = 1; N[2][2] = 2
for k in range(3, K + 1):
    for q in range(1, k + 1):
        r = q - 1
        v = N[k - 1][r] + N[k - 1][r + 1]
        if r >= 1:
            a = N[k - 3][r - 1] if r - 1 >= 0 else 0
            v += r * (a + 2 * N[k - 3][r] + N[k - 3][r + 1])
        N[k][q] = v
# 对照 core（容斥 N_from_U，T[k][m] 需要 m 到 q-1）
import core
U = core.U_fast_table(40, 41)
ok = all(core.N_from_U(U, k, q) == N[k][q] for k in range(0, 41) for q in range(0, k + 1))
print('triangle vs core.N_from_U (k<=40):', ok)
def D(k, d):
    q = k - d
    return N[k][q] if 0 <= q <= k else 0
neg_any = []
first_neg = None
for d in range(1, DMAX + 1):
    # T_i = Δ^i p_d(2d+2), from values D(2d+2+j, d), j=0..2d (polynomial region)
    vals = [D(2 * d + 2 + j, d) for j in range(2 * d + 1)]
    T = []
    cur = vals[:]
    for i in range(2 * d + 1):
        T.append(cur[0])
        cur = [cur[j + 1] - cur[j] for j in range(len(cur) - 1)]
    # N_i = Δ^i p_d(2d+1) = sum_{j>=i} (-1)^{j-i} T_j
    Nn = [sum((-1) ** (j - i) * T[j] for j in range(i, 2 * d + 1)) for i in range(2 * d + 1)]
    # 交叉核对 N_0 = D(2d+1,d) - (-1)^{d+1}(d+1)!
    assert Nn[0] == D(2 * d + 1, d) - (-1) ** (d + 1) * factorial(d + 1), d
    assert all(t > 0 for t in T), ('base 2d+2 not positive', d)
    negs = [i for i, v in enumerate(Nn) if v <= 0]
    if negs:
        neg_any.append((d, negs[:6], len(negs)))
        if first_neg is None:
            first_neg = d
print('DMAX', DMAX, 'first d with some nonpositive Newton coeff at base 2d+1:', first_neg)
for row in neg_any[:12]:
    print('  d=%d nonpositive indices (first few)=%s count=%d' % row)
print('elapsed %.1fs' % (time.time() - t0))
