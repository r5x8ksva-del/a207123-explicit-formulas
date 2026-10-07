# -*- coding: utf-8 -*-
"""s10-b1 核对 1：N 的独立计算与笔记 05 的引理 0（n_k = (1+z) n_{k−1} + Φ n_{k−3}，k≥4）。

N 的来源：
  (i)  N_brute：按定义 DFS 枚举 good 词（k≤9）；
  (ii) N_from_U：U 由按定义的转移 DP 算出（k≤60，m≤59），再用容斥（论文 Prop. 2.6）；
  (iii) N_tri：论文 Prop. 2.7 的三角递推（只拿来和 (ii) 对照）。
引理 0 只用 (ii) 的 N 核对。另做反向检查：把 Φ 里的 2zn 改成 3zn、或把某个 N 改动 1，核对应当报 FAIL。
"""
import sys
import time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from s10b1_poly import add, mul, mulz, mul1z, deriv, scal, T, Phi, norm, ev_int
from s10b1_data import U_brute, U_dp, N_brute, N_table_from_U, N_tri, nrow

t0 = time.time()
PASS = 0
FAIL = 0


def check(name, ok, detail=''):
    global PASS, FAIL
    if ok:
        PASS += 1
    else:
        FAIL += 1
        print('FAIL', name, detail)
    return ok


K = 60
U = U_dp(K, K)          # U[k][m], m ≤ 60
print('U_dp done %.1fs' % (time.time() - t0))

# --- U：DP 与暴力枚举、与论文表 1 对照
for k in range(0, 8):
    for m in range(0, 5):
        if k * m <= 24 or k <= 6:
            check('U_brute k=%d m=%d' % (k, m), U[k][m] == U_brute(k, m))
paper_tab = {0: [1, 1, 1, 1, 1, 1], 1: [1, 2, 3, 4, 5, 6], 2: [1, 4, 9, 16, 25, 36], 3: [1, 6, 17, 36, 65, 106],
             4: [1, 9, 32, 80, 165, 301], 5: [1, 14, 64, 192, 457, 938], 6: [1, 21, 119, 419, 1136, 2604],
             7: [1, 31, 214, 873, 2669, 6778], 8: [1, 46, 388, 1837, 6334, 17802]}
for k, row in paper_tab.items():
    check('paper Table 1 k=%d' % k, [U[k][m] for m in range(6)] == row)
# 论文里的四项递推（Lemma 2.5）也顺手对照，k≥1、m≥0，约定 U_0≡1, U_{−1}≡1, U_{−2}≡0, U_k(−1)=0
def Uc(k, m):
    if k == -1:
        return 1
    if k == -2:
        return 0
    if m == -1:
        return 1 if k == 0 else 0
    return U[k][m]
bad = 0
for k in range(1, K + 1):
    for m in range(0, K + 1):
        if Uc(k, m) != Uc(k, m - 1) + Uc(k - 1, m) + m * Uc(k - 3, m):
            bad += 1
check('Lemma 2.5 four-term recurrence on DP table (k<=60, m<=60)', bad == 0, 'bad=%d' % bad)

# --- N：三种来源对照
NU = N_table_from_U(U, K)
NT = N_tri(150)
for k in range(0, 10):
    nb = N_brute(k)
    check('N_brute vs N_from_U k=%d' % k, all(nb.get(q, 0) == NU[k][q] for q in range(k + 1)) and all(q <= k for q in nb),
          str(nb) + ' vs ' + str(NU[k]))
print('N_brute done %.1fs' % (time.time() - t0))
check('N_from_U == N_tri for k<=60', all(NU[k] == NT[k] for k in range(K + 1)))
# 论文表 2
paper_N = [[1], [0, 1], [0, 1, 2], [0, 1, 4, 2], [0, 1, 7, 8, 2], [0, 1, 12, 25, 16, 2], [0, 1, 19, 59, 65, 26, 2],
           [0, 1, 29, 124, 199, 139, 38, 2], [0, 1, 44, 253, 557, 574, 277, 52, 2]]
check('paper Table 2', all(NU[k] == paper_N[k] for k in range(9)))
# 基本事实：N(k,0)=0 (k≥1)，N(k,1)=1，N(k,k)=2 (k≥2)，deg n_k=k−1，n_k(0)=1
ok = all(NU[k][0] == 0 and NU[k][1] == 1 for k in range(1, K + 1)) and all(NU[k][k] == 2 for k in range(2, K + 1))
check('N(k,0)=0, N(k,1)=1, N(k,k)=2', ok)
nU = {k: nrow(NU, k) for k in range(1, K + 1)}
check('deg n_k = k-1, n_k(0)=1', all(len(nU[k]) - 1 == k - 1 and nU[k][0] == 1 for k in range(1, K + 1)))
check('n_1,n_2,n_3', nU[1] == [1] and nU[2] == [1, 2] and nU[3] == [1, 4, 2])

# --- 引理 0
for k in range(4, K + 1):
    rhs = add(mul1z(nU[k - 1]), Phi(nU[k - 3]))
    check('Lemma0 k=%d' % k, nU[k] == rhs)
check('k=3: n_3 - (1+z) n_2 = z', add(nU[3], scal(-1, mul1z(nU[2]))) == [0, 1])
# 引理 0 证明里的三个和式（逐项）
for k in range(4, K + 1):
    n = nU[k - 3]
    Nk3 = lambda q: NU[k - 3][q] if 0 <= q <= k - 3 else 0
    s1 = norm([(q - 1) * Nk3(q - 2) for q in range(1, k + 1)])            # Σ (q−1)N(k−3,q−2) z^(q−1)
    s2 = norm([2 * (q - 1) * Nk3(q - 1) for q in range(1, k + 1)])
    s3 = norm([(q - 1) * Nk3(q) for q in range(1, k + 1)])
    zn1 = mulz(deriv(n))
    e1 = mul([0, 0, 1], add(zn1, scal(2, n)))
    e2 = scal(2, mulz(add(zn1, n)))
    e3 = zn1
    check('Lemma0 sums k=%d' % k, s1 == e1 and s2 == e2 and s3 == e3)
# T、Φ 的等价写法：T n = z((1+z)^2 n)'/(1+z)
for k in range(1, 30):
    n = nU[k]
    P = mul([1, 2, 1], n)
    dP = deriv(P)
    # dP = (1+z)·L n
    Ln = add(mul1z(deriv(n)), scal(2, n))
    check('T alt form k=%d' % k, dP == mul1z(Ln) and T(n) == mulz(Ln))

# --- 反向检查（应当 FAIL）
def Phi_bad(p):   # 把 2zn 改成 3zn
    return mul1z(add(mul([0, 1, 1], deriv(p)), scal(3, mulz(p))))
nbad = sum(1 for k in range(4, K + 1) if nU[k] != add(mul1z(nU[k - 1]), Phi_bad(nU[k - 3])))
print('REVERSE Phi(2zn->3zn): Lemma0 fails for %d of %d k (expect all)' % (nbad, K - 3))
check('reverse: corrupted Phi detected for every k', nbad == K - 3)
# 改动一个 N（N(20,10)+1）：引理 0 的核对在 k=20 处应失败
NU2 = [row[:] for row in NU]
NU2[20][10] += 1
n20 = nrow(NU2, 20)
det = n20 != add(mul1z(nU[19]), Phi(nU[17]))
print('REVERSE N(20,10)+1 detected by Lemma0 check:', det)
check('reverse: corrupted N detected', det)
# 三角递推在 k=2 不成立（论文 Prop 2.7 的说明）：用递推算 N(2,2) 得 1
check('N_tri fails at (2,2) as stated', 0 + 1 + (2 - 1) * (0 + 0 + 0) == 1 and NU[2][2] == 2)

print('elapsed %.1fs' % (time.time() - t0))
print('TOTAL PASS=%d FAIL=%d' % (PASS, FAIL))
