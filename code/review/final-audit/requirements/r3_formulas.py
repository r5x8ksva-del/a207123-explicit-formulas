# -*- coding: utf-8 -*-
"""最终审计（requirements）r3：对照原始定义（core.U_fast_table / U_list / N_brute）抽查报告里与交付要求直接相关的显式公式。
  - C-4 要求的 d<=5 公式 p_0..p_5（05_C4.md T4.1），以及门槛 2d+2 精确、平移形式 p_2、锚点、Newton 系数例子；
  - T4.3(5) 的 nu_1、nu_2；T4.3(4) Num_q(1)=A000262；
  - T5.2 的四个 m 次首项系数公式；T5.3(1) 的 h_k'(1)；T5.3(3) 的首项系数；T5.3(2) U_{3j}(-j-1)=j!；
  - T5.1(4) c_4、c_18 精确值（闭式）；T2.6(ii) 的范数 17/8 与 103/16；
  - T5.4(4)(5) U_3、U_4 闭式。
只读，不修改任何文件。
"""
import os
import sys
from fractions import Fraction as Fr
from math import comb, factorial

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'code'))
import core  # noqa: E402

K = 60
M = 62
T = core.U_fast_table(K, M)
# 锚定：快速 DP == 参考实现 U_list（第 1 节逐字照抄）
for m in range(0, 13):
    ref = core.U_list(m, K)
    assert all(ref[k] == T[k][m] for k in range(K + 1)), m
# N(k,q) 由容斥；与 DFS 定义对照 k<=8
N = [[core.N_from_U(T, k, q) for q in range(k + 1)] for k in range(K + 1)]
for k in range(0, 9):
    nb = core.N_brute(k)
    assert all(N[k][q] == nb.get(q, 0) for q in range(k + 1)), k
print('[anchor] U_fast_table == U_list (m<=12,k<=60); N 容斥 == N_brute (k<=8)')

fails = []


def check(tag, ok, extra=''):
    print(('PASS ' if ok else 'FAIL ') + tag + (' ' + extra if extra else ''))
    if not ok:
        fails.append(tag)


def D(k, d):
    q = k - d
    if q < 0 or q > k:
        return 0
    return N[k][q]


def P(coefs, den):
    """系数从高到低"""
    def f(k):
        v = 0
        for c in coefs:
            v = v * k + c
        return Fr(v, den)
    return f


# T4.1 的 d<=5 公式（逐字抄自 05_C4.md）
pd = {
    0: P([2], 1),
    1: P([1, -1, -4], 1),
    2: P([1, -10, 43, -98, 164], 4),
    3: P([1, -27, 331, -2225, 8560, -17392, 11088], 24),
    4: P([1, -52, 1242, -17280, 151217, -845644, 2926356, -5702176, 5014464], 192),
    5: P([1, -85, 3350, -79370, 1241073, -13308173, 98708360, -498528820, 1637903536, -3158022432, 2686170240], 1920),
}
for d, f in pd.items():
    ok_hi = all(f(k) == D(k, d) for k in range(2 * d + 2, K + 1))
    exc = [k for k in range(d + 1, 2 * d + 2) if f(k) == D(k, d)]
    defect = D(2 * d + 1, d) - f(2 * d + 1)
    check('T4.1 p_%d：D(k,%d)=p_%d(k) 对 %d<=k<=60；门槛下 d+1..2d+1 处相等的 k=%s；e_d(2d+1)=%s（应为 %s）'
          % (d, d, d, 2 * d + 2, exc, defect, (-1) ** (d + 1) * factorial(d + 1)),
          ok_hi and not exc and defect == (-1) ** (d + 1) * factorial(d + 1))
# 平移形式 p_2=(m^4+10m^3+43m^2+82m+124)/4，m=k-5
f2s = P([1, 10, 43, 82, 124], 4)
check('T4.1 p_2 的平移形式（m=k-2d-1）', all(f2s(k - 5) == pd[2](k) for k in range(-20, 80)))
# 锚点 D(2d+2,d)
anch = [D(2 * d + 2, d) for d in range(6)]
check('④A.5 锚点 D(2d+2,d)=2,8,65,574,6012,70674', anch == [2, 8, 65, 574, 6012, 70674], str(anch))
# Newton 系数 d=2：65,74,64,30,6（基点 6）
vals = [pd[2](6 + i) for i in range(6)]
newt = []
cur = vals[:]
for i in range(5):
    newt.append(cur[0])
    cur = [cur[j + 1] - cur[j] for j in range(len(cur) - 1)]
check('T4.2(3) d=2 Newton 系数 65,74,64,30,6', newt == [65, 74, 64, 30, 6], str(newt))

# Num_q：P_{q-1} * sum_k N(k,q) x^k（截断 x^60）
def polymul(a, b, cap):
    r = [0] * min(len(a) + len(b) - 1, cap)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if i + j >= cap:
                break
            r[i + j] += x * y
    return r


def Pm(q):  # P_{q-1}=prod_{i=0}^{q-1}(1-x-i x^3)
    p = [1]
    for i in range(q):
        p = polymul(p, [1, -1, 0, -i], 10 ** 9)
    return p


nu1_ok, nu2_ok, a262 = True, True, []
for q in range(1, 18):
    ser = [N[k][q] if q <= k else 0 for k in range(K + 1)]
    num = polymul(Pm(q), ser, K + 1)
    # 次数 3q-2 <= 60 时检查高位为 0
    assert all(c == 0 for c in num[3 * q - 1:K + 1]), q
    num = num[:3 * q - 1]
    a262.append(sum(num))
    if q >= 3:
        nu1_ok &= (num[q + 1] == q * q - q - 4)
    if q >= 4:
        nu2_ok &= (Fr(num[q + 2]) == Fr(q ** 4 - 6 * q ** 3 + 7 * q ** 2 - 2 * q + 76, 4))
check('T4.3(5) [x^{q+1}]Num_q=q^2-q-4 (3<=q<=17)', nu1_ok)
check('T4.3(5) [x^{q+2}]Num_q=(q^4-6q^3+7q^2-2q+76)/4 (4<=q<=17)', nu2_ok)
# A000262: 1,1,3,13,73,501,4051,...  a(n)=(2n-1)a(n-1)-(n-1)(n-2)a(n-2)
A = [1, 1]
for n in range(2, 20):
    A.append((2 * n - 1) * A[n - 1] - (n - 1) * (n - 2) * A[n - 2])
check('T4.3(4) Num_q(1)=A000262(q) (q<=17)', a262 == A[1:18], str(a262[:6]))

# T5.2：系数由 Newton 插值得到（不经过 N）
def mcoef(k):
    xs = list(range(k + 1))
    ys = [Fr(T[k][m]) for m in xs]
    # Lagrange -> 单项式系数（精确）
    coef = [Fr(0)] * (k + 1)
    for i in range(k + 1):
        num = [Fr(1)]
        den = Fr(1)
        for j in range(k + 1):
            if j == i:
                continue
            num = [(num[t - 1] if t >= 1 else 0) - j * (num[t] if t < len(num) else 0) for t in range(len(num) + 1)]
            den *= (i - j)
        for t in range(len(num)):
            coef[t] += ys[i] * num[t] / den
    return coef


ok = [True] * 4
for k in range(2, 31):
    c = mcoef(k)
    if c[k] != Fr(2, factorial(k)):
        ok[0] = False
    if k >= 4 and c[k - 1] != Fr(k * k - 2 * k - 1, factorial(k - 1)):
        ok[1] = False
    if k == 3 and c[2] != 2:
        ok[1] = False
    if k >= 6 and c[k - 2] != Fr(3 * k ** 4 - 36 * k ** 3 + 162 * k ** 2 - 313 * k + 422, 12 * factorial(k - 2)):
        ok[2] = False
    if k >= 8 and c[k - 3] != Fr(k ** 6 - 30 * k ** 5 + 379 * k ** 4 - 2533 * k ** 3 + 9570 * k ** 2 - 19331 * k + 13380, 24 * factorial(k - 3)):
        ok[3] = False
for i, tag in enumerate(['[m^k]U_k=2/k!', '[m^{k-1}]U_k=(k^2-2k-1)/(k-1)! (k>=4; k=3 为 2)', '[m^{k-2}] 公式 (k>=6)', '[m^{k-3}] 公式 (k>=8)']):
    check('T5.2 ' + tag + '（2<=k<=30，单项式插值）', ok[i])


# h_k(t) = (1-t)^{k+1} sum_m U_k(m) t^m（截断）
def hpoly(k):
    s = [T[k][m] for m in range(M + 1)]
    b = [(-1) ** i * comb(k + 1, i) for i in range(k + 2)]
    h = polymul(b, s, M + 1)
    h = h[:k + 1]
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


okd, okl = True, True
for k in range(1, 46):
    h = hpoly(k)
    if k >= 4:
        dh1 = sum(i * c for i, c in enumerate(h))
        okd &= (dh1 == -(k * k - 3 * k - 2))
    a, r = divmod(k, 3)
    deg = len(h) - 1
    lead = h[-1]
    want = {0: (-1) ** a * factorial(a), 1: (-1) ** a * (comb(1, 1) and 0), 2: (-1) ** a * factorial(a + 1)}
    # c(a+2,2) = (a+1)! H_{a+1}
    c2 = sum(Fr(factorial(a + 1), i) for i in range(1, a + 2))
    want[1] = (-1) ** a * c2
    okl &= (deg == (2 * k) // 3 and lead == want[r])
check('T5.3(1) h_k\'(1)=-(k^2-3k-2) (4<=k<=45)', okd)
check('T5.3(3) deg h_k=floor(2k/3) 与首项系数 (1<=k<=45)', okl)


# U_{3j}(-j-1)=j!：用 k 次插值多项式求负整数值
def uval(k, y):
    xs = list(range(k + 1))
    tot = Fr(0)
    for i in xs:
        num, den = Fr(1), Fr(1)
        for j in xs:
            if j != i:
                num *= (y - j)
                den *= (i - j)
        tot += T[k][i] * num / den
    return tot


okn = all(uval(3 * j, -j - 1) == factorial(j) for j in range(1, 11))
okz = all(uval(k, -j) == 0 for k in range(1, 31) for j in range(1, (k + 2) // 3 + 1)) and \
    all(uval(k, -((k + 2) // 3) - 1) != 0 for k in range(1, 31))
check('T5.3(2) U_{3j}(-j-1)=j! (j<=10)；U_k(-j)=0 (1<=j<=s_k)、U_k(-s_k-1)!=0 (k<=30)', okn and okz)

# T5.4(4)(5)
ok3 = all(Fr(T[3][m]) == Fr((m + 1) * (m * m + 5 * m + 3), 3) == 2 * comb(m + 3, 3) - (m + 1) for m in range(M + 1))
ok4 = all(Fr(T[4][m]) == Fr((m + 1) * (m + 2) * (m * m + 11 * m + 6), 12) == comb(m + 2, 2) ** 2 - 4 * comb(m + 2, 4) for m in range(M + 1))
check('T5.4(4)(5) U_3、U_4 闭式 (m<=62)', ok3 and ok4)


# T5.1(4) c_4、c_18 精确：c_m = rho(rho^{3m+1}/m! - sum_{i<m} rho^{3i}/i!)/(3rho-2)
def cm(m, rho):
    s = Fr(rho ** (3 * m + 1), factorial(m)) - sum(Fr(rho ** (3 * i), factorial(i)) for i in range(m))
    return rho * s / (3 * rho - 2)


check('T5.1(4) c_4=215/2', cm(4, 2) == Fr(215, 2))
check('T5.1(4) c_18=37105325714711350249401/6830759936000', cm(18, 3) == Fr(37105325714711350249401, 6830759936000), str(cm(18, 3)))
# 独立：U_k(18)/3^k 的收敛（精确有理，粗看）
r = Fr(T[60][18] if 18 <= M else 0, 3 ** 60)
print('     note U_60(18)/3^60 =', float(r), ' c_18 ~', float(cm(18, 3)), '（m=18 时 k=60 远未收敛，只作量级参考）')


# T2.6(ii)：K_2=Q[x]/(2x^3+x-1) 中 N(W~_2 - 1)=17/8，N(W~_2)=103/16（乘法矩阵行列式）
def norm_in_K(g, f):
    """f 首一化后的乘法矩阵行列式；g、f 为低到高系数列表（Fraction）。"""
    f = [Fr(c) for c in f]
    lc = f[-1]
    f = [c / lc for c in f]
    n = len(f) - 1

    def red(p):
        p = [Fr(c) for c in p] + []
        for i in range(len(p) - 1, n - 1, -1):
            c = p[i]
            if c:
                for j in range(n + 1):
                    p[i - n + j] -= c * f[j]
        return (p + [Fr(0)] * n)[:n]

    cols = []
    for i in range(n):
        prod = [Fr(0)] * (len(g) + i)
        for t, c in enumerate(g):
            prod[t + i] += c
        cols.append(red(prod))
    # det
    Mx = [[cols[j][i] for j in range(n)] for i in range(n)]
    det = Fr(1)
    for c in range(n):
        piv = next((r_ for r_ in range(c, n) if Mx[r_][c] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != c:
            Mx[c], Mx[piv] = Mx[piv], Mx[c]
            det = -det
        det *= Mx[c][c]
        for r_ in range(c + 1, n):
            fac = Mx[r_][c] / Mx[c][c]
            for t in range(c, n):
                Mx[r_][t] -= fac * Mx[c][t]
    return det


f2 = [-1, 1, 0, 2]
W2 = [0] * 9
W2[0] = 1
W2[5] += 1 * 2          # j=1: 1*2^(1) x^5
W2[8] += 2 * 2 * 1      # j=2: 2*2^(2) x^8
W2m1 = W2[:]
W2m1[0] = 0
check('T2.6(ii) N(W~_2-1)=17/8', norm_in_K(W2m1, f2) == Fr(17, 8), str(norm_in_K(W2m1, f2)))
check('T2.6(ii) N(W~_2)=103/16', norm_in_K(W2, f2) == Fr(103, 16), str(norm_in_K(W2, f2)))
f1 = [-1, 1, 0, 1]
W1 = [1, 0, 0, 0, 0, 1]
check('T2.6 N(W~_1)=3（纤维 u=1）', norm_in_K(W1, f1) == 3, str(norm_in_K(W1, f1)))

print('SUMMARY r3 fails=%d %s' % (len(fails), fails))
