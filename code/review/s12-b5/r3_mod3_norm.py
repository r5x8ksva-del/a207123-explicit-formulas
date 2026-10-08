# -*- coding: utf-8 -*-
"""s12-b5 复核 r3：引理 4.2、定理 4 的 3 进论证（Z[ξ]=Z[x]/(x^3+x-1) 中的整数运算，自写）。

  r3-T-int      T_n(z)=sum_l C(n+2,l+2) n!/l! z^l 的系数是整数，且 T_n = n!·L_n^{(2)}(-z)（L 用三项递推，n<=40）
  r3-lem42      引理 4.2：T_n(z) ≡ z^n + 2[n≡2 (mod 3)] z^{n-1} (mod 3)（逐系数，0<=n<=300）
  r3-unit       ξ^{-1}=1+ξ^2；z=ξ^{-3}；z-1=ξ^{-2}（精确）；z+2 ≡ ξ^{-2} (mod 3)；N(ξ)=1、N(1+ξ)=3、N(z)=1
  r3-psi        Ψ_q = z^2 T_{q-2}(z)/(q-2)!（Q(ξ) 中精确，2<=q<=40）
  r3-normid     N(ξ(1+ξ) z^2 T_{q-2}(z)/(q-2)!) = 3 N(T_{q-2}(z))/((q-2)!)^3（精确，2<=q<=40）
  r3-cong       T_{q-2}(z) ≡ z^{q-2} 或 z^{q-3} ξ^{-2} (mod 3Z[ξ])（按 q-2 mod 3），且 N(T)≡N(该单位)=±1 (mod 3)（2<=q<=150）
  r3-v3         直接计算：v_3(3 N(T_{q-2}(z)))=1，3N(T) 不是整数的立方（2<=q<=150）
  r3-rev-*      反向：例外类改成 n≡1 时引理 4.2 不成立；把 T 换成 (1+ξ)^2 T 后 v_3≠1 被检出；立方判定对 27、-8·27 给出「是立方」
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s12b5_common import report, summary, vp_int, is_int_cube  # noqa: E402

t0 = time.time()


# ---------------------------------------------------------------- Z[ξ]，ξ^3 = 1 - ξ
def zmul(a, b):
    r = [0] * 5
    for i in range(3):
        if a[i]:
            for j in range(3):
                if b[j]:
                    r[i + j] += a[i] * b[j]
    # x^3 = 1 - x ;  x^4 = x - x^2
    return [r[0] + r[3], r[1] - r[3] + r[4], r[2] - r[4]]


def zadd(a, b):
    return [a[i] + b[i] for i in range(3)]


def zscale(a, c):
    return [c * v for v in a]


def zpow(a, n):
    r = [1, 0, 0]
    b = list(a)
    while n:
        if n & 1:
            r = zmul(r, b)
        b = zmul(b, b)
        n >>= 1
    return r


def znorm(a):
    cols = [zmul(a, [1, 0, 0]), zmul(a, [0, 1, 0]), zmul(a, [0, 0, 1])]
    M = [[cols[j][i] for j in range(3)] for i in range(3)]
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def zmod3(a):
    return [v % 3 for v in a]


XI = [0, 1, 0]
XIINV = [1, 0, 1]
Z = zpow(XIINV, 3)


def Tcoef(n):
    return [comb(n + 2, l + 2) * (factorial(n) // factorial(l)) for l in range(n + 1)]


def Teval(n, z):
    co = Tcoef(n)
    r = [0, 0, 0]
    for c in reversed(co):
        r = zadd(zmul(r, z), [c, 0, 0])
    return r


# ---------------------------------------------------------------- r3-T-int
def laguerre_poly(n, alpha):
    L0 = [Fr(1)]
    if n == 0:
        return L0
    L1 = [Fr(1 + alpha), Fr(-1)]
    for m in range(1, n):
        a = [Fr(2 * m + 1 + alpha) * c for c in L1] + [Fr(0)]
        for j in range(len(L1)):
            a[j + 1] -= L1[j]
        for j in range(len(L0)):
            a[j] -= (m + alpha) * L0[j]
        L0, L1 = L1, [c / (m + 1) for c in a]
    return L1


ok = True
for n in range(0, 41):
    Lp = laguerre_poly(n, 2)
    viaL = [factorial(n) * Lp[l] * (-1) ** l for l in range(n + 1)]   # n! L_n(-z) 的 z^l 系数
    if viaL != [Fr(c) for c in Tcoef(n)]:
        ok = False
        print('  T mismatch n=%d' % n)
report(ok, 'r3-T-int', 'T_n 系数为整数且 T_n(z)=n!·L_n^{(2)}(-z)（Laguerre 三项递推，0<=n<=40）')


# ---------------------------------------------------------------- r3-lem42
def lem42_ok(n, exc=2):
    co = Tcoef(n)
    target = [0] * (n + 1)
    target[n] = 1
    if n % 3 == exc and n >= 1:
        target[n - 1] = 2
    return all((co[l] - target[l]) % 3 == 0 for l in range(n + 1))


# 反向演示：命令行加 --break 时主检验用错的例外类（n≡1），脚本应报 FAIL、退出码 1
BREAK = '--break' in sys.argv
if BREAK:
    print('[--break] 主检验 r3-lem42 故意把例外类改成 n≡1 (mod 3)', flush=True)
ok = all(lem42_ok(n, exc=1 if BREAK else 2) for n in range(0, 301))
report(ok, 'r3-lem42', '引理 4.2 逐系数成立（0<=n<=300）')
bad_exc = sum(1 for n in range(0, 301) if not lem42_ok(n, exc=1))
report(bad_exc > 0, 'r3-rev-lem42', '反向：例外类改成 n≡1 (mod 3) 后有 %d 个 n 不成立（应 >0）' % bad_exc)

# ---------------------------------------------------------------- r3-unit
ok = zmul(XI, XIINV) == [1, 0, 0]
xim2 = zpow(XIINV, 2)
ok = ok and zadd(Z, [-1, 0, 0]) == xim2
ok = ok and zmod3(zadd(Z, [2, 0, 0])) == zmod3(xim2)
ok = ok and znorm(XI) == 1 and znorm([1, 1, 0]) == 3 and znorm(Z) == 1 and znorm(XIINV) == 1
report(ok, 'r3-unit', 'ξ·(1+ξ^2)=1；z-1=ξ^{-2}（精确）；z+2≡ξ^{-2} (mod 3)；N(ξ)=N(z)=N(ξ^{-1})=1、N(1+ξ)=3')


# ---------------------------------------------------------------- Q(ξ) 中的有理数运算（分母只出现阶乘）
def qnorm(a):
    """a 是 Fraction 三元组；N(a)=N(D a)/D^3。"""
    from math import lcm
    D = 1
    for v in a:
        D = lcm(D, Fr(v).denominator)
    ai = [int(Fr(v) * D) for v in a]
    return Fr(znorm(ai), D ** 3)


ok_psi = ok_id = True
for q in range(2, 41):
    psi = [Fr(0)] * 3
    for n in range(2, q + 1):
        zn = zpow(Z, n)
        psi = [psi[i] + Fr(comb(q, n), factorial(n - 2)) * zn[i] for i in range(3)]
    T = Teval(q - 2, Z)
    rhs = [Fr(v, factorial(q - 2)) for v in zmul(zpow(Z, 2), T)]
    if psi != rhs:
        ok_psi = False
    theta = [Fr(v, factorial(q - 2)) for v in zmul(zmul(zmul(XI, [1, 1, 0]), zpow(Z, 2)), T)]
    if qnorm(theta) != Fr(3 * znorm(T), factorial(q - 2) ** 3):
        ok_id = False
report(ok_psi, 'r3-psi', 'Ψ_q=sum_{n=2}^q C(q,n) z^n/(n-2)! = z^2 T_{q-2}(z)/(q-2)!（Q(ξ) 中精确，2<=q<=40）')
report(ok_id, 'r3-normid', 'N(ξ(1+ξ)z^2 T_{q-2}(z)/(q-2)!) = 3N(T_{q-2}(z))/((q-2)!)^3（2<=q<=40；符号为 +）')

# ---------------------------------------------------------------- r3-cong、r3-v3
QMAX = 150
ok_c = ok_v = True
small = []
for q in range(2, QMAX + 1):
    n = q - 2
    T = Teval(n, Z)
    if n % 3 == 2:
        eps = zmul(zpow(Z, n - 1), xim2)
    else:
        eps = zpow(Z, n)
    NT = znorm(T)
    Ne = znorm(eps)
    if zmod3(T) != zmod3(eps) or Ne not in (1, -1) or (NT - Ne) % 3 != 0:
        ok_c = False
        print('  cong fail q=%d' % q)
    if vp_int(3 * NT, 3) != 1 or is_int_cube(3 * NT):
        ok_v = False
        print('  v3 fail q=%d' % q)
    if q <= 6:
        small.append((q, NT))
report(ok_c, 'r3-cong', 'T_{q-2}(z) 模 3 等于单位 z^{q-2} 或 z^{q-3}ξ^{-2}，N(T)≡N(ε)=±1 (mod 3)（2<=q<=%d）' % QMAX)
report(ok_v, 'r3-v3', 'v_3(3N(T_{q-2}(z)))=1，3N(T) 不是立方（2<=q<=%d）；小例 %s' % (QMAX, small))

# ---------------------------------------------------------------- 反向
bad = 0
for q in range(2, 41):
    T2 = zmul(zpow([1, 1, 0], 2), Teval(q - 2, Z))
    NT2 = znorm(T2)
    if vp_int(3 * NT2, 3) != 1:
        bad += 1
report(bad == 39, 'r3-rev-v3', '反向：把 T 换成 (1+ξ)^2·T 后 39 个 q 中有 %d 个 v_3≠1 被检出（应全部）' % bad)
report(is_int_cube(27) and is_int_cube(-8 * 27) and not is_int_cube(3) and not is_int_cube(9 * 7),
       'r3-rev-cube', '反向：立方判定对 27、-216 为真，对 3、63 为假')

print('time %.1fs' % (time.time() - t0))
sys.exit(1 if summary('r3') else 0)
