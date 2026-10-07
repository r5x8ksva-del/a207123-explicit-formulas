# -*- coding: utf-8 -*-
"""表 B 的 B1（h_k 全实根）探索：N 行多项式 n_k(z)=sum_q N(k,q) z^(q-1) 的根与各种交错关系。

n_k = (1+z)[n_{k-1} + T n_{k-3}]（k>=4），T n := z(1+z) n' + 2 z n。
根用 numpy 求近似值，再用 Fraction 在每个根两侧精确验符号变化（确认全部实根）。
只做观察，不是证明。
"""
import sys
from fractions import Fraction
import numpy as np

sys.path.insert(0, __file__.rsplit('code', 1)[0] + 'code')


def N_table(K):
    """N[k][q]，0<=k<=K。三角递推（k>=3），初值 N(0,0)=1, N(1,1)=1, N(2,1)=1, N(2,2)=2。"""
    N = [[0] * (K + 2) for _ in range(K + 1)]
    N[0][0] = 1
    if K >= 1:
        N[1][1] = 1
    if K >= 2:
        N[2][1] = 1
        N[2][2] = 2
    for k in range(3, K + 1):
        for q in range(1, k + 1):
            r = q - 1
            v = N[k - 1][r] + N[k - 1][r + 1]
            if r >= 1:
                a = N[k - 3][r - 1] if r - 1 >= 0 else 0
                v += r * (a + 2 * N[k - 3][r] + N[k - 3][r + 1])
            N[k][q] = v
    return N


def peval(c, x):
    s = 0
    for a in reversed(c):
        s = s * x + a
    return s


def real_roots(c):
    """c: 整数系数（低次在前）。返回升序近似根；若无法确认全实根返回 None。"""
    c = list(c)
    while c and c[-1] == 0:
        c.pop()
    deg = len(c) - 1
    if deg <= 0:
        return []
    # 用 numpy 求根（系数缩放）
    approx = np.roots([float(a) for a in reversed(c)])
    if np.max(np.abs(approx.imag)) > 1e-6 * (1 + np.max(np.abs(approx.real))):
        return None
    rs = sorted(approx.real)
    # 精确核对：取相邻近似根的中点，符号应交替
    pts = [Fraction(rs[0]) - 1 - abs(Fraction(rs[0]))]
    for i in range(len(rs) - 1):
        pts.append((Fraction(rs[i]) + Fraction(rs[i + 1])) / 2)
    pts.append(Fraction(rs[-1]) + 1 + abs(Fraction(rs[-1])))
    signs = [peval(c, p) for p in pts]
    for i in range(len(signs) - 1):
        if signs[i] == 0 or (signs[i] > 0) == (signs[i + 1] > 0):
            return None
    return rs


def strip_minus_one(c):
    """除去 (1+z) 的全部因子，返回 (商, 重数)。"""
    c = list(c)
    mult = 0
    while len(c) > 1 and peval(c, -1) == 0:
        # 综合除法 by (z+1)，高次在前
        hi = list(reversed(c))
        out = [hi[0]]
        for a in hi[1:]:
            out.append(a - out[-1])  # 除以 (z - (-1))：b_i = a_i + r*b_{i-1}，r=-1
        rem = out.pop()
        assert rem == 0
        c = list(reversed(out))
        mult += 1
    return c, mult


def interlaces(f_roots, g_roots):
    """f 与 g 有公共交错多项式（实根、首项同号）的判据：
    合并后按大小，两者的根在每个区间 [第 i 个, 第 i+1 个] 中交替出现（允许相等）。
    这里用：deg f = deg g 时 max(f_i,g_i) <= min(f_{i+1},g_{i+1})；
    deg 相差 1 时把短的从左/右两种方式对齐，任一成立即可。"""
    a, b = sorted(f_roots), sorted(g_roots)
    if len(a) < len(b):
        a, b = b, a
    if len(a) == len(b):
        return all(max(a[i], b[i]) <= min(a[i + 1], b[i + 1]) + 1e-12 for i in range(len(a) - 1))
    if len(a) == len(b) + 1:
        # a 的根被 b 的根交错：a_1 <= b_1 <= a_2 <= ... <= b_{n-1} <= a_n
        ok1 = all(a[i] <= b[i] + 1e-12 and b[i] <= a[i + 1] + 1e-12 for i in range(len(b)))
        return ok1
    return False


def Tn(c):
    """T n = z(1+z) n' + 2 z n。"""
    d = [i * c[i] for i in range(1, len(c))]  # n'
    # z(1+z) n' = (z + z^2) n'
    out = [0] * (len(c) + 2)
    for i, a in enumerate(d):
        out[i + 1] += a
        out[i + 2] += a
    for i, a in enumerate(c):
        out[i + 1] += 2 * a
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


if __name__ == '__main__':
    K = 36
    N = N_table(K)
    n = {k: [N[k][q] for q in range(1, k + 1)] for k in range(1, K + 1)}
    # 核对 n_k 递推
    for k in range(4, K + 1):
        A = n[k - 1]
        B = Tn(n[k - 3])
        s = [0] * max(len(A), len(B))
        for i, a in enumerate(A):
            s[i] += a
        for i, a in enumerate(B):
            s[i] += a
        rhs = [0] * (len(s) + 1)
        for i, a in enumerate(s):
            rhs[i] += a
            rhs[i + 1] += a
        while len(rhs) > 1 and rhs[-1] == 0:
            rhs.pop()
        assert rhs == n[k], k
    print('n_k recurrence OK up to', K)
    roots = {}
    for k in range(1, K + 1):
        c, mult = strip_minus_one(n[k])
        r = real_roots(c)
        roots[k] = (r, mult)
        print('k=%2d deg=%2d mult(-1)=%d allreal=%s' % (k, len(n[k]) - 1, mult, r is not None))
    # 各种交错假设
    def R(k):
        return roots[k][0]
    tests = {
        'n_k vs n_{k-1}': lambda k: interlaces(R(k), R(k - 1)),
        'n_k vs n_{k-2}': lambda k: interlaces(R(k), R(k - 2)),
        'n_k vs n_{k-3}': lambda k: interlaces(R(k), R(k - 3)),
    }
    for name, fn in tests.items():
        res = [k for k in range(7, K + 1) if R(k) is not None and R(k - 3) is not None and fn(k)]
        print(name, 'holds for k in', res)
    # n_{k-1} 与 T n_{k-3} 的公共交错（去掉 -1 的因子后比较）
    out = []
    for k in range(7, K + 1):
        A, _ = strip_minus_one(n[k - 1])
        B, _ = strip_minus_one(Tn(n[k - 3]))
        ra, rb = real_roots(A), real_roots(B)
        ok = ra is not None and rb is not None and interlaces(ra, rb)
        out.append((k, len(A) - 1, len(B) - 1, ok))
    print('n_{k-1} vs T n_{k-3} (stripped):', out)
