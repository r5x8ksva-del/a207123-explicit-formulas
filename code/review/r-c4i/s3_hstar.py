# -*- coding: utf-8 -*-
"""s3：独立复核定理 3.5（C4-15）：p_d 在基 {C(k+c-j,2d)}_{j=0..2d} 下（c 为任意整数）总有负系数。
做法与被复核者相同的数学框架，但独立实现，并做两项额外核对：
  (1) h_j 公式本身：对若干 (d,c) 用线性代数直接解基展开系数，与 h_j 公式比较；
  (2) 根界：同时用 Fujiwara 界与 Cauchy 界（1+max|a_i/a_n|），取较小者；界外 h_1<0 由首项为负、偶次保证。
另外：完整序列分子 Q_d(x)=(1-x)^{2d+1} sum_k D(k,d) x^k 是 <=4d+2 次多项式且有负系数（d 大范围）。
用法：py -3.14 s3_hstar.py [K] [DH]
"""
import sys, os, time, pickle
from fractions import Fraction
from math import comb, factorial
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rlib import ptrim, padd, psub, pmul, pscale, peval, pshift, interp

try:
    sys.stdout.reconfigure(encoding='utf-8')
except Exception:
    pass
K = int(sys.argv[1]) if len(sys.argv) > 1 else 150
DH = int(sys.argv[2]) if len(sys.argv) > 2 else 16
t0 = time.time()
with open(os.path.join(HERE, 'N_K%d.pkl' % K), 'rb') as fh:
    N = pickle.load(fh)['N']


def D(k, d):
    q = k - d
    if k < 0 or q < 0 or q > k:
        return 0
    return N[k][q]


DMAX = (K - 8) // 4
PD = {}
for d in range(0, DMAX + 1):
    xs = list(range(2 * d + 2, 4 * d + 3))
    PD[d] = interp(xs, [D(k, d) for k in xs])
    assert all(peval(PD[d], k) == D(k, d) for k in range(2 * d + 2, K + 1))


def hvec(p, d, s):
    n = 2 * d
    vals = [peval(p, s + t) for t in range(n + 1)]
    return [sum((-1) ** i * comb(n + 1, i) * vals[j - i] for i in range(j + 1)) for j in range(n + 1)]


def binom_poly_k(c, r):
    """C(k+c, r) 作为 k 的多项式。"""
    p = [Fraction(1)]
    for i in range(r):
        p = pmul(p, [Fraction(c - i), Fraction(1)])
    return pscale(p, Fraction(1, factorial(r)))


def solve(A, b):
    """Fraction 高斯消元，A 方阵。"""
    n = len(A)
    M = [list(map(Fraction, A[i])) + [Fraction(b[i])] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col] / M[col][col]
                M[r] = [M[r][i] - f * M[col][i] for i in range(n + 1)]
    return [M[i][n] / M[i][i] for i in range(n)]


# (1) h_j 公式 vs 直接解线性方程（d<=3, c in [-6,10]）
ok = True
for d in range(1, 4):
    n = 2 * d
    for c in range(-6, 11):
        basis = [binom_poly_k(c - j, n) for j in range(n + 1)]
        A = [[(basis[j][i] if i < len(basis[j]) else 0) for j in range(n + 1)] for i in range(n + 1)]
        b = [(PD[d][i] if i < len(PD[d]) else 0) for i in range(n + 1)]
        coef = solve(A, b)
        s = 2 * d - c
        if coef != hvec(PD[d], d, s):
            ok = False
print(('OK  ' if ok else 'BAD ') + 'hformula: 线性代数直接展开 == h_j(s) 公式（s=2d-c），d<=3, -6<=c<=10')
res = [ok]

# (2) 主检查
ok_all = True
for d in range(1, DH + 1):
    p = PD[d]
    n = 2 * d
    h1 = psub(pshift(p, 1), pscale(p, n + 1))           # 作为 s 的多项式
    deg = len(h1) - 1
    lead = h1[-1]
    assert deg == n and lead < 0 and lead == -n * p[-1]
    # Fujiwara
    fb = Fraction(0)
    bnd_f = 0
    for i in range(1, deg + 1):
        r = abs(h1[deg - i] / lead)
        if i == deg:
            r = r / 2
        b = 0
        while Fraction(b) ** i < r:
            b += 1
        bnd_f = max(bnd_f, b)
    bnd_f = 2 * bnd_f
    # Cauchy
    bnd_c = 1 + max(abs(h1[i] / lead) for i in range(deg))
    bnd_c = int(bnd_c) + 1
    B = min(bnd_f, bnd_c)
    # 界外符号的直接佐证：在 ±(B+1), ±(B+50) 处 h1<0
    assert all(peval(h1, s) < 0 for s in (B + 1, -B - 1, B + 50, -B - 50))
    nonneg_s = []
    cand = 0
    for s in range(-B - 1, B + 2):
        if peval(p, s) >= 0 and peval(h1, s) >= 0:
            cand += 1
            hv = hvec(p, d, s)
            if all(h >= 0 for h in hv):
                nonneg_s.append(s)
    ok = (not nonneg_s)
    ok_all = ok_all and ok
    print(('OK  ' if ok else 'BAD ') + 'd=%d: 根界 B=%d (Fujiwara %d, Cauchy %d)，|s|<=B+1 内 h_0,h_1>=0 的候选 %d 个，全非负 h 向量：%s' % (d, B, bnd_f, bnd_c, cand, nonneg_s))
res.append(ok_all)

# (3) Q_d(x) 有负系数且为 <=4d+2 次多项式
ok = True
for d in range(1, DMAX + 1):
    ser = [D(k, d) for k in range(K + 1)]
    for _ in range(2 * d + 1):
        ser = [ser[i] - (ser[i - 1] if i > 0 else 0) for i in range(K + 1)]
    if any(ser[i] != 0 for i in range(4 * d + 3, K + 1)) or min(ser[:4 * d + 3]) >= 0:
        ok = False
    if d == 1 and ser[:7] != [0, 0, 1, 1, -1, 3, -2]:
        ok = False
print(('OK  ' if ok else 'BAD ') + 'Q_d(x) 为 <=4d+2 次多项式且有负系数，1<=d<=%d；d=1 时 = x^2+x^3-x^4+3x^5-2x^6' % DMAX)
res.append(ok)
print('SUMMARY s3 ok=%d bad=%d runtime=%.1fs' % (sum(res), len(res) - sum(res), time.time() - t0))
