# -*- coding: utf-8 -*-
"""复核者 s14-b8：命题 5 的根统计（精确 Sturm 序列，自写）。

v_k(y) := k!·u_k(-y)/((y-1)(y-2)…(y-s_k))（整系数，次数 k-s_k），由牛顿系数（来自按定义 DP 核对过的递推表）得到。
对 1<=k<=KR：用本原伪余式的 Sturm 序列数实根、二分隔离，再在 v_k 上二分到宽度 <1e-9。
检查：(a) y>s_k+1/2 的根总数、到最近整数的平均距离、<0.05 与 <0.01 的个数（笔记：260、0.252、23、4）；
(b) y>s_k 的根数 - floor(k/3) ∈ {0,1}，多出的根在 (s_k,s_k+1)；(c) 笔记点名的根 k=10:9.0213、k=30:(60.0003,60.0004)、
k=37:5531.9978、k=40:69.0045、k=30 与 40 的最大实根 5291.6、10363.9；(d) v_k 无重根。
用法：py -3.14 code/review/s14-b8/r5_roots.py [KR=40]
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import b8lib as L  # noqa: E402

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

KR = int(sys.argv[1]) if len(sys.argv) > 1 else 40
RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def content_prim(a):
    """整系数多项式除以正的容量。"""
    from math import gcd
    g = 0
    for c in a:
        g = gcd(g, abs(c))
    return [c // g for c in a] if g > 1 else list(a)


def deriv(a):
    return [i * a[i] for i in range(1, len(a))] or [0]


def prem_neg(A, B):
    """返回 -rem(A,B) 乘以一个正数后的本原整系数多项式（Sturm 序列只允许正的倍数）。"""
    A = [Fr(c) for c in A]
    B = [Fr(c) for c in B]
    while len(A) >= len(B) and any(A):
        coef = A[-1] / B[-1]
        sh = len(A) - len(B)
        for i in range(len(B)):
            A[i + sh] -= coef * B[i]
        A = trim(A)
        if len(A) == 1 and A[0] == 0:
            break
        if len(A) < len(B):
            break
    R = [-c for c in A]
    den = 1
    for c in R:
        den = den * c.denominator // __import__('math').gcd(den, c.denominator)
    R = [int(c * den) for c in R]
    return content_prim(trim(R))


def sturm_seq(p):
    seq = [content_prim(p), content_prim(deriv(p))]
    while len(seq[-1]) > 1 or seq[-1][0] == 0:
        r = prem_neg(seq[-2], seq[-1])
        if len(r) == 1 and r[0] == 0:
            break
        seq.append(r)
        if len(r) == 1:
            break
    return seq


def sign_at(poly, x):
    """poly 在有理数 x 处的符号（精确）。"""
    if isinstance(x, str):        # '+inf'
        return (poly[-1] > 0) - (poly[-1] < 0)
    x = Fr(x)
    a, b = x.numerator, x.denominator
    d = len(poly) - 1
    acc = poly[-1]
    bp = 1
    for i in range(d - 1, -1, -1):
        bp *= b
        acc = acc * a + poly[i] * bp
    return (acc > 0) - (acc < 0)


def variations(seq, x):
    sg = [sign_at(p, x) for p in seq]
    sg = [v for v in sg if v != 0]
    return sum(1 for i in range(len(sg) - 1) if sg[i] != sg[i + 1])


def isolate(seq, a, b, out, depth=0):
    """(a,b] 中的不同实根，隔离到每个区间恰一个根。"""
    n = variations(seq, a) - variations(seq, b)
    if n == 0:
        return
    if n == 1:
        out.append((a, b))
        return
    mid = (a + b) / 2
    isolate(seq, a, mid, out, depth + 1)
    isolate(seq, mid, b, out, depth + 1)


def refine(p, a, b, tol=Fr(1, 10 ** 9)):
    sa = sign_at(p, a)
    sb = sign_at(p, b)
    if sb == 0:
        return b, b
    assert sa * sb < 0, (a, b)
    while b - a > tol:
        mid = (a + b) / 2
        sm = sign_at(p, mid)
        if sm == 0:
            return mid, mid
        if sm == sa:
            a = mid
        else:
            b = mid
    return a, b


T0 = time.time()
UR = L.U_rec_table(KR, KR + 1)
D = [L.newton_coeffs(UR[k], k) for k in range(KR + 1)]

all_far = []          # (k, root, dist) for y > s_k + 1/2
rows = []
ok_count, ok_sqfree = True, True
named = {}
for k in range(2, KR + 1):
    sk = L.s_of(k)
    # k!·u_k(-y) = Σ_q d_q (-1)^q (k!/q!) y(y+1)…(y+q-1)
    poly = [0]
    rise = [1]
    for q in range(k + 1):
        w = D[k][q] * (-1) ** q * (factorial(k) // factorial(q))
        term = [w * c for c in rise]
        poly = [(poly[i] if i < len(poly) else 0) + (term[i] if i < len(term) else 0) for i in range(max(len(poly), len(term)))]
        rise = pmul(rise, [q, 1])              # 乘 (y+q)
    poly = trim(poly)
    # 除以 (y-1)…(y-s_k)
    for i in range(1, sk + 1):
        # 综合除法除以 (y - i)
        d = len(poly) - 1
        qd = [0] * d
        acc = 0
        for t in range(d, 0, -1):
            acc = acc * i + poly[t]
            qd[t - 1] = acc
        remv = acc * i + poly[0]
        assert remv == 0, (k, i)
        poly = qd
    v = trim(poly)
    assert len(v) - 1 == k - sk
    seq = sturm_seq(v)
    sqfree = (len(seq[-1]) == 1)
    ok_sqfree &= sqfree
    # 根界（Cauchy）
    B = 1 + max(abs(Fr(c, v[-1])) for c in v[:-1])
    Bp = 1
    while Bp < B:
        Bp *= 2
    half = Fr(2 * sk + 1, 2)
    n_gt_s = variations(seq, Fr(sk) + Fr(1, 10 ** 12)) - variations(seq, Fr(Bp))
    n_far = variations(seq, half) - variations(seq, Fr(Bp))
    n_unit = variations(seq, Fr(sk) + Fr(1, 10 ** 12)) - variations(seq, Fr(sk + 1))
    vs = sign_at(v, Fr(sk))
    ivs = []
    isolate(seq, Fr(sk) + Fr(1, 10 ** 12), Fr(Bp), ivs)
    roots = []
    for (a, b) in ivs:
        lo, hi = refine(v, a, b)
        roots.append((lo + hi) / 2)
    roots.sort()
    assert len(roots) == n_gt_s
    for r in roots:
        if r > half:
            dist = abs(r - round(r))
            all_far.append((k, float(r), float(dist)))
    diff = n_gt_s - k // 3
    extra_ok = (diff == 0) or (diff == 1 and n_unit >= 1)
    ok_count &= diff in (0, 1) and extra_ok
    rows.append((k, sk, len(v) - 1, n_gt_s, k // 3, n_unit, n_far, vs))
    named[k] = roots
    if k in (10, 30, 37, 40):
        print('k=%d s_k=%d：y>s_k 的根 %s' % (k, sk, ['%.4f' % float(r) for r in roots]), flush=True)

n_far = len(all_far)
mean = sum(d for _, _, d in all_far) / n_far
n05 = sum(1 for _, _, d in all_far if d < 0.05)
n01 = sum(1 for _, _, d in all_far if d < 0.01)
closest = sorted(all_far, key=lambda t: t[2])[:8]
report('r-stats', (n_far, n05, n01) == (260, 23, 4) and abs(mean - 0.252) < 0.0005,
       'k<=%d、y>s_k+1/2 的实根共 %d 个（笔记 260），到最近整数的平均距离 %.4f（0.252），<0.05 的 %d 个（23），<0.01 的 %d 个（4）；最近的 8 个 %s'
       % (KR, n_far, mean, n05, n01, ['k=%d:%.5f(%.5f)' % c for c in closest]))
report('r-count', ok_count and ok_sqfree,
       'y>s_k 的根数 - floor(k/3) ∈ {0,1}、多出时 (s_k,s_k+1) 中有根（2<=k<=%d）%s；v_k 无重根 %s；多出 1 个的 k：%s'
       % (KR, ok_count, ok_sqfree, [r[0] for r in rows if r[3] - r[4] == 1]))


def has_root(k, lo, hi):
    return any(lo < r < hi for r in named.get(k, []))


if KR >= 40:
    okn = (has_root(10, 9.02, 9.022) and has_root(30, 60.0003, 60.0004) and has_root(37, 5531.997, 5531.999)
           and has_root(40, 69.004, 69.005) and abs(float(max(named[30])) - 5291.6157) < 1e-3
           and abs(float(max(named[40])) - 10363.9087) < 1e-3)
    report('r-named', okn, '笔记点名的根：k=10 在 (9.020,9.022)、k=30 在 (60.0003,60.0004)、k=37 在 (5531.997,5531.999)、k=40 在 (69.004,69.005)；'
           '最大实根 k=30：%.4f、k=40：%.4f' % (float(max(named[30])), float(max(named[40]))))
extra_res = sorted({r[0] % 3 for r in rows if r[3] - r[4] == 1})
print('多出 1 个根的 k 模 3 的余数：%s；k≡2 (mod 3) 且 k>=5 时都多出：%s'
      % (extra_res, all(r[3] - r[4] == 1 for r in rows if r[0] % 3 == 2 and r[0] >= 5)))
print('表：k s_k deg(v) #根(y>s_k) floor(k/3) #根∈(s_k,s_k+1) #根(y>s_k+1/2) sign v(s_k)')
for r in rows:
    print('  ' + ' '.join(str(x) for x in r))
print('total %.0fs' % (time.time() - T0))
n_pass = sum(RES)
print('SUMMARY s14-b8-r5 pass=%d fail=%d' % (n_pass, len(RES) - n_pass))
sys.exit(0 if n_pass == len(RES) else 1)
