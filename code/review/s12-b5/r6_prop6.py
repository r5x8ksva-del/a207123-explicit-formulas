# -*- coding: utf-8 -*-
"""s12-b5 复核 r6：命题 6（N^c、N^E 的单族表示）。

  r6-const    1/(1-x) = x^{-6}u - (x^{-3}+x^{-2}+x^{-1})（作为级数逐项，到 x^60）
  r6-nc2      N^c(k,2) = sum_{s>=2} C(k+5-2s,s-1) - 2（即 F^c_2 = x^{-6}(u^2/(1-u)-2u)+Laurent 多项式），1<=k<=60
  r6-ne2      N^E(k,2) = c_1(k-2) = sum_s C(k-2-2s,s)（1<=k<=60）
  r6-fib      命题 6(i) 的两条纤维（3<=q<=40）：Λ_{q,q-1}x^{3q}=1、Λ_{q,q-2}x^{3q}=qx^3+1（Laurent 多项式恒等）；
              Q[x]/(b_{q-2}) 中 qx^3+1 = 1+q(1-x)/(q-2)；数值上 qη^3+1 在 b_{q-2} 三根处两两不同；b_{q-1} 的 |η_c|≠η_r
  r6-irr      b_w（w=2,3,5,6,7）没有有理根（有理根定理的候选 ±1/d，d|w）
  r6-normW    N(W~_w - 1)（w=2,3,5,6,7）——自写 Q[x]/(b_w) 范数，打印数值
  r6-ne-cert  命题 6(iii)：3<=q<=100，每个 q 都有 (w,ℓ)，ℓ 素数、ℓ∤w，v_ℓ(N(W~_w-1)) + v_ℓ(N((q-1-w)!Λ_{q,w})) ≢ 0 (mod 3)；
              (q-1-w)!Λ_{q,w} 在 Z[y]/(y^3-y^2-w)（y=η^{-1}）中整数计算
  r6-q65      v_17(N(63!·Λ_{65,2}))=2，即 (w,ℓ)=(2,17) 在 q=65 失效（笔记 §4 末的说法）
  r6-rev      反向：把纤维元换成单项式 η^{-3q}（有 (2,1) 表示时的形状）后找不到证书；换成 (W~_2-1)η^{-3q} 时能找到
"""
import os
import sys
import time
import cmath
from fractions import Fraction as Fr
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s12b5_common import (report, summary, C, ie_tables, CI, Cubic, Wtil_poly, vp_int, vp_frac, primes_upto,  # noqa: E402
                          roots_cubic_b)

t0 = time.time()
KI = 60
IN, INc, INE = ie_tables(KI, 3)
ci = CI(200)

# ---------------------------------------------------------------- r6-const
# x^{-6}u = x^{-3}/(1-x)：x^n 的系数，n>=-3 时为 1
ok = True
for n in range(-6, KI + 1):
    lhs = 1 if n >= 0 else 0
    rhs = (1 if n >= -3 else 0) - (1 if n in (-3, -2, -1) else 0)
    if lhs != rhs:
        ok = False
report(ok, 'r6-const', '1/(1-x) = x^{-6}u - (x^{-3}+x^{-2}+x^{-1})（逐项到 x^60）')

ok = all(INc[k][2] == sum(C(k + 5 - 2 * s, s - 1) for s in range(2, k + 6)) - 2 for k in range(1, KI + 1))
report(ok, 'r6-nc2', 'N^c(k,2) = sum_{s>=2} C(k+5-2s,s-1) - 2（1<=k<=60）：命题 6(i) 的 q=2 式')
ok = all(INE[k][2] == ci(1, k - 2) == sum(C(k - 2 - 2 * s, s) for s in range(0, k + 1)) for k in range(1, KI + 1))
report(ok, 'r6-ne2', 'N^E(k,2) = c_1(k-2) = sum_s C(k-2-2s,s)（1<=k<=60）：命题 6(ii)')


# ---------------------------------------------------------------- r6-fib
def lam_laurent(q, w):
    """Λ_{q,w} 作为 x 的 Laurent 多项式：{指数: 系数}。"""
    d = {}
    for M in range(w, q):
        e = -3 * (M + 1)
        d[e] = d.get(e, Fr(0)) + Fr(comb(q, M + 1), factorial(M - w))
    return d


ok1 = ok2 = ok3 = ok4 = True
mingap = 1e9
for q in range(3, 41):
    L1 = lam_laurent(q, q - 1)
    if {e + 3 * q: v for e, v in L1.items() if v} != {0: 1}:
        ok1 = False
    L2 = lam_laurent(q, q - 2)
    if {e + 3 * q: v for e, v in L2.items() if v} != {0: 1, 3: q}:
        ok1 = False
    K = Cubic([1, -1, 0, -(q - 2)])
    lhs = K.red([1, 0, 0, q])
    rhs = [1 + Fr(q, q - 2), Fr(-q, q - 2), Fr(0)]
    if lhs != rhs or rhs[1] == 0:
        ok2 = False
    rts = roots_cubic_b(q - 2)
    vals = [q * r ** 3 + 1 for r in rts]
    gap = min(abs(vals[a] - vals[b]) for a in range(3) for b in range(a + 1, 3))
    mingap = min(mingap, gap)
    if gap < 1e-6:
        ok3 = False
    rts1 = roots_cubic_b(q - 1)
    real = [r for r in rts1 if abs(r.imag) < 1e-12]
    cplx = [r for r in rts1 if abs(r.imag) >= 1e-12]
    if len(real) != 1 or len(cplx) != 2 or abs(abs(cplx[0]) - real[0].real) < 1e-6:
        ok4 = False
report(ok1 and ok2 and ok3 and ok4, 'r6-fib',
       '命题 6(i) 两条纤维（3<=q<=40）：Λ 恒等式、qx^3+1=1+q(1-x)/(q-2)（x 系数非零）、三根处取值两两不同（最小间距 %.3g）、|η_c|≠η_r' % mingap)


# ---------------------------------------------------------------- r6-irr、r6-normW
def has_rational_root(w):
    for dd in range(1, w + 1):
        if w % dd == 0:
            for sgn in (1, -1):
                x = Fr(sgn, dd)
                if 1 - x - w * x ** 3 == 0:
                    return True
    return False


WS = (2, 3, 5, 6, 7)
ok = all(not has_rational_root(w) for w in WS) and has_rational_root(4)
report(ok, 'r6-irr', 'b_2,b_3,b_5,b_6,b_7 没有有理根（在 Q 上不可约），b_4 有有理根 1/2（对照）')

NW = {}
for w in WS:
    K = Cubic([1, -1, 0, -w])
    Wt = K.red([Fr(c) for c in Wtil_poly(w)])
    NW[w] = K.norm([Wt[0] - 1, Wt[1], Wt[2]])
report(NW[2] == Fr(17, 8), 'r6-normW', 'N(W~_w-1)：%s' % {w: str(v) for w, v in NW.items()})


# ---------------------------------------------------------------- Z[y]/(y^3-y^2-w)
def ymul(a, b, w):
    r = [0] * 5
    for i in range(3):
        if a[i]:
            for j in range(3):
                if b[j]:
                    r[i + j] += a[i] * b[j]
    # y^3 = y^2 + w ; y^4 = y^3 + w y = y^2 + w + w y
    c3, c4 = r[3], r[4]
    return [r[0] + w * c3 + w * c4, r[1] + w * c4, r[2] + c3 + c4]


def ynorm(a, w):
    cols = [ymul(a, [1, 0, 0], w), ymul(a, [0, 1, 0], w), ymul(a, [0, 0, 1], w)]
    M = [[cols[j][i] for j in range(3)] for i in range(3)]
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def ypow_table(w, nmax):
    tab = [[1, 0, 0]]
    for _ in range(nmax):
        tab.append(ymul(tab[-1], [0, 1, 0], w))
    return tab


YP = {w: ypow_table(w, 3 * 301) for w in WS}


def lam_int(q, w):
    s = [0, 0, 0]
    F = factorial(q - 1 - w)
    for M in range(w, q):
        co = comb(q, M + 1) * (F // factorial(M - w))
        t = YP[w][3 * (M + 1)]
        s = [s[i] + co * t[i] for i in range(3)]
    return s


# 与 Q[x]/(b_w) 中的计算对照（小 q）：两种基下的范数应相同
ok_alt = True
for w in (2, 3):
    K = Cubic([1, -1, 0, -w])
    for q in range(w + 1, w + 6):
        el = [Fr(0)] * 3
        for M in range(w, q):
            t = K.xpow(-3 * (M + 1))
            el = [a + Fr(comb(q, M + 1) * factorial(q - 1 - w), factorial(M - w)) * b for a, b in zip(el, t)]
        if K.norm(el) != ynorm(lam_int(q, w), w):
            ok_alt = False

PR = primes_upto(3000)


def cert(q, extra_elem=None):
    """返回第一个证书 (w, ℓ, 指数和) 或 None。extra_elem(q,w) 给出替代的「纤维元」两个范数 (N1 有理, N2 整数)。"""
    for w in WS:
        if w > q - 1:
            continue
        if extra_elem is None:
            n1, n2 = NW[w], ynorm(lam_int(q, w), w)
        else:
            n1, n2 = extra_elem(q, w)
        if n2 == 0:
            continue
        cand = [l for l in PR if w % l != 0]
        for l in cand:
            v1 = vp_frac(n1, l)
            v2 = vp_int(n2, l)
            if (v1 + v2) % 3 != 0:
                return (w, l, v1 + v2)
    return None


certs = {}
for q in range(3, 101):
    certs[q] = cert(q)
missing = [q for q, c in certs.items() if c is None]
from collections import Counter  # noqa: E402
cnt = Counter((c[0], c[1]) for c in certs.values() if c)
report(not missing and ok_alt, 'r6-ne-cert', '3<=q<=100 全部有证书（缺 %s）；按 (w,ℓ) 计数 %s；Z[y] 与 Q[x]/(b_w) 两种范数一致=%s'
       % (missing, dict(cnt.most_common(8)), ok_alt))
odd = {q: c for q, c in certs.items() if c and (c[0], c[1]) != (2, 17)}
print('  不是 (2,17) 的 q：%s' % odd)

v17 = vp_int(ynorm(lam_int(65, 2), 2), 17)
report(v17 == 2, 'r6-q65', 'v_17(N(63!·Λ_{65,2})) = %d（笔记：2）；q=65 的证书 %s' % (v17, certs[65]))


# ---------------------------------------------------------------- 反向
def mono(q, w):
    # 元素 η^{-3q} = y^{3q}：N = w^{3q}；W 部分换成 1
    return Fr(1), ynorm(YP[w][3 * q], w)


def mono_W(q, w):
    return NW[w], ynorm(YP[w][3 * q], w)


none_found = all(cert(q, mono) is None for q in range(3, 41))
all_found = all(cert(q, mono_W) is not None for q in range(3, 41))
report(none_found and all_found, 'r6-rev', '反向：纤维元换成 η^{-3q} 时 3<=q<=40 都找不到证书=%s；换成 (W~-1)η^{-3q} 时都能找到=%s'
       % (none_found, all_found))

print('time %.1fs' % (time.time() - t0))
sys.exit(1 if summary('r6') else 0)
