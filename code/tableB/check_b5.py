# -*- coding: utf-8 -*-
"""表 B 的 B5（N(k,q) 的单和与短双和）的核对脚本（2026-10-08）。证明见 notes/13-主Agent-表B-B5-N的单和与短双和.md。

逐条打印「PASS <id> ...」或「FAIL <id> ...」，最后一行「SUMMARY b5 pass=<n> fail=<n>」。除 b5-twocert 外只用标准库；
b5-twocert 用 numpy，并导入 check_b2.py 的模 l 运算、筛法与 l 进实现（notes/08；check_b4.py 的 b4-two 用的是同一套）。
真值：U 取自 code/core.py（原始定义的高度 DP）；U^c（不以上升结尾）用 check_b4.py 里按定义写的 DP；
N、N^c 由容斥 N(k,q)=sum_i (-1)^(q-i) C(q,i) U_k(i-1)（T1.4）得到，N^E=N-N^c；另对 k<=8 用 DFS 按定义直接枚举核对。
  b5-def      N、N^c、N^E 的容斥值与按定义直接枚举（值域恰为 {1..q} 的合法词，是否以上升结尾）一致（k<=8）
  b5-double   定理 3：N、N^c、N^E 的双和（原子 w_i、c_i、w_i-c_i）对 1<=k<=40、1<=q<=14 精确成立；
              注 3.1：sum_t C(q,t) y^t/(n-t)! = y^n L_n^(i+1)(-1/y)（n,i<=12，多项式恒等）；注 3.2 的交错式（k<=30，q<=10）
  b5-res      引理 4.1：F_q 在 b_w 处的留数元（由 Num_q=P_{q-1} F_q 截断得到，对照定义）在 Q[x]/(b_w) 中等于
              (-1)^(q-w)/(w^2 w!) W~_w Lambda_{q,w}（q<=10，1<=w<=q-1）；F^c_q、F^E_q 同样；u'(eta)/b_w'(eta) = -1/(w^2 eta^3)
  b5-mod3     引理 4.2：T_n(z) 的系数模 3（n<=300）；T_{q-2}(xi^-3) 模 3Z[xi] 是单位 z^(q-2) 或 z^(q-3) xi^-2，3 不整除其范数（2<=q<=150）
  b5-norm     与定理 4 的论证独立的直接检查：3 N(T_{q-2}(xi^-3)) 不是有理数的立方（2<=q<=60）
  b5-linsys   (2,1) 形状的截断方程组：N_q（q=2..6）无解；N_1、N^c_2、N^E_2 有解（正对照）
  b5-top      定理 5(b)：N 的 Stirling 类比型表示的系数（由 Num_q 的部分分式算出）给出 N(k,q)（1<=k<=40，q<=10），
              最高一项 (q-1)! gamma_r(q,q-1) = A_{q-1}^(r)（2<=q<=10）
  b5-two      注 5.2（每个 i 两个原子）：N(k,3) = 13/2 - c_1(k+8) - 2c_1(k-2) + (5/2)c_2(k+3) + 6c_2(k-2)（1<=k<=40）；
              由 Num_q 的部分分式：q=3 的纤维 1、2 的元素落在 span(x^-8,x^2)、span(x^-3,x^2) 里；q=4 的纤维 3 的元素
              等于 x^-9 W~_3/3!（于是由 notes/12 引理 3.1 无解）；|a|,|a'|<=40 的解对数（q=2..5 各纤维，数据）
  b5-twocert  注 5.2（4<=q<=30，复核者 s12-b4t3 的建议）：纤维 3 的元素 S_q = 3!(q-4)! x^(3(q-1)) E_{q,3}（整系数；q<=10 时与
              Num_q 的部分分式核对）；T=3360 的 7 个证书素数（阶逐次乘方求得）；每个 q 的筛法排除全部 b≢0 (mod 3360) 的类，
              l 进步骤 3360 个 n0 全部有证书
  b5-nc       命题 6(i)：F^c_q 在纤维 q-1 处的留数元正比于 x^(-3q)，在纤维 q-2 处正比于 x^(-3q)(q x^3+1)，而 q x^3+1 不是有理数（3<=q<=40）
  b5-ne       命题 6(iii)：3<=q<=QNE（默认 300）的每个 q 都有证书（纤维 w 与素数 l∤w，使 l 的指数之和不被 3 整除）；列出不用 (2,17) 的 q
  b5-rev      反向检查：定理 3 中 i=1 项的符号改错、或平移多 1 时不成立；引理 4.2 的例外类改成 n≡1 (mod 3) 时不成立
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'code'))
sys.path.insert(0, HERE)
from core import U_fast_table  # noqa: E402
from check_b4 import (Uc_table, red, kmul, knorm, ffall, Wtilde, coords, c_seq, vp, is_prime,  # noqa: E402
                      is_rational_cube, binom, sys_status)

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RESULTS = []
QNE = int(sys.argv[1]) if len(sys.argv) > 1 else 300


def report(cid, ok, desc):
    RESULTS.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


def ie(tab, k, q):
    s = 0
    for i in range(q + 1):
        u = (1 if k == 0 else 0) if i == 0 else tab[k][i - 1]
        s += (-1) ** (q - i) * comb(q, i) * u
    return s


def brute_split(k):
    res = defaultdict(lambda: [0, 0, 0])
    seq = []
    vals = range(1, k + 1)

    def dfs():
        if len(seq) == k:
            s = set(seq)
            q = len(s)
            if s == set(range(1, q + 1)):
                asc = k >= 2 and seq[-2] < seq[-1]
                res[q][0] += 1
                res[q][2 if asc else 1] += 1
            return
        for v in vals:
            if len(seq) >= 2:
                a, b = seq[-2], seq[-1]
                if not (b == v or (a >= b and a >= v)):
                    continue
            seq.append(v)
            dfs()
            seq.pop()
    dfs()
    return res


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def bpoly(v):
    return [1, -1, 0, -v]


def Wpoly(m):
    """W_m = 1 + x^2 sum_{j=1}^m j P_{j-1}（整系数多项式）。"""
    W = [1]
    P = [1]
    for j in range(1, m + 1):
        P = poly_mul(P, bpoly(j - 1))          # P_{j-1}
        term = [0, 0] + [j * c for c in P]
        if len(term) > len(W):
            W += [0] * (len(term) - len(W))
        for t, c in enumerate(term):
            W[t] += c
    return W


def kinv(a, w):
    """K_w 中的逆元（解 3x3 线性方程组）。"""
    cols = [a, kmul(a, [0, 1, 0], w), kmul(a, [0, 0, 1], w)]
    M = [[cols[j][r] for j in range(3)] + [Fr(1 if r == 0 else 0)] for r in range(3)]
    for col in range(3):
        p = next(r for r in range(col, 3) if M[r][col] != 0)
        M[col], M[p] = M[p], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(3):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
    return [M[r][3] for r in range(3)]


def kpow(a, n, w):
    r = [Fr(1), Fr(0), Fr(0)]
    if n < 0:
        a = kinv(a, w)
        n = -n
    for _ in range(n):
        r = kmul(r, a, w)
    return r


def main():
    t0 = time.time()
    K, Q = 40, 14
    TU = U_fast_table(K, Q)
    TUc = Uc_table(K, Q)
    N = [[ie(TU, k, q) for q in range(Q + 1)] for k in range(K + 1)]
    Nc = [[ie(TUc, k, q) for q in range(Q + 1)] for k in range(K + 1)]
    NE = [[N[k][q] - Nc[k][q] for q in range(Q + 1)] for k in range(K + 1)]

    # ---- b5-def
    okd = True
    for k in range(1, 9):
        bs = brute_split(k)
        for q in range(1, k + 1):
            okd &= (tuple(bs[q]) == (N[k][q], Nc[k][q], NE[k][q]))
    report('b5-def', okd, 'N、N^c、N^E 的容斥值与按定义 DFS 枚举一致（1<=k<=8）')

    # ---- b5-double
    CS = {i: c_seq(i, K + 3 * Q + 5) for i in range(1, Q + 1)}

    def cval(i, n):
        if n < 0:
            return 0
        return 1 if i == 0 else CS[i][n]

    def wpart(i, n, which):
        base = cval(i, n)
        ext = sum(j * ffall(i, j) * cval(i, n - 3 * j - 2) for j in range(1, i + 1))
        return {'N': base + ext, 'Nc': base, 'NE': ext}[which]

    def double_sum(k, q, which, sign_flip=False, shift=0):
        tot = Fr(0)
        for i in range(q):
            for t in range(q - i):
                s = (-1) ** (q - 1 - i)
                if sign_flip and i == 1:
                    s = -s
                tot += Fr(s * comb(q, t), factorial(i) * factorial(q - 1 - i - t)) * wpart(i, k + 3 * (q - 1 - t) + shift, which)
        return tot
    okb = True
    for which, tab in (('N', N), ('Nc', Nc), ('NE', NE)):
        for q in range(1, Q + 1):
            for k in range(1, K + 1):
                okb &= (double_sum(k, q, which) == tab[k][q])
    # 注 3.1：Laguerre
    okl = True
    for i in range(0, 13):
        for n in range(0, 13):
            q = n + 1 + i
            # 左：sum_t C(q,t) y^t/(n-t)!   右：y^n L_n^(i+1)(-1/y) = sum_l C(n+i+1, n-l) y^(n-l)/l!
            L = [Fr(0)] * (n + 1)
            R = [Fr(0)] * (n + 1)
            for t in range(n + 1):
                L[t] += Fr(comb(q, t), factorial(n - t))
            for l in range(n + 1):
                R[n - l] += Fr(comb(n + i + 1, n - l), factorial(l))
            okl &= (L == R)
    # 注 3.2 交错式
    from core import stirling2_table
    S = stirling2_table(80)
    oka = True
    for q in range(1, 11):
        for k in range(1, 31):
            tot = 0
            for s in range(0, k // 3 + 1):
                for i in range(1, q + 1):
                    tot += (-1) ** (q - i) * comb(q, i) * S[i - 1 + s][i - 1] * binom(k - 2 * s + i - 1, k - 3 * s)
            oka &= (tot == Nc[k][q])
    report('b5-double', okb and okl and oka,
           '定理 3 的三个双和对 1<=k<=40、1<=q<=14 精确成立；注 3.1 的 Laguerre 恒等式（n,i<=12）；注 3.2 的交错式（k<=30，q<=10）')

    # ---- 由定义得到 Num_q（截断乘积）与 F^c、F^E 的分子
    def Pq(q):
        P = [1]
        for v in range(q):
            P = poly_mul(P, bpoly(v))
        return P

    def numer(tab, q):
        P = Pq(q)                      # P_{q-1}
        F = [tab[k][q] for k in range(K + 1)]
        prod = poly_mul(P, F)[:3 * q - 1]
        return prod                    # 次数 <= 3q-2
    # 检查截断合理：更高次的系数为 0（直到 K）
    okt = all(all(c == 0 for c in poly_mul(Pq(q), [N[k][q] for k in range(K + 1)])[3 * q - 1:K + 1]) for q in range(1, 11))

    # ---- b5-res
    okr = okt
    for q in range(2, 11):
        for w in range(1, q):
            Wt = Wtilde(w)
            x = [Fr(0), Fr(1), Fr(0)]
            xm3 = kpow(x, -3, w)
            Lam = [Fr(0)] * 3
            for M in range(w, q):
                co = Fr(comb(q, M + 1), factorial(M - w))
                Lam = [a + co * b for a, b in zip(Lam, kpow(xm3, M + 1, w))]
            const = Fr((-1) ** (q - w), w * w * factorial(w))
            for which, tab, fac in (('N', N, red(Wt, w)), ('Nc', Nc, [Fr(1), Fr(0), Fr(0)]),
                                    ('NE', NE, red([c if a > 0 else 0 for a, c in enumerate(Wt)], w))):
                num = red(numer(tab, q), w)
                prodo = [Fr(1), Fr(0), Fr(0)]
                for v in range(q):
                    if v != w:
                        prodo = kmul(prodo, red(bpoly(v), w), w)
                Rres = kmul(num, kinv(prodo, w), w)                    # 部分分式分子 R（=Res * b_w'）
                lhs = kmul(Rres, [Fr(-1, w * w) * t for t in kpow(x, -3, w)], w)   # u'Res = R * (-1/(w^2 x^3))
                rhs = [const * t for t in kmul(fac, Lam, w)]
                okr &= (lhs == rhs)
    # u'(eta)/b_w'(eta) = -1/(w^2 eta^3)：等价于 (3-2x)/x = 1 + 3w x^2（在 K_w 中）
    for w in range(1, 12):
        x = [Fr(0), Fr(1), Fr(0)]
        lhs = kmul([Fr(3), Fr(-2), Fr(0)], kinv(x, w), w)
        okr &= (lhs == [Fr(1), Fr(0), Fr(3 * w)])
    report('b5-res', okr, '引理 4.1 在 Q[x]/(b_w) 中精确成立（N、N^c、N^E；2<=q<=10，1<=w<=q-1，含 b_4 可约的情形）；'
                          'u\'/b_w\' = -1/(w^2 x^3)（w<=11）；Num_q 由定义的截断乘积得到（高次系数为 0）')

    # ---- b5-mod3
    def Tpoly(n):
        return [comb(n + 2, l + 2) * (factorial(n) // factorial(l)) for l in range(n + 1)]
    okm = True
    for n in range(0, 301):
        T = Tpoly(n)
        exp = [0] * (n + 1)
        exp[n] = 1
        if n % 3 == 2:
            exp[n - 1] = 2
        okm &= all((T[l] - exp[l]) % 3 == 0 for l in range(n + 1))
    # T_{q-2}(xi^-3) 在 K_1 中；模 3 是单位；3 不整除范数
    z = kpow([Fr(0), Fr(1), Fr(0)], -3, 1)
    zp = [[Fr(1), Fr(0), Fr(0)]]
    for _ in range(200):
        zp.append(kmul(zp[-1], z, 1))
    xim2 = kpow([Fr(0), Fr(1), Fr(0)], -2, 1)
    okn3 = True
    for q in range(2, 151):
        T = Tpoly(q - 2)
        el = [Fr(0)] * 3
        for l, c in enumerate(T):
            if c:
                el = [a + c * b for a, b in zip(el, zp[l])]
        okn3 &= all(t.denominator == 1 for t in el)
        unit = zp[q - 2] if (q - 2) % 3 != 2 else kmul(zp[q - 3], xim2, 1)
        okn3 &= all((int(a) - int(b)) % 3 == 0 for a, b in zip(el, unit))
        nm = knorm(el, 1)
        okn3 &= (nm.denominator == 1 and nm.numerator % 3 != 0)
    report('b5-mod3', okm and okn3,
           '引理 4.2 的系数同余（n<=300）；2<=q<=150：T_{q-2}(xi^-3) 在 Z[xi] 中、模 3 同余于单位 z^(q-2) 或 z^(q-3) xi^-2，且 3 不整除其范数')

    # ---- b5-norm
    okc = True
    for q in range(2, 61):
        T = Tpoly(q - 2)
        el = [Fr(0)] * 3
        for l, c in enumerate(T):
            if c:
                el = [a + c * b for a, b in zip(el, zp[l])]
        okc &= not is_rational_cube(3 * knorm(el, 1))
    report('b5-norm', okc, '直接检查：3 N(T_{q-2}(xi^-3)) 不是有理数的立方（2<=q<=60）')

    # ---- b5-linsys
    found, nsys = [], 0
    for q in range(2, 7):
        seq = [N[k][q] for k in range(K + 1)]
        for k0 in (1, 6):
            for c in range(-3, 4):
                for d in range(-3, 4):
                    nsys += 1
                    if sys_status(seq, 2, 1, c, d, k0, K) == 'solvable':
                        found.append((q, k0, c, d))
    def any_solv(seq):
        return any(sys_status(seq, 2, 1, c, d, 1, K) == 'solvable' for c in range(-6, 4) for d in range(-4, 4))
    pos = any_solv([N[k][1] for k in range(K + 1)]) and any_solv([Nc[k][2] for k in range(K + 1)]) \
        and any_solv([NE[k][2] for k in range(K + 1)])
    report('b5-linsys', not found and pos,
           '(2,1) 形状：N_q（q=2..6）的 %d 个截断方程组（k0 in {1,6}，c,d in [-3,3]，k<=40）全部无解；N_1、N^c_2、N^E_2 有解%s'
           % (nsys, '' if not found else '；有解：%s' % found[:3]))

    # ---- b5-top
    okto = True
    for q in range(2, 11):
        num = numer(N, q)
        # 部分分式：F_q = const + sum_i R_i/b_i；对 i>=1 求 R_i（K_i 中），化到基 c_i(k+3(q-1)-r)：乘以 x^{3(q-1)}
        gam = {}
        for i in range(1, q):
            prodo = [Fr(1), Fr(0), Fr(0)]
            for v in range(q):
                if v != i:
                    prodo = kmul(prodo, red(bpoly(v), i), i)
            Ri = kmul(red(num, i), kinv(prodo, i), i)
            gam[i] = kmul(Ri, kpow([Fr(0), Fr(1), Fr(0)], 3 * (q - 1), i), i)
        # i=0：b_0=1-x，R_0 = Num_q(1)/prod_{v>=1} b_v(1)
        num1 = sum(num)
        p1 = 1
        for v in range(1, q):
            p1 *= -v
        g0 = Fr(num1, p1)
        for k in range(1, K + 1):
            val = g0 + sum(sum(gam[i][r] * cval(i, k + 3 * (q - 1) - r) for r in range(3)) for i in range(1, q))
            okto &= (val == N[k][q])
    for q in range(2, 13):
        num = numer(N, q) if q <= 10 else None
        if num is None:
            # q=11,12：直接用 T4.3(2) 的容斥闭式会更快，这里用 N 的更长截断
            break
        i = q - 1
        prodo = [Fr(1), Fr(0), Fr(0)]
        for v in range(q):
            if v != i:
                prodo = kmul(prodo, red(bpoly(v), i), i)
        Ri = kmul(red(num, i), kinv(prodo, i), i)
        g = kmul(Ri, kpow([Fr(0), Fr(1), Fr(0)], 3 * (q - 1), i), i)
        okto &= ([factorial(q - 1) * t for t in g] == coords(i))
    report('b5-top', okto, '定理 5(b)：由 Num_q 的部分分式得到的 Stirling 类比型表示给出 N(k,q)（1<=k<=40，2<=q<=10）；'
                           '最高一项 (q-1)! gamma_r(q,q-1) = A_{q-1}^(r)（2<=q<=10）')

    # ---- b5-two（注 5.2：每个 i 两个原子）
    def cz(cs, n):
        return cs[n] if n >= 0 else 0
    ok3 = all(Fr(13, 2) - cz(CS[1], k + 8) - 2 * cz(CS[1], k - 2) + Fr(5, 2) * cz(CS[2], k + 3) + 6 * cz(CS[2], k - 2)
              == N[k][3] for k in range(1, K + 1))
    def Rpart(q, i):
        num = numer(N, q)
        prodo = [Fr(1), Fr(0), Fr(0)]
        for v in range(q):
            if v != i:
                prodo = kmul(prodo, red(bpoly(v), i), i)
        return kmul(red(num, i), kinv(prodo, i), i)
    def det3(u, v, w):
        return (u[0] * (v[1] * w[2] - v[2] * w[1]) - u[1] * (v[0] * w[2] - v[2] * w[0]) + u[2] * (v[0] * w[1] - v[1] * w[0]))
    xx = [Fr(0), Fr(1), Fr(0)]
    ok4 = Rpart(4, 3) == [t / 6 for t in kmul(coords(3), kpow(xx, -9, 3), 3)]
    okspan = (det3(Rpart(3, 1), kpow(xx, -8, 1), kpow(xx, 2, 1)) == 0
              and det3(Rpart(3, 2), kpow(xx, -3, 2), kpow(xx, 2, 2)) == 0)
    cnts = {}
    for q in range(2, 6):
        for i in range(1, q):
            E = Rpart(q, i)
            X = {a: kpow(xx, a, i) for a in range(-40, 41)}
            cnts[(q, i)] = sum(1 for a in range(-40, 41) for b in range(a + 1, 41) if det3(E, X[a], X[b]) == 0)
    okw = cnts[(4, 3)] == 0 and all(cnts[(q, i)] > 0 for q in (2, 3) for i in range(1, q))
    report('b5-two', ok3 and ok4 and okspan and okw,
           '注 5.2：N(k,3) 的两原子式对 1<=k<=40 成立：%s；q=3 两条纤维的元素在 span(x^-8,x^2)、span(x^-3,x^2) 里：%s；'
           'q=4 纤维 3 的元素 = x^-9 W~_3/3!：%s；|a|,|a\'|<=40 的解对数（(q,纤维)：个数）%s'
           % (ok3, okspan, ok4, ', '.join('(%d,%d):%d' % (q, i, c) for (q, i), c in sorted(cnts.items()))))

    # ---- b5-twocert（注 5.2：4<=q<=30 时纤维 3 无两原子解）
    import check_b2 as B2
    T3 = 3360
    CERT3 = [(5, 20), (13, 84), (31, 480), (71, 70), (97, 96), (193, 96), (673, 672)]
    okord = True
    for (l, P) in CERT3:
        cur, order = [1, 0, 0], None
        for e in range(1, T3 + 1):
            cur = B2.mulm(cur, [0, 1, 0], 3, l)
            if cur == [1, 0, 0]:
                order = e
                break
        okord &= is_prime(l) and l % 2 == 1 and l != 3 and order == P and T3 % P == 0
    def S_coeffs(q):
        W = Wtilde(3)
        L = [0] * (3 * (q - 4) + 1)
        for M in range(3, q):
            L[3 * (q - 1 - M)] += (-1) ** (q - 4) * comb(q, M + 1) * (factorial(q - 4) // factorial(M - 3))
        out = [0] * (len(W) + len(L) - 1)
        for a, x1 in enumerate(W):
            if x1:
                for b, y1 in enumerate(L):
                    out[a + b] += x1 * y1
        return out
    okS = all(red(S_coeffs(q), 3) == [6 * factorial(q - 4) * t for t in kmul(Rpart(q, 3), kpow(xx, 3 * (q - 1), 3), 3)]
              for q in range(4, 11))
    def elem_mod(co):
        def f(l):
            acc = [0, 0, 0]
            for d, c in enumerate(co):
                if c % l:
                    v = B2.powm(d, 3, l)
                    acc = [(acc[t] + c * v[t]) % l for t in range(3)]
            return acc
        return f
    saved = (B2.T, B2.CERT.get(3))
    B2.T = T3
    B2.CERT[3] = CERT3
    failq = []
    try:
        for q in range(4, 31):
            surv, tabs = B2.sieve('U', (3,), elems={3: elem_mod(S_coeffs(q))})
            unr, _ = B2.padic('U', (3,), tabs)
            if surv or unr:
                failq.append((q, len(surv), len(unr)))
    finally:
        B2.T, B2.CERT[3] = saved
    report('b5-twocert', okord and okS and not failq,
           '注 5.2：4<=q<=30 时 N(.,q) 没有每个 i 两个原子的表示（纤维 3，T=3360、7 个证书素数，阶核对：%s；S_q 与部分分式一致（q<=10）：%s；'
           '筛法与 l 进未排除的 q：%s）' % (okord, okS, failq or '无'))

    # ---- b5-nc
    oknc = True
    for q in range(3, 41):
        for w, expect in ((q - 1, 'mono'), (q - 2, 'lin')):
            x = [Fr(0), Fr(1), Fr(0)]
            xm3 = kpow(x, -3, w)
            Lam = [Fr(0)] * 3
            for M in range(w, q):
                co = Fr(comb(q, M + 1), factorial(M - w))
                Lam = [a + co * b for a, b in zip(Lam, kpow(xm3, M + 1, w))]
            ratio = kmul(Lam, kpow(x, 3 * q, w), w)       # Lambda * x^{3q}
            if expect == 'mono':
                oknc &= (ratio == [Fr(1), Fr(0), Fr(0)])
            else:
                target = [Fr(0)] * 3
                qx3 = [Fr(q) * t for t in kpow(x, 3, w)]
                target = [qx3[0] + 1, qx3[1], qx3[2]]
                oknc &= (ratio == target) and target[1] != 0
    report('b5-nc', oknc, '命题 6(i)：3<=q<=40 时 Lambda_{q,q-1} x^{3q} = 1，Lambda_{q,q-2} x^{3q} = q x^3+1，且 q x^3+1 的 x 系数非零（不是有理数）')

    # ---- b5-ne
    FIB = [2, 3, 5, 6, 7]
    pre = {}
    for w in FIB:
        Wm1 = red([c if a > 0 else 0 for a, c in enumerate(Wtilde(w))], w)
        NW = knorm(Wm1, w)
        xm3 = kpow([Fr(0), Fr(1), Fr(0)], -3, w)
        zps = [[Fr(1), Fr(0), Fr(0)]]
        for _ in range(QNE + 2):
            zps.append(kmul(zps[-1], xm3, w))
        pre[w] = (NW, zps)
    uncovered, others = [], []
    PRIMES = (17, 2, 3, 5, 7, 11, 13, 19, 23, 29, 31, 37, 41, 43, 47)
    for q in range(3, QNE + 1):
        cert = None
        for w in FIB:
            if w > q - 1:
                continue
            NW, zps = pre[w]
            L = [Fr(0)] * 3
            for M in range(w, q):
                co = Fr(comb(q, M + 1) * factorial(q - 1 - w), factorial(M - w))
                L = [a + co * b for a, b in zip(L, zps[M + 1])]
            tot = NW * knorm(L, w)
            for l in PRIMES:
                if w % l == 0:
                    continue
                if vp(tot, l) % 3:
                    cert = (w, l)
                    break
            if cert:
                break
        if cert is None:
            uncovered.append(q)
        elif cert != (2, 17):
            others.append((q, cert))
    report('b5-ne', not uncovered, '命题 6(iii)：3<=q<=%d 的每个 q 都有证书（纤维 w in {2,3,5,6,7}，素数 l∤w）；不用 (2,17) 的：%s%s'
           % (QNE, ', '.join('q=%d:(%d,%d)' % (qq, w, l) for qq, (w, l) in others) or '无',
              '' if not uncovered else '；无证书：%s' % uncovered[:10]))

    # ---- b5-rev
    r1 = any(double_sum(k, q, 'N', sign_flip=True) != N[k][q] for q in range(3, 8) for k in range(1, 20))
    r2 = any(double_sum(k, q, 'N', shift=1) != N[k][q] for q in range(2, 8) for k in range(1, 20))
    r3 = False
    for n in range(0, 60):
        T = Tpoly(n)
        exp = [0] * (n + 1)
        exp[n] = 1
        if n % 3 == 1:
            exp[n - 1] = 2
        if not all((T[l] - exp[l]) % 3 == 0 for l in range(n + 1)):
            r3 = True
            break
    report('b5-rev', r1 and r2 and r3,
           '反向检查：定理 3 中 i=1 项的符号改错、或平移多 1 时不成立；引理 4.2 的例外类改成 n≡1 (mod 3) 时不成立')
    print('time %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
    n_pass = sum(RESULTS)
    n_fail = len(RESULTS) - n_pass
    print('SUMMARY b5 pass=%d fail=%d' % (n_pass, n_fail))
    sys.exit(0 if n_fail == 0 else 1)
