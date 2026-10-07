# -*- coding: utf-8 -*-
"""s9-b7 独立核对 F1-F3：notes/09 §3 的系数 a_k 与 f_k(t) 精确相等（不经过 T3.4(4)）。

不导入项目里的任何模块（core.py、check_b7_borel.py 都不导入），只用标准库 + Fraction。

记号同 notes/09：tau=-t>0，psi_x(s)=(1-x)s+tau(e^s-1)，g_x(z)=1+x^2 z/(1-z)^2，
H(w,x)=g_x(-tau e^{s_x(w)})/psi_x'(s_x(w))，a_k := sum_{3n+j=k} n! [w^n x^j] H。

[w^n] H 用 Lagrange 反演精确计算（不做数值反函数）：因为 H(w,x)dw = g_x(-tau e^s) ds，
  [w^n] H(w,x) = Res_s g_x(-tau e^s) psi_x(s)^{-n-1} = [s^n] g_x(-tau e^s) (s/psi_x(s))^{n+1}，
  s/psi_x(s) = 1/(c + tau*phi(s))，c = 1-x+tau，phi(s) = (e^s-1-s)/s = sum_{i>=1} s^i/(i+1)!，
  g_x(-tau e^s) = 1 - x^2 G(s)，G(s) = tau e^s/(1+tau e^s)^2（与 x 无关）。
于是 [w^n x^j] H = sum_{m<=n} C(-n-1,m) tau^m ( P_{n,m}[x^j]c^{-n-1-m} - Q_{n,m}[x^{j-2}]c^{-n-1-m} )，
  P_{n,m}=[s^n]phi^m，Q_{n,m}=[s^n]phi^m G，c^{-p}=(1+tau)^{-p} sum_i C(p+i-1,i)(x/(1+tau))^i。

f_k(t)：由 (1-t)f_k=f_{k-1}+t f'_{k-3}（notes/07 §1）推出 h_k 的多项式递推
  h_k = h_{k-1} + t(1-t)[(1-t)h'_{k-3} + (k-2)h_{k-3}]，h_0=h_1=1，h_2=1+t，f_k=h_k/(1-t)^{k+1}；
  再用原始定义（长度 k 的允许行（不含连续 001、010）在逐分量序下的多重链个数 = U_k(m)）
  对 k<=9、m<=6 核对 sum_m U_k(m)t^m = h_k/(1-t)^{k+1}。

输出：逐条 PASS/FAIL，最后一行 SUMMARY。
  F1  h_k 递推 vs 原始定义（多重链暴力计数）
  F2  a_k = f_k(t) 精确相等：8 个 t，k<=45；另 2 个 t 到 k<=90
  F3  反向检查：把 g_x 里的 x^2 换成 x^3、或把 c 换成 1+x+tau，恒等式必须失败
"""
import sys
import time
from fractions import Fraction as Fr
from itertools import product
from math import comb, factorial

if not sys.stdout.isatty():
    sys.stdout.reconfigure(encoding='utf-8')

RES = []


def report(cid, ok, desc):
    RES.append(bool(ok))
    print('%s %s %s' % ('PASS' if ok else 'FAIL', cid, desc), flush=True)


# ---------- 截断幂级数（单变量，Fraction 系数） ----------
def smul(a, b, N):
    c = [Fr(0)] * (N + 1)
    for i in range(min(len(a), N + 1)):
        ai = a[i]
        if ai == 0:
            continue
        for j in range(min(len(b), N + 1 - i)):
            bj = b[j]
            if bj:
                c[i + j] += ai * bj
    return c


def sinv(a, N):
    b = [Fr(0)] * (N + 1)
    b[0] = 1 / a[0]
    for n in range(1, N + 1):
        s = Fr(0)
        for i in range(1, min(n, len(a) - 1) + 1):
            s += a[i] * b[n - i]
        b[n] = -s / a[0]
    return b


# ---------- a_k（Lagrange 反演） ----------
def a_coeffs(tau, K, xpow_g=2, c_sign=-1):
    """xpow_g、c_sign 只给反向检查用：正确值是 xpow_g=2（g 里的 x^2）、c_sign=-1（c=1-x+tau）。"""
    N = K // 3
    E = [Fr(1, factorial(i)) for i in range(N + 1)]
    tE = [tau * e for e in E]
    den = [tE[0] + 1] + tE[1:]
    G = smul(tE, sinv(smul(den, den, N), N), N)
    phi = [Fr(0)] + [Fr(1, factorial(i + 1)) for i in range(1, N + 1)]
    pw = [[Fr(1)] + [Fr(0)] * N]
    for m in range(1, N + 1):
        pw.append(smul(pw[-1], phi, N))
    P, Q = {}, {}
    for m in range(N + 1):
        pg = smul(pw[m], G, N)
        for n in range(N + 1):
            P[(n, m)] = pw[m][n]
            Q[(n, m)] = pg[n]
    base = 1 + tau

    def cpc(p, i):
        # [x^i] (base + c_sign*x)^{-p}... 写成 base^{-p}(1 + c_sign x/base)^{-p}
        if i < 0:
            return Fr(0)
        return Fr(comb(p + i - 1, i)) * Fr(-c_sign) ** i / base ** (p + i)

    out = []
    for k in range(K + 1):
        tot = Fr(0)
        for n in range(k // 3 + 1):
            j = k - 3 * n
            Hnj = Fr(0)
            for m in range(n + 1):
                if P[(n, m)] == 0 and Q[(n, m)] == 0:
                    continue
                coef = Fr((-1) ** m * comb(n + m, m)) * tau ** m
                p = n + 1 + m
                Hnj += coef * (P[(n, m)] * cpc(p, j) - Q[(n, m)] * cpc(p, j - xpow_g))
            tot += factorial(n) * Hnj
        out.append(tot)
    return out


# ---------- h_k 与 f_k ----------
def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def h_polys(K):
    h = [[1], [1], [1, 1]]
    for k in range(3, K + 1):
        q = h[k - 3]
        der = [i * q[i] for i in range(1, len(q))] or [0]
        omt_der = padd(der, [0] + [-c for c in der])          # (1-t) h'
        d = padd(omt_der, [(k - 2) * c for c in q])           # (1-t)h' + (k-2)h
        term = padd([0] + d, [0, 0] + [-c for c in d])        # (t - t^2) d
        h.append(padd(h[k - 1], term))
    return h


def f_values(t, hs):
    out = []
    for k, hk in enumerate(hs):
        val = Fr(0)
        for c in reversed(hk):
            val = val * t + c
        out.append(val / (1 - t) ** (k + 1))
    return out


# ---------- 原始定义：允许行的多重链 ----------
def allowed_rows(k):
    rows = []
    for r in product((0, 1), repeat=k):
        ok = True
        for i in range(k - 2):
            tr = r[i:i + 3]
            if tr == (0, 0, 1) or tr == (0, 1, 0):
                ok = False
                break
        if ok:
            rows.append(r)
    return rows


def U_brute(k, M):
    rows = allowed_rows(k)
    R = len(rows)
    geq = [[all(a >= b for a, b in zip(rows[i], rows[j])) for j in range(R)] for i in range(R)]
    U = [1]
    cnt = [1] * R  # 以 rows[i] 结尾、长度 1 的多重链
    U.append(sum(cnt))
    for m in range(2, M + 1):
        new = [0] * R
        for i in range(R):
            if cnt[i]:
                for j in range(R):
                    if geq[i][j]:
                        new[j] += cnt[i]
        cnt = new
        U.append(sum(cnt))
    return U


def main():
    t0 = time.time()
    # F1
    hs = h_polys(12)
    ok = True
    bad = []
    for k in range(0, 10):
        U = U_brute(k, 6)
        for m in range(0, 7):
            pred = sum(hs[k][i] * comb(m - i + k, k) for i in range(len(hs[k])) if i <= m)
            if pred != U[m]:
                ok = False
                bad.append((k, m, pred, U[m]))
    report('F1', ok, 'h_k 递推的 t^m 系数 = 原始定义的多重链计数 U_k(m)（k<=9, m<=6, 70 个值）%s；例 U_9(0..6)=%s'
           % ('' if ok else ' 不符 %s' % bad[:3], U_brute(9, 6)))

    # F2
    hs = h_polys(90)
    taus = [Fr(1, 2), Fr(3), Fr(1, 10), Fr(7, 3), Fr(2), Fr(5), Fr(1, 1000), Fr(100)]
    ok = True
    info = []
    for tau in taus:
        K = 90 if tau in (Fr(1, 2), Fr(3)) else 45
        a = a_coeffs(tau, K)
        f = f_values(-tau, hs[:K + 1])
        mism = [k for k in range(K + 1) if a[k] != f[k]]
        ok = ok and not mism
        info.append('t=%s:k<=%d %s' % (-tau, K, '全等' if not mism else '不等于 k=%s' % mism[:5]))
    # 举一个具体值
    a3 = a_coeffs(Fr(1, 2), 6)
    f3 = f_values(Fr(-1, 2), hs[:7])
    report('F2', ok, '形式系数 a_k=sum n![w^n x^j]H 与 f_k(t) 精确相等：%s；例 t=-1/2：a_6=%s，f_6=%s'
           % ('; '.join(info), a3[6], f3[6]))

    # F3 反向检查
    tau = Fr(1, 2)
    f = f_values(-tau, hs[:13])
    a_bad1 = a_coeffs(tau, 12, xpow_g=3)
    a_bad2 = a_coeffs(tau, 12, c_sign=+1)
    m1 = [k for k in range(13) if a_bad1[k] != f[k]]
    m2 = [k for k in range(13) if a_bad2[k] != f[k]]
    report('F3', bool(m1) and bool(m2), '反向检查：g 用 x^3 时首个不符在 k=%s；c 用 1+x+tau 时首个不符在 k=%s（都应当不符）'
           % (m1[:1], m2[:1]))

    print('time %.1fs' % (time.time() - t0))
    n = sum(RES)
    print('SUMMARY s9b7_formal pass=%d fail=%d' % (n, len(RES) - n))
    return 0 if n == len(RES) else 1


if __name__ == '__main__':
    sys.exit(main())
